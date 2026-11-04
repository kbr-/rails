/-!
The decision model's trace: what an agent's session records, one step per event, in the forms the
refusal dataset's `turn_record`s carry (a user's text; the agent's reply, thinking and tool calls; a
tool's result; a hook's refusal).
-/

namespace Rails

inductive Event where
  | user (text : String)
  | reply (text : String)
  | thinking (text : String)
  /-- A tool call: its id, the tool, and its input's string fields. -/
  | call (id : String) (tool : String) (input : List (String × String))
  /-- A tool's result: the call it answers, its output, and whether the harness marked it failed. -/
  | result (id : String) (output : String) (failed : Bool := false)
  | refusal (hook : String) (text : String)
  deriving Repr, DecidableEq, Inhabited

/-- One event with the agent message it belongs to (calls sent together share it) and its time in
milliseconds. -/
structure Step where
  event : Event
  message : Nat
  time : Nat
  deriving Repr, DecidableEq, Inhabited

/-- A call's input field. -/
def Event.field (e : Event) (key : String) : Option String :=
  match e with
  | .call _ _ input => input.lookup key
  | _ => none

def isUser : Event → Bool
  | .user _ => true
  | _ => false

def isReply : Event → Bool
  | .reply _ => true
  | _ => false

def isTool (name : String) : Event → Bool
  | .call _ tool _ => tool == name
  | _ => false

/-- A shell call's command: Claude Code's `Bash` `command`, or Codex's `exec` input. -/
def command (e : Event) : Option String :=
  if isTool "Bash" e then e.field "command"
  else if isTool "exec" e then e.field "input"
  else none

/-- The first list is a prefix of the second; structural, so the kernel evaluates it and verdicts
on sample traces are proved by `decide`. -/
def hasPrefix : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a == b && hasPrefix as bs

/-- The first list occurs as a contiguous part of the second. -/
def occursIn (n : List Char) : List Char → Bool
  | [] => n.isEmpty
  | h :: t => hasPrefix n (h :: t) || occursIn n t

private def commandHas (needle : String) (e : Event) : Bool :=
  match command e with
  | some c => occursIn needle.toList c.toList
  | none => false

/-- A character ending a shell command: `;`, `&`, `|`, a newline or `(`. -/
def isSep (c : Char) : Bool := c == ';' || c == '&' || c == '|' || c == '\n' || c == '('

/-- A shell text's commands, each its words in order: separators outside quotes end a command,
blanks outside quotes end a word, and a quoted string's characters stay in their word. Structural,
so the kernel evaluates it. -/
def shellCommands (cs : List Char) : List (List (List Char)) :=
  go cs none [] [] []
where
  /-- The word built so far, kept reversed so each character is one cons. -/
  word (w : List Char) : List (List Char) := if w.isEmpty then [] else [w.reverse]
  /-- `w`, `cmd` and `acc` are kept reversed, each step a cons, and turned round at the end. -/
  go : List Char → Option Char → List Char → List (List Char) → List (List (List Char)) →
      List (List (List Char))
    | [], _, w, cmd, acc => (((word w).reverse ++ cmd).reverse :: acc).reverse.filter (!·.isEmpty)
    | c :: cs, some q, w, cmd, acc =>
      if c == q then go cs none w cmd acc else go cs (some q) (c :: w) cmd acc
    | c :: cs, none, w, cmd, acc =>
      if c == '\'' || c == '"' then go cs (some c) w cmd acc
      else if isSep c then go cs none [] [] (((word w).reverse ++ cmd).reverse :: acc)
      else if c == ' ' || c == '\t' then go cs none [] ((word w).reverse ++ cmd) acc
      else go cs none (c :: w) cmd acc

/-- The first list ends the second. -/
def endsWith (suffix s : List Char) : Bool := hasPrefix suffix.reverse s.reverse

/-- A word before a command's program: a variable assignment, `env`, or an interpreter running the
program as its script. -/
def isLauncher (w : List Char) : Bool :=
  w.contains '=' || w == "env".toList || w == "python3".toList || w == "python".toList ||
    w == "sh".toList || w == "bash".toList

/-- Some command of the call runs a program whose name ends `prog`, its launcher words skipped,
with `p` holding of its words. -/
def runs (prog : String) (p : List (List Char) → Bool) (e : Event) : Bool :=
  match command e with
  | some c => (shellCommands c.toList).any fun ws => match ws.dropWhile isLauncher with
    | w :: _ => endsWith prog.toList w && p ws
    | [] => false
  | none => false

/-- Each command of the call as its program word (launcher words skipped) and its words, the
command text tokenized once: a predicate testing many programs reads this. -/
def programs (e : Event) : List (List Char × List (List Char)) :=
  match command e with
  | some c => (shellCommands c.toList).filterMap fun ws => match ws.dropWhile isLauncher with
    | w :: _ => some (w, ws)
    | [] => none
  | none => []

private def hasWord (s : String) (ws : List (List Char)) : Bool := ws.contains s.toList

/-- A push: `git ... push` (with options such as `-C PATH` between) or the checked-push script. -/
def isPush (e : Event) : Bool := runs "git" (hasWord "push") e || runs "checked-push.sh" (fun _ => true) e

private def hasAny (ss : List String) (ws : List (List Char)) : Bool := ss.any (hasWord · ws)

/-- An API call writing: `-X` or `--method` with a writing method, or `-XPOST` and the like. -/
private def writes (ws : List (List Char)) : Bool :=
  let methods := ["POST", "PUT", "PATCH", "DELETE"]
  (hasAny ["-X", "--method"] ws && hasAny methods ws) ||
    hasAny (methods.map ("-X" ++ ·)) ws || hasAny (methods.map ("--method=" ++ ·)) ws

/-- A push, publish or deploy (rule 1): a git push; a container or package push (`docker`,
`podman` or `buildah push`, `skopeo copy`, `npm publish`, `twine upload`); a hosted-service write
(`gh` or `glab` creating or changing a release, a repository, a pull or merge request, or calling
their API with a writing method; `confluence_page.py`); a cluster deploy (`helm upgrade` or
`install`, `kubectl apply`). A write through another client stays unseen. -/
def isPublish (e : Event) : Bool :=
  (programs e).any fun (w, ws) =>
    let is (p : String) := endsWith p.toList w
    (is "git" && hasWord "push" ws) || is "checked-push.sh" ||
    ((is "docker" || is "podman" || is "buildah") && hasWord "push" ws) ||
    (is "skopeo" && hasWord "copy" ws) || (is "npm" && hasWord "publish" ws) ||
    (is "twine" && hasWord "upload" ws) ||
    (is "gh" && ((hasWord "release" ws && hasAny ["create", "upload", "edit"] ws) ||
      (hasWord "repo" ws && hasWord "create" ws) ||
      (hasWord "pr" ws && hasAny ["create", "edit", "comment"] ws) ||
      (hasWord "api" ws && writes ws))) ||
    (is "glab" && ((hasWord "mr" ws && hasAny ["create", "update", "note"] ws) ||
      (hasWord "release" ws && hasWord "create" ws) || (hasWord "api" ws && writes ws))) ||
    is "confluence_page.py" || (is "helm" && hasAny ["upgrade", "install"] ws) ||
    (is "kubectl" && hasWord "apply" ws)

/-- `isPublish` holds of every push. -/
theorem isPush_isPublish (e : Event) (h : isPush e = true) : isPublish e = true := by
  simp only [isPush, runs, Bool.or_eq_true] at h
  simp only [isPublish, programs, List.any_eq_true]
  cases hc : command e with
  | none => simp [hc] at h
  | some c =>
    simp only [hc] at h
    rcases h with h | h <;> obtain ⟨ws, hws, hp⟩ := List.any_eq_true.mp h <;>
      (split at hp
       · rename_i w rest hd
         refine ⟨(w, ws), List.mem_filterMap.mpr ⟨ws, hws, by simp [hd]⟩, ?_⟩
         simp at hp
         simp [hp]
       · simp at hp)

/-- A line of `cs` says Claude attribution, read in lower case as the commit-msg hook
(`tools/git-hooks/commit-msg`) reads it: a `co-authored-by:` naming Claude or Anthropic,
Anthropic's no-reply address, the "generated with Claude Code" footer, or a `claude-session:`
link, which the hook leaves to the rule. -/
def saysAttribution (cs : List Char) : Bool :=
  let lower := cs.map Char.toLower
  let has (s : String) (l : List Char) := occursIn s.toList l
  (lower.splitOn '\n').any (fun l => has "co-authored-by:" l && (has "claude" l || has "anthropic" l)) ||
    has "noreply@anthropic.com" lower || has "generated with claude code" lower ||
    has "generated with [claude code" lower || has "claude-session:" lower

/-- A commit whose command carries Claude attribution in its text; a message from a file, an
editor or an amended commit is outside the trace. -/
def isAttributedCommit (e : Event) : Bool :=
  runs "git" (hasWord "commit") e &&
    match command e with
    | some c => saysAttribution c.toList
    | none => false

/-- A file edit: Claude Code's Edit or Write, or a Codex command running `apply_patch`. -/
def isEdit (e : Event) : Bool := isTool "Edit" e || isTool "Write" e || runs "apply_patch" (fun _ => true) e

def isRead (e : Event) : Bool := isTool "Read" e

def isRequestAdd (e : Event) : Bool :=
  runs "task_index.py" (fun ws => hasWord "request" ws && hasWord "add" ws) e

def isReviewerRun (e : Event) : Bool :=
  isTool "Agent" e && e.field "subagent_type" == some "medium-reviewer"

/-- A tool result the harness didn't mark failed. In the refusal dataset every result whose output
starts with a non-zero `Exit code` is marked failed, so its text needn't be read. -/
def isPassingResult : Event → Bool
  | .result _ _ failed => !failed
  | _ => false

/-- A file a call reads or writes. -/
def readPath (e : Event) : Option String := if isRead e then e.field "file_path" else none
def writePath (e : Event) : Option String := if isEdit e then e.field "file_path" else none

/-- The first call reads a path the second writes. -/
def readsWhatOtherWrites (reader writer : Step) : Bool :=
  match readPath reader.event, writePath writer.event with
  | some r, some w => r == w
  | _, _ => false

end Rails
