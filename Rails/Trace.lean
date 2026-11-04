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

def isPush (e : Event) : Bool := commandHas "git push" e || commandHas "checked-push.sh" e

/-- A commit whose message carries Claude attribution. -/
def isAttributedCommit (e : Event) : Bool :=
  commandHas "git commit" e && (commandHas "Co-Authored-By: Claude" e || commandHas "Claude-Session:" e)

/-- A file edit: Claude Code's Edit or Write, or a Codex command calling `apply_patch`. -/
def isEdit (e : Event) : Bool := isTool "Edit" e || isTool "Write" e || commandHas "apply_patch" e

def isRead (e : Event) : Bool := isTool "Read" e

def isRequestAdd (e : Event) : Bool := commandHas "task_index.py request add" e

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
