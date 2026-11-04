import Rails.Rules
import Rails.Examples
import Rails.Witness

/-!
Rules 841 to 980 of `tasks/agents-on-rails/RULES.md`, the sample's 844 and 926 left out: the
computation policy (running, sizing, observing and storing computations, timing), the rented
machine, the personal addendum's research and tool rules, and the engineering discipline's
verification, design, documentation and history rules. The range holds no MAY rule.
-/

namespace Rails.Ruleset.Range7
open Rails Formula Ruleset Rules

/-! Helpers over a command's words, for the predicates below. -/

/-- The word `s` is one of the command's words. -/
def has (s : String) (ws : List (List Char)) : Bool := ws.contains s.toList

/-- Some string field of the call's input contains `s`. -/
def inputHas (s : String) : Event → Bool
  | .call _ _ input => input.any fun (_, v) => occursIn s.toList v.toList
  | _ => false

/-- The call's shell text contains `s` anywhere. -/
def commandHas (s : String) (e : Event) : Bool :=
  match command e with
  | some c => occursIn s.toList c.toList
  | none => false

/-- The word after the first occurrence of the flag `f`. -/
def afterFlag (f : List Char) : List (List Char) → Option (List Char)
  | [] => none
  | a :: tl => if a == f then tl.head? else afterFlag f tl

/-- A word of decimal digits as its number. -/
def natOf (cs : List Char) : Option Nat :=
  if cs.isEmpty || !cs.all Char.isDigit then none
  else some (cs.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0)

/-- The number given as the word after the flag `f` (the `--flag=N` form is not read). -/
def flagNat (f : String) (ws : List (List Char)) : Option Nat := (afterFlag f.toList ws).bind natOf

/-- An optional number above `k`. -/
def above (o : Option Nat) (k : Nat) : Bool :=
  match o with
  | some n => decide (k < n)
  | none => false

/-- The words of the call's `compute.sh` command, if it has one. -/
def computeWords (e : Event) : Option (List (List Char)) :=
  ((programs e).find? fun (w, _) => endsWith "compute.sh".toList w).map (·.2)

/-- The call runs `compute.sh` with `p` holding of its words. -/
def computeHas (p : List (List Char) → Bool) (e : Event) : Bool :=
  match computeWords e with
  | some ws => p ws
  | none => false

/-- Some command of the call names the script `script` among its words, with `p` holding of them:
the script run directly or through the launcher (`./compute.sh python3 tools/x.py`). A command
merely naming the script as an argument (`cat tools/x.py`) counts too, so a rule that requires such
a call errs toward keeping. -/
def invokes (script : String) (p : List (List Char) → Bool) (e : Event) : Bool :=
  (programs e).any fun (_, ws) => ws.any (endsWith script.toList) && p ws

/-- A shell call the harness runs in the foreground. -/
def isForeground (e : Event) : Bool :=
  (isTool "Bash" e || isTool "exec" e) && e.field "run_in_background" != some "true"

/-- The seconds a `compute.sh` run is allowed: its `--timeout`, else 60 or twice its `--expect`. -/
def allowedSeconds (ws : List (List Char)) : Nat :=
  match flagNat "--timeout" ws with
  | some t => t
  | none => match flagNat "--expect" ws with
    | some x => max 60 (2 * x)
    | none => 60

/-- The words of a quoted argument, split at blanks. -/
def wordCount (w : List Char) : Nat := ((w.splitOn ' ').filter (!·.isEmpty)).length

/-- The file a call writes ends with `s`. -/
def pathEnds (s : String) (e : Event) : Bool :=
  match writePath e with
  | some p => endsWith s.toList p.toList
  | none => false

/-- The file a call writes contains `s` in its path. -/
def pathHas (s : String) (e : Event) : Bool :=
  match writePath e with
  | some p => occursIn s.toList p.toList
  | none => false

/-- A command word of the `pod` tool with the verb `v` (`lake -d tools/rented exe pod v ...`). -/
def podVerb (v : String) (e : Event) : Bool := (programs e).any fun (_, ws) => has "pod" ws && has v ws

/-- A single-dash option word holding the letter `a` (`-a`, `-avz`). -/
def shortFlagWithA (w : List Char) : Bool :=
  match w with
  | '-' :: c :: rest => c != '-' && (c :: rest).contains 'a'
  | _ => false

/-- The option `-x` or `-s` of `aria2c` asks for more than one connection, as `-x 16` or `-x16`. -/
def manyConnections (f : String) (ws : List (List Char)) : Bool :=
  above (flagNat f ws) 1 || ws.any fun w => hasPrefix f.toList w && above (natOf (w.drop 2)) 1

/-! Event predicates. -/

def anyCall : Pred := ⟨"anyCall", isCall, [bash "ls"]⟩
def resultEvent : Pred := ⟨"resultEvent", isResult, [.result "c" "out"]⟩
def refusalEvent : Pred := ⟨"refusalEvent", isRefusalEvent, [.refusal "hook" "no"]⟩
def commit : Pred := ⟨"commit", runs "git" (has "commit"), [bash "git commit -m x"]⟩
def ffBase : Pred := ⟨"ffBase", runs "ff-base.sh" (fun _ => true), [bash "tools/ff-base.sh"]⟩
def computeRun : Pred :=
  ⟨"computeRun", computeHas (fun _ => true), [bash "./compute.sh python3 x.py"]⟩
/-- A computer algebra system run outside the launcher. -/
def bareAlgebraRun : Pred := ⟨"bareAlgebraRun", fun e => (programs e).any fun (w, _) =>
    ["M2", "Singular", "gap", "gp", "msolve"].any fun p => endsWith p.toList w,
  [bash "Singular x.sing"]⟩
/-- A Python computation allowed more than 120 s without a `--kernel-reason` of six words. -/
def pythonWithoutKernelReason : Pred := ⟨"pythonWithoutKernelReason", computeHas fun ws =>
    ws.any (endsWith ".py".toList) && decide (120 < allowedSeconds ws) &&
      match afterFlag "--kernel-reason".toList ws with
      | some r => decide (wordCount r < 6)
      | none => true,
  [bash "./compute.sh --timeout 300 python3 x.py"]⟩
def pythonWithKernelReason : Pred := ⟨"pythonWithKernelReason",
  computeHas fun ws => ws.any (endsWith ".py".toList) && has "--kernel-reason" ws,
  [bash "./compute.sh --kernel-reason 'flint rank kernel reuses one factorization' python3 x.py"]⟩
def threadsOne : Pred := ⟨"threadsOne", computeHas fun ws => flagNat "--threads" ws == some 1,
  [bash "./compute.sh --threads 1 python3 x.py"]⟩
/-- A foreground run given more than 60 s and more than twice its `--expect`. -/
def timeoutBeyondAllowance : Pred := ⟨"timeoutBeyondAllowance", fun e => isForeground e &&
    computeHas (fun ws => above (flagNat "--timeout" ws) 60 &&
      match flagNat "--expect" ws, flagNat "--timeout" ws with
      | some x, some t => decide (2 * x < t)
      | _, _ => true) e,
  [bash "./compute.sh --timeout 120 python3 x.py"]⟩
def computeWithTimeout : Pred :=
  ⟨"computeWithTimeout", computeHas (has "--timeout"), [bash "./compute.sh --timeout 90 x"]⟩
def computeWithExpect : Pred :=
  ⟨"computeWithExpect", computeHas (has "--expect"), [bash "./compute.sh --expect 40 x"]⟩
/-- The foreground runs the Bash guard refuses. -/
def foregroundOverlong : Pred := ⟨"foregroundOverlong", fun e => isForeground e &&
    computeHas (fun ws => above (flagNat "--expect" ws) 60 || above (flagNat "--timeout" ws) 180 ||
      (above (flagNat "--timeout" ws) 60 && flagNat "--expect" ws == none)) e,
  [bash "./compute.sh --expect 120 python3 x.py"]⟩
/-- A long run missing the flags its length needs. -/
def longRunMissingFlags : Pred := ⟨"longRunMissingFlags", computeHas fun ws =>
    let expect := flagNat "--expect" ws
    (above (flagNat "--timeout" ws) 600 && expect == none) ||
    (above expect 600 && (match flagNat "--threads" ws with | some t => decide (t < 4) | none => false)
      && !has "--serial-reason" ws) ||
    (above expect 600 && !has "--sized-by" ws),
  [bash "./compute.sh --timeout 900 python3 x.py"]⟩
def overHalfHourUnapproved : Pred := ⟨"overHalfHourUnapproved",
  computeHas fun ws => above (flagNat "--timeout" ws) 1800 && !has "--user-approved" ws,
  [bash "./compute.sh --timeout 3600 --expect 3000 x"]⟩
def userApprovedRun : Pred :=
  ⟨"userApprovedRun", computeHas (has "--user-approved"), [bash "./compute.sh --user-approved 'yes' x"]⟩
def stopRun : Pred := ⟨"stopRun", fun e => isTool "TaskStop" e || runs "kill" (fun _ => true) e ||
    runs "pkill" (fun _ => true) e || runs "systemctl" (has "stop") e || podVerb "drop" e,
  [.call "s" "TaskStop" [], bash "kill 123"]⟩
def backgroundRun : Pred := ⟨"backgroundRun",
  fun e => isTool "Bash" e && e.field "run_in_background" == some "true",
  [.call "b" "Bash" [("command", "./compute.sh python3 x.py"), ("run_in_background", "true")]]⟩
def foregroundCall : Pred := ⟨"foregroundCall", isForeground, [bash "./compute.sh python3 x.py"]⟩
def armsWatchRun : Pred := ⟨"armsWatchRun", fun e => isTool "Monitor" e && inputHas "watch_run.py" e,
  [.call "m" "Monitor" [("command", "python3 tools/watch_run.py t1")]]⟩
def sshRun : Pred := ⟨"sshRun", fun e => (programs e).any fun (w, _) => endsWith "ssh".toList w,
  [bash "ssh pod 'ls'"]⟩
/-- A command run by hand on another machine without `timeout` around it. -/
def sshWithoutTimeout : Pred := ⟨"sshWithoutTimeout",
  fun e => (programs e).any fun (w, ws) => endsWith "ssh".toList w && !has "timeout" ws,
  [bash "ssh pod python3 x.py"]⟩
/-- A launcher run piped through a filter that shows part of its output. -/
def computePiped : Pred := ⟨"computePiped", fun e =>
    computeHas (fun _ => true) e && (programs e).any fun (w, _) =>
      ["grep", "head", "tail"].any fun p => endsWith p.toList w,
  [bash "./compute.sh python3 x.py | tail -5"]⟩
def writesPngFile : Pred :=
  ⟨"writesPngFile", pathEnds ".png", [.call "w" "Write" [("file_path", "plot.png")]]⟩
def evidencePack : Pred := ⟨"evidencePack",
  invokes "evidence_io.py" (fun ws => has "pack" ws && has "--replace" ws),
  [bash "./compute.sh --threads 1 python3 tools/evidence_io.py pack --replace research/results/d"]⟩
def saveRunOutput : Pred :=
  ⟨"saveRunOutput", invokes "save-run-output.py" (fun _ => true), [bash "tools/save-run-output.py t r o"]⟩
def editsNotebook : Pred := ⟨"editsNotebook", pathEnds "notebook.html", [edit "notebook.html"]⟩
def recordProvenance : Pred := ⟨"recordProvenance",
  invokes "record-provenance.py" (has "--out"), [bash "tools/record-provenance.py --out m.json f"]⟩
def timingReportStop : Pred := ⟨"timingReportStop",
  computeHas fun ws => has "report" ws && has "--stop" ws, [bash "./compute.sh report t --stop"]⟩
def htmlOutGiven : Pred := ⟨"htmlOutGiven", computeHas (has "--html-out"),
  [bash "./compute.sh report t --stop --html-out r/timing.html"]⟩
def archiveSession : Pred :=
  ⟨"archiveSession", invokes "archive-session.py" (fun _ => true), [bash "./tools/archive-session.py t"]⟩
def phaseMarker : Pred :=
  ⟨"phaseMarker", computeHas (has "phase"), [bash "./compute.sh phase t coding"]⟩
def timingStart : Pred := ⟨"timingStart", computeHas (has "start"), [bash "./compute.sh start t"]⟩
def timingStartWithModel : Pred := ⟨"timingStartWithModel",
  computeHas fun ws => has "start" ws && has "--model" ws, [bash "./compute.sh start t --model m"]⟩
/-- A Lean build or proof check outside the launcher's `formal_verification` category. -/
def leanCheckOutsideCategory : Pred := ⟨"leanCheckOutsideCategory", fun e =>
    let ps := programs e
    let isLean (w : List Char) (ws : List (List Char)) :=
      (endsWith "lake".toList w && (has "build" ws || has "lean" ws)) || endsWith "lean".toList w ||
        (endsWith "compute.sh".toList w && (has "lake" ws || has "lean" ws))
    ps.any (fun (w, ws) => isLean w ws) && !ps.any fun (w, ws) =>
      endsWith "compute.sh".toList w && has "--category" ws && has "formal_verification" ws,
  [bash "lake build"]⟩
def loadsRentedSkill : Pred := ⟨"loadsRentedSkill",
  fun e => isTool "Skill" e && e.field "skill" == some "rented-machine",
  [.call "k" "Skill" [("skill", "rented-machine")]]⟩
def createsPod : Pred := ⟨"createsPod", isTool "mcp__plugin_runpod_runpod__create-pod",
  [.call "p" "mcp__plugin_runpod_runpod__create-pod" []]⟩
def podMount : Pred := ⟨"podMount", podVerb "mount", [bash "lake -d tools/rented exe pod mount"]⟩
def podAdd : Pred := ⟨"podAdd", podVerb "add", [bash "lake -d tools/rented exe pod add 'j 1 4 x'"]⟩
/-- A queued job whose command holds a pipe, a redirect or a glob. -/
def podAddWithShell : Pred := ⟨"podAddWithShell", fun e => (programs e).any fun (_, ws) =>
    has "pod" ws && has "add" ws && ws.any fun w => w.contains '|' || w.contains '>' || w.contains '*',
  [bash "lake -d tools/rented exe pod add 'j 1 4 python3 x.py > out'"]⟩
def podQueueChange : Pred := ⟨"podQueueChange",
  fun e => podVerb "add" e || podVerb "drop" e || podVerb "rerun" e,
  [bash "lake -d tools/rented exe pod drop j"]⟩
def editsPodJobs : Pred := ⟨"editsPodJobs", pathEnds "pod_jobs.txt", [edit "tools/rented/pod_jobs.txt"]⟩
def armsPodWatch : Pred := ⟨"armsPodWatch", fun e => isTool "Monitor" e && inputHas "pod watch" e,
  [.call "m" "Monitor" [("command", "lake -d tools/rented exe pod watch")]]⟩
def watchFilterDropsQuiet : Pred := ⟨"watchFilterDropsQuiet", fun e =>
    isTool "Monitor" e && inputHas "pod watch" e && inputHas "grep" e && !inputHas "JOB QUIET" e,
  [.call "m" "Monitor" [("command", "lake -d tools/rented exe pod watch | grep DONE")]]⟩
def mentionsQueueLock : Pred :=
  ⟨"mentionsQueueLock", commandHas "queue.lock", [bash "flock queue.lock true"]⟩
def editsMcpConfig : Pred := ⟨"editsMcpConfig", fun e => pathEnds ".mcp.json" e || runs "claude" (has "mcp") e,
  [edit ".mcp.json"]⟩
/-- An `rsync` to `/workspace` with `-a`, or without `-rlpt`. -/
def rsyncWorkspaceWrongFlags : Pred := ⟨"rsyncWorkspaceWrongFlags", fun e => (programs e).any fun (w, ws) =>
    endsWith "rsync".toList w && ws.any (occursIn "/workspace".toList) &&
      (ws.any shortFlagWithA || !ws.any (hasPrefix "-rlpt".toList)),
  [bash "rsync -a src/ /workspace/src/"]⟩
def aria2ManyConnections : Pred := ⟨"aria2ManyConnections", fun e => (programs e).any fun (w, ws) =>
    endsWith "aria2c".toList w && (manyConnections "-x" ws || manyConnections "-s" ws),
  [bash "aria2c -x 16 http://h/f"]⟩
def editsReport : Pred := ⟨"editsReport", pathEnds "research/REPORT.md", [edit "research/REPORT.md"]⟩
def editsMainSkill : Pred := ⟨"editsMainSkill", pathEnds "engineering-discipline/SKILL.md",
  [edit "skills/engineering-discipline/SKILL.md"]⟩
def editsPersonalSkill : Pred := ⟨"editsPersonalSkill",
  pathEnds "engineering-discipline-personal/SKILL.md",
  [edit "skills/engineering-discipline-personal/SKILL.md"]⟩
def skillSubmoduleCommit : Pred := ⟨"skillSubmoduleCommit",
  runs "git" (fun ws => has "commit" ws && ws.any (occursIn "skills/engineering-discipline".toList)),
  [bash "git -C skills/engineering-discipline commit -m x"]⟩
def loadsMoveSkill : Pred := ⟨"loadsMoveSkill",
  fun e => isTool "Skill" e && e.field "skill" == some "move-changes-between-commits",
  [.call "k" "Skill" [("skill", "move-changes-between-commits")]]⟩
/-- A user message of only `^`. -/
def caretMessage : Pred := ⟨"caretMessage", fun
    | .user t => t.toList.filter (fun c => !c.isWhitespace) == ['^']
    | _ => false,
  [.user "^"]⟩
def cookieCopy : Pred :=
  ⟨"cookieCopy", runs "firefox_cookies.py" (fun _ => true), [bash "tools/firefox_cookies.py h.example"]⟩
def createsBranch : Pred := ⟨"createsBranch", runs "git" fun ws =>
    (has "checkout" ws && has "-b" ws) || (has "switch" ws && has "-c" ws) ||
      (has "worktree" ws && has "add" ws && has "-b" ws),
  [bash "git switch -c kbr/fix"]⟩
def delegates : Pred := ⟨"delegates", isTool "Agent", [.call "a" "Agent" [("prompt", "do x")]]⟩
def memoryWrite : Pred :=
  ⟨"memoryWrite", pathHas "/memory/", [edit "/home/u/.claude/projects/p/memory/note.md"]⟩
def editsTasksOrResearch : Pred := ⟨"editsTasksOrResearch",
  fun e => pathHas "tasks/" e || pathHas "research/" e, [edit "tasks/x/PLAN.md"]⟩
def autosquashRebase : Pred := ⟨"autosquashRebase",
  runs "git" (fun ws => has "rebase" ws && has "--autosquash" ws), [bash "git rebase -i --autosquash main"]⟩
def historyRewrite : Pred := ⟨"historyRewrite",
  runs "git" (fun ws => has "rebase" ws || (has "commit" ws && has "--amend" ws)),
  [bash "git rebase main"]⟩
def forcePush : Pred := ⟨"forcePush", runs "git" fun ws =>
    has "push" ws && (has "--force" ws || has "-f" ws || ws.any (hasPrefix "--force-with-lease".toList)),
  [bash "git push --force-with-lease origin b"]⟩
/-- A cycle's end: the research finisher or a task checkpoint. -/
def cycleEnd : Pred := ⟨"cycleEnd",
  fun e => invokes "finish-turn.py" (fun _ => true) e || invokes "task_checkpoint.py" (fun _ => true) e,
  [bash "./tools/finish-turn.py t1", bash "python3 tools/task_checkpoint.py --entry e.html"]⟩

def preds : List Pred :=
  [anyCall, resultEvent, refusalEvent, commit, ffBase, computeRun, bareAlgebraRun,
   pythonWithoutKernelReason, pythonWithKernelReason, threadsOne, timeoutBeyondAllowance,
   computeWithTimeout, computeWithExpect, foregroundOverlong, longRunMissingFlags,
   overHalfHourUnapproved, userApprovedRun, stopRun, backgroundRun, foregroundCall, armsWatchRun,
   sshRun, sshWithoutTimeout, computePiped, writesPngFile, evidencePack, saveRunOutput,
   editsNotebook, recordProvenance, timingReportStop, htmlOutGiven, archiveSession, phaseMarker,
   timingStart, timingStartWithModel, leanCheckOutsideCategory, loadsRentedSkill, createsPod,
   podMount, podAdd, podAddWithShell, podQueueChange, editsPodJobs, armsPodWatch,
   watchFilterDropsQuiet, mentionsQueueLock, editsMcpConfig, rsyncWorkspaceWrongFlags,
   aria2ManyConnections, editsReport, editsMainSkill, editsPersonalSkill, skillSubmoduleCommit,
   loadsMoveSkill, caretMessage, cookieCopy, createsBranch, delegates, memoryWrite,
   editsTasksOrResearch, autosquashRebase, historyRewrite, forcePush, cycleEnd]

theorem preds_wellFormed : preds.all Pred.wellFormed = true := by decide

/-- The mechanical predicates refuse the compliant forms beside their samples. -/
theorem compliant_forms :
    !bareAlgebraRun.test (bash "./compute.sh Singular x.sing") &&
    !leanCheckOutsideCategory.test
      (bash "./compute.sh --category formal_verification --expect 55 -- lake env lean R.lean") &&
    !leanCheckOutsideCategory.test (bash "lake -d tools/rented exe pod watch") &&
    !foregroundOverlong.test (bash "./compute.sh --expect 55 -- lake env lean R.lean") &&
    !foregroundOverlong.test
      (.call "b" "Bash" [("command", "./compute.sh --expect 300 x"), ("run_in_background", "true")]) &&
    !longRunMissingFlags.test (bash "./compute.sh --timeout 900 --expect 700 --sized-by r1 x") &&
    !overHalfHourUnapproved.test (bash "./compute.sh --timeout 3600 --user-approved 'ok' x") &&
    !pythonWithoutKernelReason.test
      (bash "./compute.sh --timeout 300 --kernel-reason 'flint rank kernel reuses one factorization' python3 x.py") &&
    !timeoutBeyondAllowance.test (bash "./compute.sh --timeout 100 --expect 50 x") &&
    !sshWithoutTimeout.test (bash "timeout 60 ssh pod ls") &&
    !computePiped.test (bash "./compute.sh python3 x.py") &&
    !rsyncWorkspaceWrongFlags.test (bash "rsync -rlpt src/ /workspace/src/") &&
    !podAddWithShell.test (bash "lake -d tools/rented exe pod add 'j<k 1 4 python3 x.py'") &&
    !aria2ManyConnections.test (bash "aria2c -x 1 http://h/f") &&
    !watchFilterDropsQuiet.test
      (.call "m" "Monitor" [("command", "lake -d tools/rented exe pod watch | grep -E 'DONE|JOB QUIET'")]) &&
    !caretMessage.test (.user "^ why?") &&
    !editsMainSkill.test (edit "skills/engineering-discipline-personal/SKILL.md") = true := by
  decide

/-! Atoms. -/

def commitInWorktree : Atom := ⟨"commitInWorktree",
  "Is this commit made in a persistent worktree whose branch synchronizes with a local base?", .call⟩
def editsSharedCheckout : Atom := ⟨"editsSharedCheckout",
  "Does this edit, made by a background session, change a file in the shared checkout rather than the session's own worktree?", .edit⟩
def breaksBranchTaskRules : Atom := ⟨"breaksBranchTaskRules",
  "Does this call break a task or evidence rule specific to the branch it works on?", .call⟩
def heavyLoopInPython : Atom := ⟨"heavyLoopInPython",
  "Does this edit put a heavy numerical loop in pure Python rather than compiled code?", .edit⟩
def handWrittenElimination : Atom := ⟨"handWrittenElimination",
  "Does this edit hand-write elimination for exact linear algebra in a C or C++ kernel instead of calling fflas-ffpack, FLINT, LinBox or NTL?", .edit⟩
def heavyLoopNotCompiledParallel : Atom := ⟨"heavyLoopNotCompiledParallel",
  "Does this edit write a custom heavy loop in a language other than C or C++, or a parallel one without OpenMP?", .edit⟩
def pythonOnlyComputation : Atom := ⟨"pythonOnlyComputation",
  "Does this run start a computation written in Python only?", .call⟩
def showsSecondsRuntime : Link := ⟨"showsSecondsRuntime",
  "Does this result show that the anchored Python-only computation runs in seconds?"⟩
def missesVectorization : Atom := ⟨"missesVectorization",
  "Does this edit leave unvectorized a computation that could be vectorized, or vectorize fully where chunking would keep within the memory budget?", .edit⟩
def notIncremental : Atom := ⟨"notIncremental",
  "Does this run lack checkpoints a long run needs, or repeat work a finished earlier run already did?", .call⟩
def seriesNotIncremental : Atom := ⟨"seriesNotIncremental",
  "Does this run compute a parameter series other than in one incremental pass, or recompute a shared prefix?", .call⟩
def longRun : Atom := ⟨"longRun", "Does this call launch a long-running computation?", .call⟩
def listsStagesOfRun : Link := ⟨"listsStagesOfRun",
  "Does this reply list the stages of the anchored run and the waste removed from them?"⟩
def runsSettledParameters : Atom := ⟨"runsSettledParameters",
  "Does this run compute parameters or outputs that proved results or archived runs already settle, or that the question doesn't need?", .call⟩
def reportsSlowNeededComputation : Atom := ⟨"reportsSlowNeededComputation",
  "Does this reply report that a computation the goal needs is too slow?", .reply⟩
def buildsFasterImplementation : Link := ⟨"buildsFasterImplementation",
  "Does this edit move the computation the anchored reply calls slow to a computer algebra system or a compiled kernel?"⟩
def defersLineForSlowness : Atom := ⟨"defersLineForSlowness",
  "Does this reply abandon or defer a line of work because an implementation is slow?", .reply⟩
def sameSeriesOtherInvocation : Link := ⟨"sameSeriesOtherInvocation",
  "Is this run another invocation of the anchored run's parameter series or of its validation cases?"⟩
def tripleNestedPythonLoop : Atom := ⟨"tripleNestedPythonLoop",
  "Does this edit nest Python loops three deep over non-literal ranges?", .edit⟩
def runsBudgetManyWorkers : Atom := ⟨"runsBudgetManyWorkers",
  "Does this run start as many worker processes as the CPU budget?", .call⟩
def oversubscribesCpus : Atom := ⟨"oversubscribesCpus",
  "Does this run's worker count times threads per worker exceed the CPU budget, or nest thread pools?", .call⟩
def algebraNameCollides : Atom := ⟨"algebraNameCollides",
  "Does this edit give a computer algebra script a custom name without a prefix, one that can collide with a built-in?", .edit⟩
def pariStackSharesLine : Atom := ⟨"pariStackSharesLine",
  "Does this edit put a PARI/GP stack-size default on a line with other settings?", .edit⟩
def parallelAlgebraRun : Atom := ⟨"parallelAlgebraRun",
  "Does this run start a computer algebra calculation that uses several threads?", .call⟩
def checksThreadSettings : Link := ⟨"checksThreadSettings",
  "Does this call check the effective thread settings of the anchored calculation?"⟩
def timeoutIsMargin : Atom := ⟨"timeoutIsMargin",
  "Is this run's --timeout a safety margin rather than a length derived from a count or a measured run?", .call⟩
def expectFromCount : Atom := ⟨"expectFromCount",
  "Is this run's --expect derived from a count of its work?", .call⟩
def measuresRunForExpect : Link := ⟨"measuresRunForExpect",
  "Is this result a measured run from which the anchored run's --expect is derived?"⟩
def approvesLongRun : Link := ⟨"approvesLongRun",
  "Does this user message approve the anchored run lasting over 30 minutes, in the words its --user-approved quotes?"⟩
def exhaustiveEnumeration : Atom := ⟨"exhaustiveEnumeration",
  "Does this run start an exhaustive enumeration?", .call⟩
def statesEnumerationSize : Link := ⟨"statesEnumerationSize",
  "Does this reply state the anchored enumeration's size and expected time?"⟩
def enumerationBeyondBudget : Atom := ⟨"enumerationBeyondBudget",
  "Does this run include enumeration cases beyond the time or memory budget?", .call⟩
def estimatesLargestCase : Atom := ⟨"estimatesLargestCase",
  "Does this reply estimate the time or size of the largest case of a series?", .reply⟩
def measuresSmallerCase : Link := ⟨"measuresSmallerCase",
  "Is this result a measured smaller run the anchored estimate extrapolates?"⟩
def longRunWithoutReductions : Atom := ⟨"longRunWithoutReductions",
  "Does this long run skip an available exact reduction, shared work or parallel path?", .call⟩
def validatesReplacement : Atom := ⟨"validatesReplacement",
  "Does this result validate a run that replaces another one still running?", .result⟩
def stopsSupersededRun : Link := ⟨"stopsSupersededRun",
  "Does this call stop the run the anchored result shows superseded?"⟩
def runsPastDecision : Atom := ⟨"runsPastDecision",
  "Does this run continue past the point where its question is decided, with no early exit?", .call⟩
def testNotSmallestSize : Atom := ⟨"testNotSmallestSize",
  "Does this run test at a larger size than the smallest informative one, skip symmetry classes or a sizing run, or scale a probe no result justified?", .call⟩
def waitsByFixedSleep : Atom := ⟨"waitsByFixedSleep",
  "Does this edit make a test or measurement script wait a fixed time rather than for the event it waits on?", .edit⟩
def detectionRun : Atom := ⟨"detectionRun",
  "Does this run run for a length chosen to detect something?", .call⟩
def statesRunLength : Link := ⟨"statesRunLength",
  "Does this reply state the anchored run's length, derived from what it must detect?"⟩
def presetTrainingSteps : Atom := ⟨"presetTrainingSteps",
  "Does this run train for a preset step count rather than until its measured held-out slope is spent?", .call⟩
def speedMeasurement : Atom := ⟨"speedMeasurement", "Does this run measure speed?", .call⟩
def namesMeasuredDecision : Link := ⟨"namesMeasuredDecision",
  "Does this reply name the decision the anchored speed measurement serves?"⟩
def measuresOnOtherDevice : Atom := ⟨"measuresOnOtherDevice",
  "Does this speed measurement run on another device than the work will run on?", .call⟩
def speedWithoutPublishedFigure : Atom := ⟨"speedWithoutPublishedFigure",
  "Does this reply report a speed measurement without a published figure for the same work beside it?", .reply⟩
def tunesHandBuiltPath : Atom := ⟨"tunesHandBuiltPath",
  "Does this edit tune a hand-built implementation path for speed?", .edit⟩
def runsPublishedBaseline : Link := ⟨"runsPublishedBaseline",
  "Does this run run the published engine for the anchored edit's work as a baseline here?"⟩
def showsSeveralFoldGap : Atom := ⟨"showsSeveralFoldGap",
  "Does this result show a speed gap of several times against a published figure?", .result⟩
def profilesGapByPart : Link := ⟨"profilesGapByPart",
  "Does this run profile by part the gap the anchored result shows?"⟩
def readingOmitsGap : Atom := ⟨"readingOmitsGap",
  "Does this reply report a later speed reading without the gap still left against the published figure?", .reply⟩
def skipsLargestProfilePart : Atom := ⟨"skipsLargestProfilePart",
  "Does this edit optimize a part of a profile other than its largest?", .edit⟩
def measurementUntimedCost : Atom := ⟨"measurementUntimedCost",
  "Does this run measure something without timing the measurement's own cost beside it?", .call⟩
def longWhileUserWaits : Atom := ⟨"longWhileUserWaits",
  "Does this call run in the foreground for more than a few seconds while the user waits in the conversation?", .call⟩
def runsLongerThanQuestion : Atom := ⟨"runsLongerThanQuestion",
  "Does this run last longer than its question needs?", .call⟩
def leavesRemoteProcesses : Atom := ⟨"leavesRemoteProcesses",
  "Does this command leave processes running on the other machine?", .call⟩
def endsLeftProcesses : Link := ⟨"endsLeftProcesses",
  "Does this call list and end what the anchored command left on the other machine?"⟩
def mayExceedMinute : Atom := ⟨"mayExceedMinute", "May this run take over a minute?", .call⟩
def startsRemoteRun : Atom := ⟨"startsRemoteRun", "Does this call start a run on another machine?", .call⟩
def armsRemoteWatcher : Link := ⟨"armsRemoteWatcher",
  "Does this command arm, on the other machine, a watcher of the anchored run, from a file with stdin closed?"⟩
def proceedsBesideRun : Link := ⟨"proceedsBesideRun",
  "Is this call work that proceeds while the anchored long run goes?"⟩
def inspectsOrEndsRun : Link := ⟨"inspectsOrEndsRun",
  "Is this event an inspection of the anchored run five minutes in (which step, memory), or its end within five minutes?"⟩
def scalesPastControl : Atom := ⟨"scalesPastControl",
  "Does this run scale a script past its control case?", .call⟩
def sizesExpensiveStep : Link := ⟨"sizesExpensiveStep",
  "Does this run size the expensive steps the anchored scaled run takes?"⟩
def delaysCaseWrites : Atom := ⟨"delaysCaseWrites",
  "Does this edit make a long run hold its progress unflushed or its completed cases unwritten until the end?", .edit⟩
def misplacesCompression : Atom := ⟨"misplacesCompression",
  "Does this write store new result or provenance data other than as zstd level 3, or compress source, documentation, timing HTML, a summary, an index, a manifest or an image?", .edit⟩
def savesNonJpegImage : Atom := ⟨"savesNonJpegImage",
  "Does this edit save an image other than as JPEG at quality 80?", .edit⟩
def commitsOthersRawOutput : Atom := ⟨"commitsOthersRawOutput",
  "Does this commit include another producer's raw output?", .call⟩
def dataScriptWithoutOut : Atom := ⟨"dataScriptWithoutOut",
  "Does this edit write a script producing important data without an --out PATH writing its complete result to a tracked location?", .edit⟩
def importantRunWithoutOut : Atom := ⟨"importantRunWithoutOut",
  "Does this run produce important output from a program without --out?", .call⟩
def savesThatRun : Link := ⟨"savesThatRun", "Does this call save the anchored run's output?"⟩
def importantRun : Atom := ⟨"importantRun", "Does this run produce output a research record needs?", .call⟩
def referencesOutputWithProvenance : Link := ⟨"referencesOutputWithProvenance",
  "Does this notebook edit reference the anchored run's output path with its command, parameters, seed, encoding and provenance?"⟩
def overwritesAcceptedResult : Atom := ⟨"overwritesAcceptedResult",
  "Does this run write to a path holding an accepted earlier result?", .call⟩
def unstructuredOrUnstreamed : Atom := ⟨"unstructuredOrUnstreamed",
  "Does this edit store data in an unstructured format, or generate, save, copy or hash a large file whole rather than streamed or chunked?", .edit⟩
def commitsSharedData : Atom := ⟨"commitsSharedData",
  "Does this commit add shared data files whose path, size and hash are recorded nowhere?", .call⟩
def capturedEqualsOut : Atom := ⟨"capturedEqualsOut",
  "Does this archive hold a captured output identical to its declared --out report?", .call⟩
def commitsCanonicalReport : Link := ⟨"commitsCanonicalReport",
  "Does this commit include the anchored archive's canonical report with the archive?"⟩
def inventsTiming : Atom := ⟨"inventsTiming",
  "Does this edit invent a timing category or backfill unmeasured time?", .edit⟩
def overlapsWorkerTimes : Atom := ⟨"overlapsWorkerTimes",
  "Does this edit add overlapping worker times in a timing report rather than exclusive wall-clock intervals?", .edit⟩
def hidesMixedTime : Atom := ⟨"hidesMixedTime",
  "Does this timing report leave undisclosed material mixed time, work before instrumentation or final generation after the snapshot?", .edit⟩
def inventsSplitAfterwards : Atom := ⟨"inventsSplitAfterwards",
  "Does this edit invent a split of time or an overhead estimate after the fact?", .edit⟩
def plansOrDraftsInTimedTurn : Atom := ⟨"plansOrDraftsInTimedTurn",
  "Does this reply plan or draft work in an instrumented turn?", .reply⟩
def marksWorkPhase : Link := ⟨"marksWorkPhase",
  "Does this phase marker set the phase of the work the anchored reply plans or drafts?"⟩
def carriesNewCode : Atom := ⟨"carriesNewCode",
  "Does this call carry a new code or patch argument?", .call⟩
def awaitedSourceBatch : Atom := ⟨"awaitedSourceBatch",
  "Does this call fetch an awaited source or web batch in an instrumented turn?", .call⟩
def combinesSourceFollowUp : Atom := ⟨"combinesSourceFollowUp",
  "Does this call combine a source follow-up with the phase marker for interpreting the previous batch?", .call⟩
def guessedModelLabel : Atom := ⟨"guessedModelLabel",
  "Does this timing start give a guessed or placeholder model label, or unknown for what could be established?", .call⟩
def codexSession : Atom := ⟨"codexSession", "Is this call made in a Codex session?", .call⟩
def jobSummaryOmitsPeak : Atom := ⟨"jobSummaryOmitsPeak",
  "Does this edit write a resource-limited job summary in which a failing or quarter-budget job doesn't report its own memory peak?", .edit⟩
def actsOnRentedMachine : Atom := ⟨"actsOnRentedMachine", "Does this call act on a rented machine?", .call⟩
def wrongRentalForm : Atom := ⟨"wrongRentalForm",
  "Does this call put on a Serverless batch a long, stateful or checkpointed run or one the user waits on, or on a Pod many short independent requests that can wait a day?", .call⟩
def quotesServerlessRate : Atom := ⟨"quotesServerlessRate",
  "Does this reply quote a Serverless batch's rate?", .reply⟩
def readsRate : Link := ⟨"readsRate", "Is this result a read of the rate the anchored reply quotes?"⟩
def podLacksSshPort : Atom := ⟨"podLacksSshPort",
  "Does this Pod creation leave out the port 70022/tcp?", .call⟩
def rentedMachineUnderused : Atom := ⟨"rentedMachineUnderused",
  "At this point, does a rented machine in use have a GPU below its slots or more than two usable CPUs idle?", .any⟩
def idleWithNothingQueued : Atom := ⟨"idleWithNothingQueued",
  "At this point, does a rented machine have idle CPUs and nothing queued?", .any⟩
def answersIdleCapacity : Link := ⟨"answersIdleCapacity",
  "Does this event answer the anchored idle capacity: a job answering an open question, more threads for a job that would use them, or a statement that none exists?"⟩
def makeWork : Atom := ⟨"makeWork",
  "Does this queued job keep a machine busy without answering an open question?", .call⟩
def holdsJobNeedlessly : Atom := ⟨"holdsJobNeedlessly",
  "Does this queued job wait on something it doesn't need, or hold GPU work back for more than it really needs?", .call⟩
def reportsJobFailure : Atom := ⟨"reportsJobFailure",
  "Does this result report a rented-machine job failing?", .result⟩
def readsFailedJob : Atom := ⟨"readsFailedJob",
  "Does this call read the failed rented-machine job's output or log?", .call⟩
def asksWhatRunsOnRented : Atom := ⟨"asksWhatRunsOnRented",
  "Does this reply ask the user what to run on a rented machine?", .reply⟩
def refusalBlocksRentedWork : Atom := ⟨"refusalBlocksRentedWork",
  "Does this refusal stop a step that keeps a rented machine busy?", .refusal⟩
def asksStandingGrant : Link := ⟨"asksStandingGrant",
  "Does this reply ask the user once for a standing grant, to be recorded in run_state, covering the step the anchored refusal stopped?"⟩
def showsJobMeasuresNothing : Atom := ⟨"showsJobMeasuresNothing",
  "Does this result show a running job measures nothing (superseded, duplicate or diverged)?", .result⟩
def stopsThatRun : Link := ⟨"stopsThatRun", "Does this call stop the run the anchored result is about?"⟩
def reportsQuietJob : Atom := ⟨"reportsQuietJob", "Does this result report a quiet job?", .result⟩
def inspectsQuietJob : Link := ⟨"inspectsQuietJob",
  "Does this call find out what the job the anchored result reports quiet is doing?"⟩
def startsUsingRented : Atom := ⟨"startsUsingRented",
  "Does this call start using a rented machine?", .call⟩
def monitorExpired : Atom := ⟨"monitorExpired",
  "Does this result report that the monitor on pod watch expired?", .result⟩
def reportsFreeSlot : Atom := ⟨"reportsFreeSlot", "Does this result report a free slot on the rented machine?", .result⟩
def endsTurnWithWorkLeft : Atom := ⟨"endsTurnWithWorkLeft",
  "Does this reply end the turn while code, reading or analysis remain to do beside the runs?", .reply⟩
def thinksOfNextJob : Atom := ⟨"thinksOfNextJob", "Does this reply name a next job for the rented machine?", .reply⟩
def waitsOnLock : Atom := ⟨"waitsOnLock", "Does this command wait for queue.lock to be released?", .call⟩
def afterRestart : Atom := ⟨"afterRestart",
  "Is this the first event after a session restart or an interrupted pod up while a rented machine is in use?", .any⟩
def checksRentedData : Link := ⟨"checksRentedData",
  "Does this call check the rented machine's data after the anchored restart?"⟩
def rentedAddressChanged : Atom := ⟨"rentedAddressChanged",
  "Does this result show a rented machine's address changed?", .result⟩
def signInExpired : Atom := ⟨"signInExpired", "Does this result show RunPod's sign-in failing?", .result⟩
def restoresSignIn : Link := ⟨"restoresSignIn", "Does this call restore the RunPod sign-in the anchored result shows failing?"⟩
def usesContainerDisk : Atom := ⟨"usesContainerDisk",
  "Does this call put a venv, checkpoint or result on a rented machine's container disk rather than /workspace?", .call⟩
def readsHardFromDisk : Atom := ⟨"readsHardFromDisk",
  "Does this call have a job read hard from disk data that would fit in /dev/shm within what jobs need of RAM?", .call⟩
def callsReadColdUnchecked : Atom := ⟨"callsReadColdUnchecked",
  "Does this reply call a read cold without a warm repeat clearly faster than it?", .reply⟩
def listsOwnIdea : Atom := ⟨"listsOwnIdea", "Does this reply list an idea or direction to pursue?", .reply⟩
def developsListedIdea : Link := ⟨"developsListedIdea", "Does this reply develop the idea the anchored reply listed?"⟩
def waitsForUserIdeas : Atom := ⟨"waitsForUserIdeas",
  "Does this reply wait for the user to propose ideas rather than originate them, other fields included?", .reply⟩
def changesPattern : Atom := ⟨"changesPattern", "Does this edit change a pattern in research/REPORT.md?", .edit⟩
def pureLogicOutsideLean : Atom := ⟨"pureLogicOutsideLean",
  "Does this edit, in the user's own project, put pure logic outside Lean or unproved, or impure logic outside Lean where Lean can run it?", .edit⟩
def nonLeanUndemanded : Atom := ⟨"nonLeanUndemanded",
  "Does this edit write code in a language other than Lean that no project or library demands, or more of it than the demand needs?", .edit⟩
def namesHabitBehindMistake : Atom := ⟨"namesHabitBehindMistake",
  "Does this reply name the habit behind the mistake, show it by mistakes of other kinds, and say why the agent didn't catch it?", .reply⟩
def mistakeWithoutHabit : Atom := ⟨"mistakeWithoutHabit",
  "Does this reply recognise the agent's own mistake without naming the habit behind it, shown by mistakes of other kinds, and why it wasn't caught?", .reply⟩
def readsSiteCookieCode : Link := ⟨"readsSiteCookieCode",
  "Does this read open the site's code that names the cookies the anchored copy needs?"⟩
def takesAllHostCookies : Atom := ⟨"takesAllHostCookies",
  "Does this cookie copy take every cookie of the host?", .call⟩
def cookieHeaderForReadable : Atom := ⟨"cookieHeaderForReadable",
  "Does this edit build a Cookie header by script for a read firefox_get.py could make?", .edit⟩
def descriptionLevelUnfixed : Atom := ⟨"descriptionLevelUnfixed",
  "Does this edit leave its level of description or notion of sameness unfixed, mix what is observed with how it is represented, or leave independent descriptions of one thing unrelated?", .edit⟩
def deepCheck : Atom := ⟨"deepCheck", "Does this run a costly deep check?", .call⟩
def cheapExhaustiveFirst : Link := ⟨"cheapExhaustiveFirst",
  "Is this run a cheap exhaustive check of what the anchored deep check examines?"⟩
def acceptsCoarseFailure : Atom := ⟨"acceptsCoarseFailure",
  "Does this reply accept a failure a coarse view reports without checking it for feasibility?", .reply⟩
def keepsHardToStateDesign : Atom := ⟨"keepsHardToStateDesign",
  "Does this edit keep a design in which what must hold is hard to say?", .edit⟩
def mrWork : Atom := ⟨"mrWork", "Is this commit work intended for a merge request?", .call⟩
def sideBranchAgainstDirection : Atom := ⟨"sideBranchAgainstDirection",
  "Does this call put work on a side branch of the user's own project for which the user directed working on main or master?", .call⟩
def relaysReadOnlyCommand : Atom := ⟨"relaysReadOnlyCommand",
  "Does this reply ask the user to run a read-only or diagnostic command the agent could run itself?", .reply⟩
def declinesAccessOffer : Atom := ⟨"declinesAccessOffer",
  "Does this reply decline or ignore the user's offer to set up the agent's read access?", .reply⟩
def rediagnosesSymptom : Atom := ⟨"rediagnosesSymptom",
  "Does this reply start diagnosing a symptom that has occurred before in the work?", .reply⟩
def searchesRootCaused : Link := ⟨"searchesRootCaused",
  "Does this call check whether the anchored symptom matches something already root-caused?"⟩
def buildsNewTool : Atom := ⟨"buildsNewTool", "Does this edit build a new tool, script, check or mechanism?", .edit⟩
def searchesForExistingJob : Link := ⟨"searchesForExistingJob",
  "Does this call search for something that already does the anchored edit's job, by the job done?"⟩
def buildDecisionOmitsSearch : Atom := ⟨"buildDecisionOmitsSearch",
  "Does this reply decide to build something without naming, in that sentence, the search made and what it found?", .reply⟩
def bugReportWithoutRepro : Atom := ⟨"bugReportWithoutRepro",
  "Does this reply report a bug without the exact command and output, observed against expected?", .reply⟩
def briefLacksIdentifiers : Atom := ⟨"briefLacksIdentifiers",
  "Does this delegation's brief lack the exact identifiers (repository, pinned versions, file paths, commands) or the deliverable's precise shape?", .call⟩
def buildsRequestPart : Atom := ⟨"buildsRequestPart", "Does this edit build a part of the user's request?", .edit⟩
def checksPartAgainstTarget : Link := ⟨"checksPartAgainstTarget",
  "Does this call check the request part the anchored edit builds against the target the request names?"⟩
def buildsPurposelessPart : Atom := ⟨"buildsPurposelessPart",
  "Does this edit build a part of a request that serves no purpose in the target it names?", .edit⟩
def skipsPartSilently : Atom := ⟨"skipsPartSilently",
  "Does this reply leave a purposeless part of a request unbuilt without saying what the target does instead?", .reply⟩
def unexplainedJargon : Atom := ⟨"unexplainedJargon",
  "Does this reply use an unfamiliar mechanism, a term or its own jargon without explaining it or asking?", .reply⟩
def asksWhatChoiceGains : Atom := ⟨"asksWhatChoiceGains",
  "Does this user message ask what a design choice of the agent's gains?", .user⟩
def statesGain : Link := ⟨"statesGain", "Does this reply say what the design choice the anchored message asks about gains?"⟩
def hidesSecondOrderEffects : Atom := ⟨"hidesSecondOrderEffects",
  "Does this reply propose a design choice without its non-obvious second-order consequences, with how often and how much where numbers are at hand?", .reply⟩
def designPartUncosted : Atom := ⟨"designPartUncosted",
  "Does this reply describe a design part without its cost (where it runs, how often, what it reads)?", .reply⟩
def perCallRecomputes : Atom := ⟨"perCallRecomputes",
  "Does this edit make a per-call path compute a result rather than read one kept current elsewhere?", .edit⟩
def movesOnWithItemOpen : Atom := ⟨"movesOnWithItemOpen",
  "Does this reply move to the next design or cleanup item while an earlier one is unresolved or unrecorded?", .reply⟩
def asksPerStepOnApprovedPlan : Atom := ⟨"asksPerStepOnApprovedPlan",
  "Does this reply ask the user's leave for a step of a plan the user already approved?", .reply⟩
def userTextUnhelpful : Atom := ⟨"userTextUnhelpful",
  "Does this edit write product copy, an error or a warning that doesn't say what is happening, offer a way out of a refusal, make a failure visible or tell the admin where to look?", .edit⟩
def treatsAnswerAsCompletion : Atom := ⟨"treatsAnswerAsCompletion",
  "Does this reply treat answering the latest message as completing a requested artifact?", .reply⟩
def showsRunWrong : Atom := ⟨"showsRunWrong",
  "Does this result show a run doing the wrong thing, or one a decision superseded?", .result⟩
def handsOverArtifact : Atom := ⟨"handsOverArtifact", "Does this reply hand an artifact over?", .reply⟩
def answersReviewerQuestions : Atom := ⟨"answersReviewerQuestions",
  "Does this reply answer the artifact's reviewer's first questions (its size, how it compares with its kind, why it differs)?", .reply⟩
def measuresArtifact : Link := ⟨"measuresArtifact",
  "Is this result a measurement of the artifact the anchored reply hands over?"⟩
def makesRuleDefinedArtifact : Atom := ⟨"makesRuleDefinedArtifact",
  "Does this edit make an artifact of a kind the rules define (a ledger, a request, a review file, a commit message)?", .edit⟩
def readsDefiningRule : Link := ⟨"readsDefiningRule",
  "Does this read open the rule defining the anchored artifact's kind?"⟩
def proseRuleWithoutCheck : Atom := ⟨"proseRuleWithoutCheck",
  "Does this edit add a rule that is only prose, with no generator or check giving its format one home?", .edit⟩
def ignoresUsersNextState : Atom := ⟨"ignoresUsersNextState",
  "Does this reply leave unaddressed part of the state the user will be in after their message (a run to stop, work to save, what to do meanwhile)?", .reply⟩
def writesDurableKnowledge : Atom := ⟨"writesDurableKnowledge",
  "Does this edit write what was learned into a persistent doc?", .edit⟩
def summarizesLearned : Link := ⟨"summarizesLearned",
  "Does this reply summarize what the anchored edit writes into the doc?"⟩
def asksToPersist : Link := ⟨"asksToPersist",
  "Does this user message ask for the anchored edit's write into a persistent doc?"⟩
def describesPastState : Atom := ⟨"describesPastState",
  "Does this edit make a committed comment, doc, instruction file or living plan describe anything other than the current state?", .edit⟩
def implementsInterface : Atom := ⟨"implementsInterface", "Does this edit implement an interface?", .edit⟩
def draftsContract : Link := ⟨"draftsContract",
  "Does this edit draft the contract (non-obvious semantics, invariants, design reasons) of the interface the anchored edit implements?"⟩
def historicalNarration : Atom := ⟨"historicalNarration",
  "Does this edit write historical narration (we considered X, this used to be Y, not yet Z) in a committed doc?", .edit⟩
def recordsCommitHash : Atom := ⟨"recordsCommitHash",
  "Does this edit record a commit hash in a record meant to stay accurate?", .edit⟩
def hashOrUntimedCount : Atom := ⟨"hashOrUntimedCount",
  "Does this edit include a commit hash or a count of tests without its time?", .edit⟩
def unresolvableReference : Atom := ⟨"unresolvableReference",
  "Does this edit give a reference with no referent the reader can look up or act on?", .edit⟩
def correctsAgentOrStatesPreference : Atom := ⟨"correctsAgentOrStatesPreference",
  "Does this user message correct the agent or state a preference about how it works?", .user⟩
def writesStandingRule : Link := ⟨"writesStandingRule",
  "Does this edit write the anchored correction as a general standing rule in its durable home, without the case's jargon?"⟩
def addsRule : Atom := ⟨"addsRule", "Does this edit add a rule to an instruction file or skill?", .edit⟩
def readsOwningRule : Link := ⟨"readsOwningRule",
  "Does this read open the rule already owning the concern of the rule the anchored edit adds?"⟩
def addsCoveredRule : Atom := ⟨"addsCoveredRule",
  "Does this edit add a rule for a requirement an existing rule already covers?", .edit⟩
def duplicatesRule : Atom := ⟨"duplicatesRule",
  "Does this edit leave a second authoritative copy of a rule or skill, or keep one in a file that doesn't travel between machines?", .edit⟩
def correctsAnalysis : Atom := ⟨"correctsAnalysis",
  "Does this user message correct the agent's analysis or work?", .user⟩
def answersHowMade : Link := ⟨"answersHowMade",
  "Does this reply answer the anchored correction about how the work was made?"⟩
def undoesSoundWork : Atom := ⟨"undoesSoundWork",
  "Does this edit undo work that isn't wrong because it was done at the wrong time?", .edit⟩
def raisesIdea : Atom := ⟨"raisesIdea", "Does this reply raise an idea or a promising lead?", .reply⟩
def recordsIdea : Link := ⟨"recordsIdea", "Does this edit record the anchored idea in its durable home?"⟩
def padsOrLosesProse : Atom := ⟨"padsOrLosesProse",
  "Does this text pad its prose with wording or meta-commentary, or lose substance or a required record?", .any⟩
def sentenceNotForNextAction : Atom := ⟨"sentenceNotForNextAction",
  "Does this text hold a sentence its reader can't use for their next action?", .any⟩
def descriptionNarratesCheck : Atom := ⟨"descriptionNarratesCheck",
  "Does this edit make a description say when or on which branch state something was checked, rather than what holds at the tip?", .edit⟩
def auditsCommitBothWays : Link := ⟨"auditsCommitBothWays",
  "Does this call audit the anchored commit's staged changes against its message both ways?"⟩
def commitMixesConcerns : Atom := ⟨"commitMixesConcerns",
  "Does this commit mix changes of different logical lines (layers, unrelated fixes)?", .call⟩
def lowerLayerRidesUnused : Atom := ⟨"lowerLayerRidesUnused",
  "Does this commit carry lower-layer code added for a later commit that this commit doesn't use?", .call⟩
def opensMrReview : Atom := ⟨"opensMrReview",
  "Does this publication offer a branch for a merge request's review?", .publish⟩
def mrHistoryUnfolded : Atom := ⟨"mrHistoryUnfolded",
  "Does this branch offered for review keep WIP or correction commits unfolded into the commits they belong to?", .publish⟩
def rewritesNonMrHistory : Atom := ⟨"rewritesNonMrHistory",
  "Does this rewrite change earlier commits of work that won't become a merge request, with no concrete reason such as private data?", .call⟩
def changesSentDocument : Atom := ⟨"changesSentDocument",
  "Does this edit change a document already sent to its reader?", .edit⟩
def smallDamageOnly : Atom := ⟨"smallDamageOnly",
  "Does this force push rewrite pushed history whose damage is small?", .call⟩
def deploymentSpecificDesign : Atom := ⟨"deploymentSpecificDesign",
  "Does this text accept a design with a per-deployment or per-instance literal?", .any⟩

/-! Rules. -/

/-- Rule 841: a worktree commit is followed by the base synchronization, before the next commit; a
background session edits its own worktree, and the branch's own rules hold. -/
def worktreeDiscipline : Rule where
  number := 841
  keyword := .must
  domain := .tasks
  formula := (ev commit ∧ₗ atom commitInWorktree ⟹ eventually (ev ffBase)) ∧ₗ
    (ev commit ⟹ ¬ₗ since (ev commit ∧ₗ atom commitInWorktree) (ev ffBase)) ∧ₗ
    never (ev editing ∧ₗ atom editsSharedCheckout) ∧ₗ never (ev anyCall ∧ₗ atom breaksBranchTaskRules)

/-- Rule 842: no heavy numerical loop in pure Python. -/
def heavyLoopsCompiled : Rule where
  number := 842
  keyword := .must
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom heavyLoopInPython)

/-- Rule 843: exact linear algebra in a kernel calls a library, never hand-written elimination. -/
def linearAlgebraLibraries : Rule where
  number := 843
  keyword := .must
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom handWrittenElimination)

/-- Rule 845: a computer algebra script runs through the launcher. -/
def algebraThroughLauncher : Rule where
  number := 845
  keyword := .must
  domain := .mathematics
  formula := never (ev bareAlgebraRun)

/-- Rule 846: heavy loops in C or C++ with OpenMP; a Python-only computation shown to run in
seconds first. -/
def heavyLoopsInC : Rule where
  number := 846
  keyword := .must
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom heavyLoopNotCompiledParallel) ∧ₗ
    (ev computeRun ∧ₗ atom pythonOnlyComputation ⟹ once (ev resultEvent ∧ₗ link showsSecondsRuntime))

/-- Rule 847: vectorize, chunking within memory, unless a reason is given. -/
def vectorizeAndChunk : Rule where
  number := 847
  keyword := .should
  domain := .mathematics
  formula := ev editing ∧ₗ atom missesVectorization ⟹ atom justified

/-- Rule 848: every computation incremental. -/
def incrementalComputation : Rule where
  number := 848
  keyword := .must
  domain := .mathematics
  formula := never (ev computeRun ∧ₗ atom notIncremental)

/-- Rule 849: a parameter series in one incremental pass, shared prefixes once. -/
def seriesInOnePass : Rule where
  number := 849
  keyword := .must
  domain := .mathematics
  formula := never (ev computeRun ∧ₗ atom seriesNotIncremental)

/-- Rule 850: a long run's stages listed before it, and nothing settled recomputed. -/
def stagesBeforeLaunch : Rule where
  number := 850
  keyword := .must
  domain := .mathematics
  formula := (ev computeRun ∧ₗ atom longRun ⟹ once (ev reply ∧ₗ link listsStagesOfRun)) ∧ₗ
    never (ev computeRun ∧ₗ atom runsSettledParameters)

/-- Rule 851: a slow needed computation gets a faster implementation in the same cycle (with no
cycle's end between the report and the edit), and the line goes on. -/
def slowCallsForKernel : Rule where
  number := 851
  keyword := .must
  domain := .mathematics
  formula := (ev reply ∧ₗ atom reportsSlowNeededComputation ⟹
      eventually (ev editing ∧ₗ link buildsFasterImplementation ∧ₗ
        since (ev reply ∧ₗ atom reportsSlowNeededComputation) (ev cycleEnd))) ∧ₗ
    never (ev reply ∧ₗ atom defersLineForSlowness)

/-- Rule 852: a long Python computation names its kernel and reuse in six words or more. -/
def kernelReason : Rule where
  number := 852
  keyword := .must
  domain := .mathematics
  formula := never (ev pythonWithoutKernelReason)

/-- Rule 853: a series and its validation cases in one invocation. -/
def seriesInOneInvocation : Rule where
  number := 853
  keyword := .must
  domain := .mathematics
  formula := never (ev computeRun ∧ₗ once (ev computeRun ∧ₗ link sameSeriesOtherInvocation))

/-- Rule 854: no Python loops three deep over non-literal ranges. -/
def noTripleLoops : Rule where
  number := 854
  keyword := .must
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom tripleNestedPythonLoop)

/-- Rule 855: workers times threads within the budget; `--threads 1` for a budget of workers. -/
def threadBudget : Rule where
  number := 855
  keyword := .must
  domain := .mathematics
  formula := never (ev computeRun ∧ₗ atom oversubscribesCpus) ∧ₗ
    (ev computeRun ∧ₗ atom runsBudgetManyWorkers ⟹ ev threadsOne)

/-- Rule 856: custom names in algebra scripts carry a prefix. -/
def prefixedAlgebraNames : Rule where
  number := 856
  keyword := .must
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom algebraNameCollides)

/-- Rule 857: PARI/GP stack defaults on their own lines; thread settings checked first. -/
def pariSettings : Rule where
  number := 857
  keyword := .must
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom pariStackSharesLine) ∧ₗ
    (ev computeRun ∧ₗ atom parallelAlgebraRun ⟹ once (ev anyCall ∧ₗ link checksThreadSettings))

/-- Rule 858: a foreground run within 60 s or twice its `--expect`; `--expect` from a count or a
measured run, `--timeout` never a margin. -/
def runAllowance : Rule where
  number := 858
  keyword := .must
  domain := .mathematics
  formula := never (ev timeoutBeyondAllowance) ∧ₗ never (ev computeWithTimeout ∧ₗ atom timeoutIsMargin) ∧ₗ
    (ev computeWithExpect ⟹ atom expectFromCount ∨ₗ once (ev resultEvent ∧ₗ link measuresRunForExpect))

/-- Rule 859: no foreground run the Bash guard refuses. -/
def noLongForeground : Rule where
  number := 859
  keyword := .mustNot
  domain := .mathematics
  formula := never (ev foregroundOverlong)

/-- Rule 860: a run over ten minutes carries `--expect`, `--serial-reason` and `--sized-by`. -/
def longRunFlags : Rule where
  number := 860
  keyword := .must
  domain := .mathematics
  formula := never (ev longRunMissingFlags)

/-- Rule 861: no run over 30 minutes without the user's quoted approval. -/
def halfHourNeedsApproval : Rule where
  number := 861
  keyword := .mustNot
  domain := .mathematics
  formula := never (ev overHalfHourUnapproved) ∧ₗ (ev userApprovedRun ⟹ once (ev user ∧ₗ link approvesLongRun))

/-- Rule 862: an enumeration's size and time stated before it runs, cases beyond the budget cut. -/
def enumerationSized : Rule where
  number := 862
  keyword := .must
  domain := .mathematics
  formula := (ev computeRun ∧ₗ atom exhaustiveEnumeration ⟹ once (ev reply ∧ₗ link statesEnumerationSize)) ∧ₗ
    never (ev computeRun ∧ₗ atom enumerationBeyondBudget)

/-- Rule 863: a largest case estimated from a measured smaller run. -/
def estimateFromMeasurement : Rule where
  number := 863
  keyword := .must
  domain := .mathematics
  formula := ev reply ∧ₗ atom estimatesLargestCase ⟹ once (ev resultEvent ∧ₗ link measuresSmallerCase)

/-- Rule 864: a long run applies the reductions, shared work and parallel paths at hand. -/
def reductionsBeforeLongRun : Rule where
  number := 864
  keyword := .must
  domain := .mathematics
  formula := never (ev computeRun ∧ₗ atom longRunWithoutReductions)

/-- Rule 865: a superseded run stopped once its replacement is validated; a computation ends when
its question is decided. -/
def stopSupersededRuns : Rule where
  number := 865
  keyword := .must
  domain := .mathematics
  formula := (ev resultEvent ∧ₗ atom validatesReplacement ⟹ eventually (ev stopRun ∧ₗ link stopsSupersededRun)) ∧ₗ
    never (ev computeRun ∧ₗ atom runsPastDecision)

/-- Rule 866: tests at the smallest informative size, unless a reason is given. -/
def smallestInformativeSize : Rule where
  number := 866
  keyword := .should
  domain := .mathematics
  formula := ev computeRun ∧ₗ atom testNotSmallestSize ⟹ atom justified

/-- Rule 867: a wait ends on its event; a run's length is stated before launch. -/
def waitsOnEvents : Rule where
  number := 867
  keyword := .must
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom waitsByFixedSleep) ∧ₗ
    (ev computeRun ∧ₗ atom detectionRun ⟹ once (ev reply ∧ₗ link statesRunLength))

/-- Rule 868: no preset training step count. -/
def trainingBySlope : Rule where
  number := 868
  keyword := .must
  domain := .mathematics
  formula := never (ev computeRun ∧ₗ atom presetTrainingSteps)

/-- Rule 869: a speed measurement names its decision first and runs on the work's device. -/
def speedMeasurementPurpose : Rule where
  number := 869
  keyword := .must
  domain := .mathematics
  formula := (ev computeRun ∧ₗ atom speedMeasurement ⟹ once (ev reply ∧ₗ link namesMeasuredDecision)) ∧ₗ
    never (ev computeRun ∧ₗ atom measuresOnOtherDevice)

/-- Rule 870: a speed reading beside a published figure; the published engine run before tuning a
hand-built path. -/
def publishedBaseline : Rule where
  number := 870
  keyword := .must
  domain := .mathematics
  formula := never (ev reply ∧ₗ atom speedWithoutPublishedFigure) ∧ₗ
    (ev editing ∧ₗ atom tunesHandBuiltPath ⟹ once (ev computeRun ∧ₗ link runsPublishedBaseline))

/-- Rule 871: a several-fold gap profiled by part, each later reading stating the gap left, work on
the largest part. -/
def profileTheGap : Rule where
  number := 871
  keyword := .must
  domain := .mathematics
  formula := (ev resultEvent ∧ₗ atom showsSeveralFoldGap ⟹ eventually (ev computeRun ∧ₗ link profilesGapByPart)) ∧ₗ
    never (ev reply ∧ₗ atom readingOmitsGap) ∧ₗ never (ev editing ∧ₗ atom skipsLargestProfilePart)

/-- Rule 872: a measure's own cost timed beside it. -/
def timeTheMeasure : Rule where
  number := 872
  keyword := .must
  domain := .mathematics
  formula := never (ev computeRun ∧ₗ atom measurementUntimedCost)

/-- Rule 873: no long foreground run while the user waits; a run lasts what its question needs. -/
def backgroundWhileWaiting : Rule where
  number := 873
  keyword := .must
  domain := .mathematics
  formula := never (ev foregroundCall ∧ₗ atom longWhileUserWaits) ∧ₗ
    never (ev computeRun ∧ₗ atom runsLongerThanQuestion)

/-- Rule 874: a remote command under `timeout`, and what it left there ended. -/
def remoteUnderTimeout : Rule where
  number := 874
  keyword := .must
  domain := .mathematics
  formula := never (ev sshWithoutTimeout) ∧ₗ
    (ev sshRun ∧ₗ atom leavesRemoteProcesses ⟹ eventually (ev anyCall ∧ₗ link endsLeftProcesses))

/-- Rule 875: the call after a background run that may take over a minute arms its monitor. -/
def monitorNext : Rule where
  number := 875
  keyword := .must
  domain := .mathematics
  formula := (ev anyCall ∧ₗ ¬ₗ ev armsWatchRun ⟹
      ¬ₗ since (ev backgroundRun ∧ₗ atom mayExceedMinute) (ev anyCall)) ∧ₗ
    (ev backgroundRun ∧ₗ atom mayExceedMinute ⟹ eventually (ev armsWatchRun))

/-- Rule 876: a run on another machine gets a watcher there. -/
def remoteWatcher : Rule where
  number := 876
  keyword := .must
  domain := .mathematics
  formula := ev anyCall ∧ₗ atom startsRemoteRun ⟹ eventually (ev sshRun ∧ₗ link armsRemoteWatcher)

/-- Rule 877: work proceeds while a long run goes. -/
def workBesideRuns : Rule where
  number := 877
  keyword := .must
  domain := .mathematics
  formula := ev backgroundRun ∧ₗ atom longRun ⟹ eventually (ev anyCall ∧ₗ link proceedsBesideRun)

/-- Rule 878: a run still going after five minutes is inspected. -/
def fiveMinuteDecision : Rule where
  number := 878
  keyword := .must
  domain := .mathematics
  formula := ev backgroundRun ∧ₗ atom longRun ⟹
    eventually ((ev anyCall ∨ₗ ev resultEvent) ∧ₗ link inspectsOrEndsRun)

/-- Rule 879: expensive steps sized before a script scales past its control case. -/
def sizeBeforeScaling : Rule where
  number := 879
  keyword := .must
  domain := .mathematics
  formula := ev computeRun ∧ₗ atom scalesPastControl ⟹ once (ev computeRun ∧ₗ link sizesExpensiveStep)

/-- Rule 880: long runs observable: no filter on the launcher, progress flushed, cases written. -/
def observableRuns : Rule where
  number := 880
  keyword := .must
  domain := .mathematics
  formula := never (ev computePiped) ∧ₗ never (ev editing ∧ₗ atom delaysCaseWrites)

/-- Rule 881: results zstd-3, readable files uncompressed. -/
def zstdResults : Rule where
  number := 881
  keyword := .must
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom misplacesCompression)

/-- Rule 882: images JPEG at quality 80, never PNG. -/
def jpegImages : Rule where
  number := 882
  keyword := .must
  domain := .mathematics
  formula := never (ev writesPngFile ∨ₗ (ev editing ∧ₗ atom savesNonJpegImage))

def commitsUnpackedPaths : Atom := ⟨"commitsUnpackedPaths",
  "Does this commit stage a raw path whose packed copy exists, or keep a link naming the raw path?", .call⟩

/-- Rule 883: another producer's raw output packed before it is committed, the compressed paths
staged and the links updated. -/
def packBeforeCommit : Rule where
  number := 883
  keyword := .must
  domain := .mathematics
  formula := (ev commit ∧ₗ atom commitsOthersRawOutput ⟹ once (ev evidencePack)) ∧ₗ
    never (ev commit ∧ₗ atom commitsUnpackedPaths)

/-- Rule 884: a data-producing script takes `--out` to a tracked location. -/
def scriptsTakeOut : Rule where
  number := 884
  keyword := .must
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom dataScriptWithoutOut)

/-- Rule 885: a run without `--out` saved with `save-run-output.py`. -/
def saveRunsWithoutOut : Rule where
  number := 885
  keyword := .must
  domain := .mathematics
  formula := ev computeRun ∧ₗ atom importantRunWithoutOut ⟹ eventually (ev saveRunOutput ∧ₗ link savesThatRun)

/-- Rule 886: a run's output referenced in the notebook with its provenance. -/
def referenceOutputs : Rule where
  number := 886
  keyword := .must
  domain := .mathematics
  formula := ev computeRun ∧ₗ atom importantRun ⟹ eventually (ev editsNotebook ∧ₗ link referencesOutputWithProvenance)

/-- Rule 887: distinct run paths, no accepted result overwritten. -/
def distinctRunPaths : Rule where
  number := 887
  keyword := .must
  domain := .mathematics
  formula := never (ev computeRun ∧ₗ atom overwritesAcceptedResult)

/-- Rule 888: structured formats, streamed or chunked, unless a reason is given. -/
def structuredStreamed : Rule where
  number := 888
  keyword := .should
  domain := .mathematics
  formula := ev editing ∧ₗ atom unstructuredOrUnstreamed ⟹ atom justified

/-- Rule 889: shared data's path, size and hash recorded before its commit, unless a reason is
given. -/
def provenanceManifest : Rule where
  number := 889
  keyword := .should
  domain := .mathematics
  formula := ev commit ∧ₗ atom commitsSharedData ⟹ once (ev recordProvenance) ∨ₗ atom justified

/-- Rule 890: a stopped timing session exported to HTML and archived. -/
def exportAndArchive : Rule where
  number := 890
  keyword := .must
  domain := .mathematics
  formula := ev timingReportStop ⟹ ev htmlOutGiven ∧ₗ eventually (ev archiveSession)

/-- Rule 891: no invented timing category or backfilled time. -/
def noInventedTiming : Rule where
  number := 891
  keyword := .mustNot
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom inventsTiming)

/-- Rule 892: an archive's canonical report committed with it. -/
def commitCanonicalReport : Rule where
  number := 892
  keyword := .must
  domain := .mathematics
  formula := ev archiveSession ∧ₗ atom capturedEqualsOut ⟹ eventually (ev commit ∧ₗ link commitsCanonicalReport)

/-- Rule 893: exclusive intervals, no overlapping worker times added. -/
def exclusiveIntervals : Rule where
  number := 893
  keyword := .must
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom overlapsWorkerTimes)

/-- Rule 894: mixed time disclosed, no split invented afterwards. -/
def discloseMixedTime : Rule where
  number := 894
  keyword := .must
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom hidesMixedTime) ∧ₗ never (ev editing ∧ₗ atom inventsSplitAfterwards)

/-- Rule 895: the work phase marked before planning or drafting. -/
def phaseBeforeDrafting : Rule where
  number := 895
  keyword := .must
  domain := .mathematics
  formula := ev reply ∧ₗ atom plansOrDraftsInTimedTurn ⟹ once (ev phaseMarker ∧ₗ link marksWorkPhase)

/-- Rule 896: no phase marker in a call carrying new code. -/
def markerApartFromCode : Rule where
  number := 896
  keyword := .mustNot
  domain := .mathematics
  formula := never (ev phaseMarker ∧ₗ atom carriesNewCode)

/-- Rule 897: an awaited source batch's call sets the interpreting phase; a follow-up is marked
apart. -/
def phaseAfterSources : Rule where
  number := 897
  keyword := .must
  domain := .mathematics
  formula := (ev anyCall ∧ₗ atom awaitedSourceBatch ⟹ ev phaseMarker) ∧ₗ
    never (ev phaseMarker ∧ₗ atom combinesSourceFollowUp)

/-- Rule 898: Lean builds and proof checks in the `formal_verification` category. -/
def leanInCategory : Rule where
  number := 898
  keyword := .must
  domain := .mathematics
  formula := never (ev leanCheckOutsideCategory)

def startNeedsModelLabel : Atom := ⟨"startNeedsModelLabel",
  "Is this timing start made where no session metadata gives the model and no MATH_AGENT_MODEL is set?", .call⟩

/-- Rule 899: no guessed model label; no `--model` on a Codex start; without metadata, a `--model`
label. -/
def honestModelLabel : Rule where
  number := 899
  keyword := .mustNot
  domain := .mathematics
  formula := never (ev timingStart ∧ₗ atom guessedModelLabel) ∧ₗ
    never (ev timingStartWithModel ∧ₗ atom codexSession) ∧ₗ
    never (ev timingStart ∧ₗ ¬ₗ ev timingStartWithModel ∧ₗ atom startNeedsModelLabel)

/-- Rule 900: a failing or quarter-budget job's summary reports its memory peak. -/
def jobReportsPeak : Rule where
  number := 900
  keyword := .must
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom jobSummaryOmitsPeak)

/-- Rule 901: the rented-machine skill loaded before anything on a rented machine. -/
def rentedSkillFirst : Rule where
  number := 901
  keyword := .must
  domain := .softwareEngineering
  formula := ev anyCall ∧ₗ atom actsOnRentedMachine ⟹ once (ev loadsRentedSkill)

/-- Rule 902: a Pod or a Serverless batch by the run's shape, a batch's rate quoted from a read,
unless a reason is given. -/
def podOrServerless : Rule where
  number := 902
  keyword := .should
  domain := .softwareEngineering
  formula := (ev anyCall ∧ₗ atom wrongRentalForm ⟹ atom justified) ∧ₗ
    (ev reply ∧ₗ atom quotesServerlessRate ⟹ once (ev resultEvent ∧ₗ link readsRate) ∨ₗ atom justified)

/-- Rule 903: a Pod created with 70022/tcp and then mounted. -/
def podPortAndMount : Rule where
  number := 903
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev createsPod ∧ₗ atom podLacksSshPort) ∧ₗ (ev createsPod ⟹ eventually (ev podMount))

/-- Rule 904: a rented machine's GPUs and CPUs kept busy. -/
def rentedFullyBusy : Rule where
  number := 904
  keyword := .must
  domain := .softwareEngineering
  formula := never (atom rentedMachineUnderused)

/-- Rule 905: idle CPUs with nothing queued get a useful job or the statement none exists; no
make-work. -/
def answerIdleCapacity : Rule where
  number := 905
  keyword := .must
  domain := .softwareEngineering
  formula := (atom idleWithNothingQueued ⟹ eventually ((ev podAdd ∨ₗ ev reply) ∧ₗ link answersIdleCapacity)) ∧ₗ
    never (ev podAdd ∧ₗ atom makeWork)

/-- Rule 906: jobs start as the machine comes up, GPU work held only for what it needs. -/
def startJobsEarly : Rule where
  number := 906
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev podAdd ∧ₗ atom holdsJobNeedlessly)

/-- Rule 907: the call after a failed job's report reads it. -/
def readFailedJobs : Rule where
  number := 907
  keyword := .must
  domain := .softwareEngineering
  formula := ev anyCall ∧ₗ ¬ₗ atom readsFailedJob ⟹
    ¬ₗ since (ev resultEvent ∧ₗ atom reportsJobFailure) (ev anyCall)

/-- Rule 908: the agent decides what runs on the machine; a refusal keeping it idle gets one ask
for a standing grant. -/
def runAsIfAway : Rule where
  number := 908
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev reply ∧ₗ atom asksWhatRunsOnRented) ∧ₗ
    (ev refusalEvent ∧ₗ atom refusalBlocksRentedWork ⟹ eventually (ev reply ∧ₗ link asksStandingGrant))

/-- Rule 909: a job measuring nothing is stopped the moment that is known: the call after the
result showing it is a stop. -/
def stopUselessJobs : Rule where
  number := 909
  keyword := .must
  domain := .softwareEngineering
  formula := (ev resultEvent ∧ₗ atom showsJobMeasuresNothing ⟹ eventually (ev stopRun ∧ₗ link stopsThatRun)) ∧ₗ
    (ev anyCall ∧ₗ ¬ₗ ev stopRun ⟹ ¬ₗ since (ev resultEvent ∧ₗ atom showsJobMeasuresNothing) (ev anyCall))

/-- Rule 910: a watcher's filter keeps JOB QUIET, and a quiet job is looked into. -/
def keepQuietWord : Rule where
  number := 910
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev watchFilterDropsQuiet) ∧ₗ
    (ev resultEvent ∧ₗ atom reportsQuietJob ⟹ eventually (ev anyCall ∧ₗ link inspectsQuietJob))

/-- Rule 911: a monitor on pod watch armed as soon as a machine is in use, and re-armed at each
expiry: the next call is the arming. -/
def armPodWatch : Rule where
  number := 911
  keyword := .must
  domain := .softwareEngineering
  formula := (ev anyCall ∧ₗ atom startsUsingRented ⟹ eventually (ev armsPodWatch)) ∧ₗ
    (ev resultEvent ∧ₗ atom monitorExpired ⟹ eventually (ev armsPodWatch)) ∧ₗ
    (ev anyCall ∧ₗ ¬ₗ ev armsPodWatch ⟹
      ¬ₗ since ((ev anyCall ∧ₗ atom startsUsingRented) ∨ₗ (ev resultEvent ∧ₗ atom monitorExpired))
        (ev armsPodWatch))

/-- Rule 912: a free slot gets the next job; no turn ends with work left beside the runs. -/
def fillFreeSlots : Rule where
  number := 912
  keyword := .must
  domain := .softwareEngineering
  formula := (ev resultEvent ∧ₗ atom reportsFreeSlot ⟹ eventually (ev podAdd)) ∧ₗ
    never (ev reply ∧ₗ atom endsTurnWithWorkLeft)

/-- Rule 913: a queued job's command holds no pipe, redirect or glob. -/
def podAddNoShell : Rule where
  number := 913
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev podAddWithShell)

/-- Rule 914: next jobs queued as soon as thought of, unless a reason is given. -/
def queueEarly : Rule where
  number := 914
  keyword := .should
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom thinksOfNextJob ⟹ eventually (ev podQueueChange) ∨ₗ atom justified

/-- Rule 915: no wait on queue.lock. -/
def noQueueLockWait : Rule where
  number := 915
  keyword := .mustNot
  domain := .softwareEngineering
  formula := never (ev mentionsQueueLock ∧ₗ atom waitsOnLock)

/-- Rule 916: a queue change is written to pod_jobs.txt. -/
def recordQueue : Rule where
  number := 916
  keyword := .must
  domain := .softwareEngineering
  formula := ev podQueueChange ⟹ eventually (ev editsPodJobs)

/-- Rule 917: after a restart, watchers re-armed and the data checked. -/
def rearmAfterRestart : Rule where
  number := 917
  keyword := .must
  domain := .softwareEngineering
  formula := atom afterRestart ⟹ eventually (ev armsPodWatch) ∧ₗ eventually (ev anyCall ∧ₗ link checksRentedData)

/-- Rule 918: a changed machine address updated in the MCP entries. -/
def updateMcpEntries : Rule where
  number := 918
  keyword := .must
  domain := .softwareEngineering
  formula := ev resultEvent ∧ₗ atom rentedAddressChanged ⟹ eventually (ev editsMcpConfig)

/-- Rule 919: a failing RunPod sign-in restored. -/
def keepSignIn : Rule where
  number := 919
  keyword := .must
  domain := .softwareEngineering
  formula := ev resultEvent ∧ₗ atom signInExpired ⟹ eventually (ev anyCall ∧ₗ link restoresSignIn)

/-- Rule 920: venvs, checkpoints and results on /workspace. -/
def keepOnWorkspace : Rule where
  number := 920
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev anyCall ∧ₗ atom usesContainerDisk)

/-- Rule 921: data read hard copied to /dev/shm, unless a reason is given. -/
def copyToShm : Rule where
  number := 921
  keyword := .should
  domain := .softwareEngineering
  formula := ev anyCall ∧ₗ atom readsHardFromDisk ⟹ atom justified

/-- Rule 922: rsync to /workspace with -rlpt, never -a. -/
def rsyncFlags : Rule where
  number := 922
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev rsyncWorkspaceWrongFlags)

/-- Rule 923: a read called cold only beside a faster warm repeat. -/
def coldReadEvidence : Rule where
  number := 923
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev reply ∧ₗ atom callsReadColdUnchecked)

/-- Rule 924: several aria2c processes rather than many connections, unless a reason is given. -/
def aria2Processes : Rule where
  number := 924
  keyword := .should
  domain := .softwareEngineering
  formula := ev aria2ManyConnections ⟹ atom justified

/-- Rule 925: ideas originated, and the ones listed developed. -/
def originateIdeas : Rule where
  number := 925
  keyword := .must
  domain := .mathematics
  formula := never (ev reply ∧ₗ atom waitsForUserIdeas) ∧ₗ
    (ev reply ∧ₗ atom listsOwnIdea ⟹ eventually (ev reply ∧ₗ link developsListedIdea))

/-- Rule 927: a pattern change in REPORT.md carried to both skills in the same step (before the next
commit, the skills' own commit first), committed in the submodule, and the bumped pointer committed
after it. -/
def skillsFollowReport : Rule where
  number := 927
  keyword := .must
  domain := .discipline
  formula := (ev editsReport ∧ₗ atom changesPattern ⟹
      eventually (ev editsMainSkill) ∧ₗ eventually (ev editsPersonalSkill) ∧ₗ
        eventually (ev skillSubmoduleCommit)) ∧ₗ
    (ev commit ⟹ ¬ₗ since (ev editsReport ∧ₗ atom changesPattern) (ev editsMainSkill) ∧ₗ
      ¬ₗ since (ev editsReport ∧ₗ atom changesPattern) (ev editsPersonalSkill)) ∧ₗ
    (ev commit ∧ₗ ¬ₗ ev skillSubmoduleCommit ⟹
      ¬ₗ since (ev editsReport ∧ₗ atom changesPattern) (ev skillSubmoduleCommit)) ∧ₗ
    (ev skillSubmoduleCommit ⟹ eventually (ev commit ∧ₗ ¬ₗ ev skillSubmoduleCommit))

/-- Rule 928: changes moved between commits under the move-changes-between-commits skill. -/
def moveSkill : Rule where
  number := 928
  keyword := .must
  domain := .discipline
  formula := ev anyCall ∧ₗ atom movesChanges ⟹ once (ev loadsMoveSkill)

/-- Rule 929: pure logic in Lean, proved; impure logic in Lean where it runs. -/
def logicInLean : Rule where
  number := 929
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom pureLogicOutsideLean)

/-- Rule 930: another language only where demanded, kept thin, unless a reason is given. -/
def otherLanguagesThin : Rule where
  number := 930
  keyword := .should
  domain := .discipline
  formula := ev editing ∧ₗ atom nonLeanUndemanded ⟹ atom justified

/-- Rule 931: the reply to a `^` names the habit, and nothing is built before it. -/
def caretAnswer : Rule where
  number := 931
  keyword := .must
  domain := .discipline
  formula := (ev reply ∧ₗ ¬ₗ atom namesHabitBehindMistake ⟹ ¬ₗ since (ev caretMessage) (ev reply)) ∧ₗ
    (ev editing ⟹ ¬ₗ since (ev caretMessage) (ev reply ∧ₗ atom namesHabitBehindMistake))

/-- Rule 932: a recognised own mistake gets the habit-naming answer unprompted. -/
def habitUnprompted : Rule where
  number := 932
  keyword := .must
  domain := .discipline
  formula := never (ev reply ∧ₗ atom mistakeWithoutHabit)

/-- Rule 933: the site's cookie names read before the copy, else every cookie taken. -/
def cookieNamesFirst : Rule where
  number := 933
  keyword := .must
  domain := .softwareEngineering
  formula := ev cookieCopy ⟹ once (ev reading ∧ₗ link readsSiteCookieCode) ∨ₗ atom takesAllHostCookies

/-- Rule 934: reads through firefox_get.py, a header script only for what it can't do, unless a
reason is given. -/
def firefoxGetForReads : Rule where
  number := 934
  keyword := .should
  domain := .softwareEngineering
  formula := ev editing ∧ₗ atom cookieHeaderForReadable ⟹ atom justified

/-- Rule 935: the level of description fixed, observation apart from representation. -/
def fixLevelOfDescription : Rule where
  number := 935
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom descriptionLevelUnfixed)

/-- Rule 936: cheap exhaustive checks before deep ones, coarse failures checked for feasibility,
unless a reason is given. -/
def cheapChecksFirst : Rule where
  number := 936
  keyword := .should
  domain := .discipline
  formula := (ev computeRun ∧ₗ atom deepCheck ⟹ once (ev computeRun ∧ₗ link cheapExhaustiveFirst) ∨ₗ atom justified) ∧ₗ
    (ev reply ∧ₗ atom acceptsCoarseFailure ⟹ atom justified)

/-- Rule 937: a design changed until what must hold is easy to say, unless a reason is given. -/
def easyToStateDesign : Rule where
  number := 937
  keyword := .should
  domain := .discipline
  formula := ev editing ∧ₗ atom keepsHardToStateDesign ⟹ atom justified

/-- Rule 938: work for a merge request committed on a branch created for it. -/
def branchForMr : Rule where
  number := 938
  keyword := .must
  domain := .discipline
  formula := ev commit ∧ₗ atom mrWork ⟹ once (ev createsBranch)

/-- Rule 939: our own project on main when the user directs it, unless a reason is given. -/
def mainWhenDirected : Rule where
  number := 939
  keyword := .should
  domain := .discipline
  formula := ev anyCall ∧ₗ atom sideBranchAgainstDirection ⟹ atom justified

/-- Rule 940: read-only commands run, not relayed, unless a reason is given. -/
def runReadOnlyYourself : Rule where
  number := 940
  keyword := .should
  domain := .discipline
  formula := ev reply ∧ₗ atom relaysReadOnlyCommand ⟹ atom justified

/-- Rule 941: an offer of read access taken, unless a reason is given. -/
def takeAccessOffers : Rule where
  number := 941
  keyword := .should
  domain := .discipline
  formula := ev reply ∧ₗ atom declinesAccessOffer ⟹ atom justified

/-- Rule 942: a recurring symptom checked against what was root-caused, unless a reason is given. -/
def matchRootCaused : Rule where
  number := 942
  keyword := .should
  domain := .discipline
  formula := ev reply ∧ₗ atom rediagnosesSymptom ⟹ once (ev anyCall ∧ₗ link searchesRootCaused) ∨ₗ atom justified

/-- Rule 943: a search for what does the job before building, named in the deciding sentence. -/
def searchBeforeBuilding : Rule where
  number := 943
  keyword := .must
  domain := .discipline
  formula := (ev editing ∧ₗ atom buildsNewTool ⟹ once (ev anyCall ∧ₗ link searchesForExistingJob)) ∧ₗ
    never (ev reply ∧ₗ atom buildDecisionOmitsSearch)

/-- Rule 944: a bug reported with a precise repro. -/
def preciseRepro : Rule where
  number := 944
  keyword := .must
  domain := .discipline
  formula := never (ev reply ∧ₗ atom bugReportWithoutRepro)

/-- Rule 945: a delegation's brief front-loads identifiers and the deliverable, unless a reason is
given. -/
def frontLoadBrief : Rule where
  number := 945
  keyword := .should
  domain := .discipline
  formula := ev delegates ∧ₗ atom briefLacksIdentifiers ⟹ atom justified

/-- Rule 946: each request part checked against its target before building; nothing built for a
purposeless part, and the reply says what the target does instead. -/
def checkPartsAgainstTarget : Rule where
  number := 946
  keyword := .must
  domain := .discipline
  formula := (ev editing ∧ₗ atom buildsRequestPart ⟹ once (ev anyCall ∧ₗ link checksPartAgainstTarget)) ∧ₗ
    never (ev editing ∧ₗ atom buildsPurposelessPart) ∧ₗ never (ev reply ∧ₗ atom skipsPartSilently)

/-- Rule 947: unfamiliar mechanisms and jargon explained. -/
def explainJargon : Rule where
  number := 947
  keyword := .must
  domain := .discipline
  formula := never (ev reply ∧ₗ atom unexplainedJargon)

/-- Rule 948: asked what a design choice gains, the agent says. -/
def stateChoiceGains : Rule where
  number := 948
  keyword := .must
  domain := .discipline
  formula := ev user ∧ₗ atom asksWhatChoiceGains ⟹ eventually (ev reply ∧ₗ link statesGain)

/-- Rule 949: second-order consequences surfaced unasked. -/
def surfaceConsequences : Rule where
  number := 949
  keyword := .must
  domain := .discipline
  formula := never (ev reply ∧ₗ atom hidesSecondOrderEffects)

/-- Rule 950: each design part costed; a per-call path reads a result kept current elsewhere. -/
def costDesignParts : Rule where
  number := 950
  keyword := .must
  domain := .discipline
  formula := never (ev reply ∧ₗ atom designPartUncosted) ∧ₗ never (ev editing ∧ₗ atom perCallRecomputes)

/-- Rule 951: one design item at a time. -/
def oneItemAtATime : Rule where
  number := 951
  keyword := .must
  domain := .discipline
  formula := never (ev reply ∧ₗ atom movesOnWithItemOpen)

/-- Rule 952: an approved plan executed without asking per step. -/
def executeApprovedPlan : Rule where
  number := 952
  keyword := .must
  domain := .discipline
  formula := never (ev reply ∧ₗ atom asksPerStepOnApprovedPlan)

/-- Rule 953: product copy written for the end user. -/
def endUserCopy : Rule where
  number := 953
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom userTextUnhelpful)

/-- Rule 954: answering the latest message completes no artifact. -/
def answerIsNoCompletion : Rule where
  number := 954
  keyword := .mustNot
  domain := .discipline
  formula := never (ev reply ∧ₗ atom treatsAnswerAsCompletion)

/-- Rule 955: a run doing the wrong thing, or superseded, is stopped. -/
def stopWrongRuns : Rule where
  number := 955
  keyword := .must
  domain := .discipline
  formula := ev resultEvent ∧ₗ atom showsRunWrong ⟹ eventually (ev stopRun ∧ₗ link stopsThatRun)

/-- Rule 956: a handed-over artifact answers its reviewer's first questions from measurement. -/
def answerReviewerQuestions : Rule where
  number := 956
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom handsOverArtifact ⟹
    atom answersReviewerQuestions ∧ₗ once (ev resultEvent ∧ₗ link measuresArtifact)

/-- Rule 957: an artifact of a defined kind made from the rule that defines it. -/
def artifactFromRule : Rule where
  number := 957
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom makesRuleDefinedArtifact ⟹ once (ev reading ∧ₗ link readsDefiningRule)

/-- Rule 958: a prose-only rule given a generator or check, unless a reason is given. -/
def rulesGetChecks : Rule where
  number := 958
  keyword := .should
  domain := .discipline
  formula := ev editing ∧ₗ atom proseRuleWithoutCheck ⟹ atom justified

/-- Rule 959: the turn acts on the user's whole next state. -/
def actOnWholeState : Rule where
  number := 959
  keyword := .must
  domain := .discipline
  formula := never (ev reply ∧ₗ atom ignoresUsersNextState)

/-- Rule 960: durable knowledge summarized first, written when separately asked. -/
def twoStepDurableWrites : Rule where
  number := 960
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom writesDurableKnowledge ⟹
    once (ev reply ∧ₗ link summarizesLearned) ∧ₗ once (ev user ∧ₗ link asksToPersist)

/-- Rule 961: committed docs describe the current state. -/
def currentStateDocs : Rule where
  number := 961
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom describesPastState)

/-- Rule 962: the interface contract drafted before its implementation. -/
def contractFirst : Rule where
  number := 962
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom implementsInterface ⟹ once (ev editing ∧ₗ link draftsContract)

/-- Rule 963: no historical narration in committed docs. -/
def noHistoricalNarration : Rule where
  number := 963
  keyword := .mustNot
  domain := .discipline
  formula := never (ev editing ∧ₗ atom historicalNarration)

/-- Rule 964: no commit hash in a lasting record, nor hashes or untimed counts in drafts under
`tasks/` or `research/`. -/
def noHashesInRecords : Rule where
  number := 964
  keyword := .mustNot
  domain := .discipline
  formula := never (ev editing ∧ₗ atom recordsCommitHash) ∧ₗ
    never (ev editsTasksOrResearch ∧ₗ atom hashOrUntimedCount)

/-- Rule 965: every reference resolvable. -/
def resolvableReferences : Rule where
  number := 965
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom unresolvableReference)

/-- Rule 966: a correction becomes a standing rule, never project memory. -/
def correctionsBecomeRules : Rule where
  number := 966
  keyword := .must
  domain := .discipline
  formula := (ev user ∧ₗ atom correctsAgentOrStatesPreference ⟹ eventually (ev editing ∧ₗ link writesStandingRule)) ∧ₗ
    never (ev memoryWrite)

/-- Rule 967: the owning rule found before a rule is added; a rule added only for what nothing
covers. -/
def extendOwningRule : Rule where
  number := 967
  keyword := .must
  domain := .discipline
  formula := (ev editing ∧ₗ atom addsRule ⟹ once (ev reading ∧ₗ link readsOwningRule)) ∧ₗ
    never (ev editing ∧ₗ atom addsCoveredRule)

/-- Rule 968: one authoritative, travelling copy of each rule. -/
def oneCopyOfRules : Rule where
  number := 968
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom duplicatesRule)

/-- Rule 969: a correction of the work answered about how it was made, sound work left standing. -/
def answerHowWorkWasMade : Rule where
  number := 969
  keyword := .must
  domain := .discipline
  formula := (ev user ∧ₗ atom correctsAnalysis ⟹ eventually (ev reply ∧ₗ link answersHowMade)) ∧ₗ
    never (ev editing ∧ₗ atom undoesSoundWork)

/-- Rule 970: an idea recorded in its durable home as soon as it comes up: the recording edit is the
first edit after the reply raising it. -/
def recordIdeas : Rule where
  number := 970
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom raisesIdea ⟹
    eventually (ev editing ∧ₗ link recordsIdea ∧ₗ since (ev reply ∧ₗ atom raisesIdea) (ev editing))

/-- Rule 971: prose compressed without losing substance. -/
def compressProse : Rule where
  number := 971
  keyword := .must
  domain := .discipline
  formula := never ((ev reply ∨ₗ ev editing) ∧ₗ atom padsOrLosesProse)

/-- Rule 972: each sentence for its reader's next action. -/
def sentencesForAction : Rule where
  number := 972
  keyword := .must
  domain := .discipline
  formula := never ((ev reply ∨ₗ ev editing) ∧ₗ atom sentenceNotForNextAction)

/-- Rule 973: a description states what holds at the tip. -/
def descriptionAtTip : Rule where
  number := 973
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom descriptionNarratesCheck)

/-- Rule 974: commits along logical lines, each audited against its message first. -/
def logicalCommits : Rule where
  number := 974
  keyword := .must
  domain := .discipline
  formula := never (ev commit ∧ₗ atom commitMixesConcerns) ∧ₗ
    (ev commit ⟹ once (ev anyCall ∧ₗ link auditsCommitBothWays))

/-- Rule 975: lower-layer code in its own commit, never riding in one that doesn't use it. -/
def lowerLayerOwnCommit : Rule where
  number := 975
  keyword := .must
  domain := .discipline
  formula := never (ev commit ∧ₗ atom lowerLayerRidesUnused)

/-- Rule 976: a merge request's history folded with autosquash before its review. -/
def foldHistoryForReview : Rule where
  number := 976
  keyword := .must
  domain := .discipline
  formula := (ev publish ∧ₗ atom opensMrReview ⟹ once (ev autosquashRebase)) ∧ₗ
    never (ev publish ∧ₗ atom mrHistoryUnfolded)

/-- Rule 977: work outside a merge request appends its fixes, unless a reason is given. -/
def appendFixes : Rule where
  number := 977
  keyword := .should
  domain := .discipline
  formula := ev historyRewrite ∧ₗ atom rewritesNonMrHistory ⟹ atom justified

/-- Rule 978: a document sent stays as sent. -/
def sentStaysSent : Rule where
  number := 978
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom changesSentDocument)

/-- Rule 979: pushed history with small damage left alone, unless a reason is given. -/
def leavePushedHistory : Rule where
  number := 979
  keyword := .should
  domain := .discipline
  formula := ev forcePush ∧ₗ atom smallDamageOnly ⟹ atom justified

/-- Rule 980: no per-deployment literal accepted in a design. -/
def deploymentAgnostic : Rule where
  number := 980
  keyword := .must
  domain := .discipline
  formula := never ((ev reply ∨ₗ ev editing) ∧ₗ atom deploymentSpecificDesign)

def rules : List Rule :=
  [worktreeDiscipline, heavyLoopsCompiled, linearAlgebraLibraries, algebraThroughLauncher,
   heavyLoopsInC, vectorizeAndChunk, incrementalComputation, seriesInOnePass, stagesBeforeLaunch,
   slowCallsForKernel, kernelReason, seriesInOneInvocation, noTripleLoops, threadBudget,
   prefixedAlgebraNames, pariSettings, runAllowance, noLongForeground, longRunFlags,
   halfHourNeedsApproval, enumerationSized, estimateFromMeasurement, reductionsBeforeLongRun,
   stopSupersededRuns, smallestInformativeSize, waitsOnEvents, trainingBySlope,
   speedMeasurementPurpose, publishedBaseline, profileTheGap, timeTheMeasure,
   backgroundWhileWaiting, remoteUnderTimeout, monitorNext, remoteWatcher, workBesideRuns,
   fiveMinuteDecision, sizeBeforeScaling, observableRuns, zstdResults, jpegImages, packBeforeCommit,
   scriptsTakeOut, saveRunsWithoutOut, referenceOutputs, distinctRunPaths, structuredStreamed,
   provenanceManifest, exportAndArchive, noInventedTiming, commitCanonicalReport,
   exclusiveIntervals, discloseMixedTime, phaseBeforeDrafting, markerApartFromCode,
   phaseAfterSources, leanInCategory, honestModelLabel, jobReportsPeak, rentedSkillFirst,
   podOrServerless, podPortAndMount, rentedFullyBusy, answerIdleCapacity, startJobsEarly,
   readFailedJobs, runAsIfAway, stopUselessJobs, keepQuietWord, armPodWatch, fillFreeSlots,
   podAddNoShell, queueEarly, noQueueLockWait, recordQueue, rearmAfterRestart, updateMcpEntries,
   keepSignIn, keepOnWorkspace, copyToShm, rsyncFlags, coldReadEvidence, aria2Processes,
   originateIdeas, skillsFollowReport, moveSkill, logicInLean, otherLanguagesThin, caretAnswer,
   habitUnprompted, cookieNamesFirst, firefoxGetForReads, fixLevelOfDescription, cheapChecksFirst,
   easyToStateDesign, branchForMr, mainWhenDirected, runReadOnlyYourself, takeAccessOffers,
   matchRootCaused, searchBeforeBuilding, preciseRepro, frontLoadBrief, checkPartsAgainstTarget,
   explainJargon, stateChoiceGains, surfaceConsequences, costDesignParts, oneItemAtATime,
   executeApprovedPlan, endUserCopy, answerIsNoCompletion, stopWrongRuns, answerReviewerQuestions,
   artifactFromRule, rulesGetChecks, actOnWholeState, twoStepDurableWrites, currentStateDocs,
   contractFirst, noHistoricalNarration, noHashesInRecords, resolvableReferences,
   correctionsBecomeRules, extendOwningRule, oneCopyOfRules, answerHowWorkWasMade, recordIdeas,
   compressProse, sentencesForAction, descriptionAtTip, logicalCommits, lowerLayerOwnCommit,
   foldHistoryForReview, appendFixes, sentStaysSent, leavePushedHistory, deploymentAgnostic]

/-- The range holds no MAY rule. -/
def permissions : List Nat := []

/-- The range's numbers, the sample's 844 and 926 left out, each in `rules` once. -/
theorem range_covered :
    (rules.map (·.number)) = (List.range' 841 140).filter (fun n => n != 844 && n != 926) := by
  decide

end Rails.Ruleset.Range7
