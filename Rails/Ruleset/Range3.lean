import Rails.Rules
import Rails.Examples
import Rails.Witness

/-!
Rules 281 to 420 of `tasks/agents-on-rails/RULES.md`, the sample's 341, 383 and 420 left out: review
rounds and their records, property tests, the branch checks, evidence ledgers, guards and fixes,
claims and sources, history rewrites, and the computation controls. Every rule of the range is a
MUST or MUST NOT, so the range has no permission theorem.
-/

namespace Rails.Ruleset.Range3
open Rails Formula Ruleset Rules Examples

/-! Helpers over a command's words. -/

private def word (s : String) (ws : List (List Char)) : Bool := ws.contains s.toList

/-- Some word holds `s` as a contiguous part. -/
private def wordHas (s : String) (ws : List (List Char)) : Bool := ws.any (occursIn s.toList)

/-- A program word is `prog` or a path ending `/prog`. -/
private def isProg (prog : String) (w : List Char) : Bool :=
  w == prog.toList || endsWith ("/" ++ prog).toList w

/-- Some command of the call runs exactly the program `prog`, with `p` holding of its words. -/
private def runsProg (prog : String) (p : List (List Char) → Bool) (e : Event) : Bool :=
  (programs e).any fun (w, ws) => isProg prog w && p ws

private def git (p : List (List Char) → Bool) : Event → Bool := runsProg "git" p

/-- The call's shell text holds `s`. -/
private def commandHas (s : String) (e : Event) : Bool :=
  match command e with
  | some c => occursIn s.toList c.toList
  | none => false

/-- An edit whose new text (Edit's `new_string`, Write's `content`, a patch's `input`) holds `s`. -/
private def editText (s : String) (e : Event) : Bool :=
  isEdit e && ["new_string", "content", "input"].any fun k =>
    match e.field k with
    | some v => occursIn s.toList v.toList
    | none => false

private def writesPathEnding (suffix : String) (e : Event) : Bool :=
  match writePath e with
  | some p => endsWith suffix.toList p.toList
  | none => false

private def readsPathEnding (suffix : String) (e : Event) : Bool :=
  match readPath e with
  | some p => endsWith suffix.toList p.toList
  | none => false

/-- A shell word `bash` or `sh` directly before a word running `compute.sh`. -/
private def shellBeforeCompute : List (List Char) → Bool
  | a :: b :: rest =>
    ((a == "bash".toList || a == "sh".toList) && isProg "compute.sh" b) || shellBeforeCompute (b :: rest)
  | _ => false

/-- A command running `compute.sh` with an assignment before it that sets no thread count. -/
private def envBeforeCompute (ws : List (List Char)) : Bool :=
  ws.any (isProg "compute.sh") &&
    (ws.takeWhile (!isProg "compute.sh" ·)).any fun w => w.contains '=' && !occursIn "THREADS".toList w

private def isController (w : List Char) (ws : List (List Char)) : Bool :=
  (isProg "compute.sh" w && (word "start" ws || word "run" ws)) || isProg "finish-turn.py" w ||
    isProg "resume.py" w

/-- A controller's command run with a filter or `cd` beside it, or with a redirect. -/
private def isFilteredController (e : Event) : Bool :=
  let ps := programs e
  ps.any (fun (w, ws) => isController w ws) &&
    (ps.any (fun (w, _) => ["head", "tail", "grep", "cd"].any (isProg · w)) ||
      ps.any (fun (_, ws) => ws.any (·.contains '>')))

private def installsPackages (dryRun : Bool) (e : Event) : Bool :=
  (programs e).any fun (w, ws) =>
    ((isProg "pip" w || isProg "pip3" w || isProg "uv" w || word "pip" ws) && word "install" ws &&
      word "--dry-run" ws == dryRun) ||
    (!dryRun && (isProg "npm" w || isProg "pnpm" w || isProg "yarn" w) &&
      (word "install" ws || word "add" ws))

private def isBranchDelete (e : Event) : Bool :=
  git (fun ws => word "branch" ws && (word "-D" ws || word "-d" ws || word "--delete" ws)) e

/-! Event predicates. -/

def anyCall : Pred := ⟨"anyCall", isCall, [bash "ls"]⟩
def toolResult : Pred := ⟨"toolResult", isResult, [.result "c" "out"]⟩
def agentRun : Pred := ⟨"agentRun", isTool "Agent", [.call "a" "Agent" [("prompt", "review")], reviewer]⟩
def resumesAgent : Pred := ⟨"resumesAgent", isTool "SendMessage", [.call "m" "SendMessage" [("to", "a")]]⟩
def loadsPropertyTesting : Pred := ⟨"loadsPropertyTesting",
  fun e => isTool "Skill" e && e.field "skill" == some "property-testing",
  [.call "s" "Skill" [("skill", "property-testing")]]⟩
def loadsMrReview : Pred := ⟨"loadsMrReview",
  fun e => isTool "Skill" e && e.field "skill" == some "mr-review",
  [.call "s" "Skill" [("skill", "mr-review")]]⟩
def loadsKnowledge : Pred := ⟨"loadsKnowledge",
  fun e => isTool "Skill" e || runsProg "resume.py" (fun _ => true) e || readsPathEnding "PLAN.md" e,
  [.call "s" "Skill" [("skill", "engineering-discipline")], bash "python3 tools/resume.py",
   read "tasks/x/PLAN.md"]⟩
def gitCommit : Pred := ⟨"gitCommit", git (word "commit"), [bash "git commit -m x"]⟩
def gitRebase : Pred := ⟨"gitRebase", git (word "rebase"), [bash "git rebase origin/main"]⟩
def gitMerge : Pred := ⟨"gitMerge", git (word "merge"), [bash "git merge --ff-only b"]⟩
def gitStage : Pred := ⟨"gitStage", git (word "add"), [bash "git add f.py"]⟩
def gitStash : Pred := ⟨"gitStash", git (word "stash"), [bash "git stash push -u"]⟩
def gitTag : Pred := ⟨"gitTag", git (word "tag"), [bash "git tag backup"]⟩
def readsHistory : Pred := ⟨"readsHistory", git (fun ws => word "log" ws || word "show" ws),
  [bash "git log --oneline main..origin/main", bash "git show abc"]⟩
def formatPatch : Pred := ⟨"formatPatch", git (word "format-patch"),
  [bash "git format-patch main..b -o /tmp/p"]⟩
/-- Staging the whole worktree: `git add .`, `-A` or `--all`, or `git commit -a`. -/
def stagesWholeTree : Pred := ⟨"stagesWholeTree",
  git fun ws => (word "add" ws && (word "." ws || word "-A" ws || word "--all" ws)) ||
    (word "commit" ws && (word "-a" ws || word "-am" ws || word "--all" ws)),
  [bash "git add .", bash "git commit -am fix"]⟩
/-- A history rewrite: a rebase, an amend, a hard reset, a filter, a forced push. -/
def rewritesHistory : Pred := ⟨"rewritesHistory",
  git fun ws => word "rebase" ws || (word "commit" ws && word "--amend" ws) ||
    (word "reset" ws && word "--hard" ws) || word "filter-branch" ws || word "filter-repo" ws ||
    (word "push" ws && (word "--force" ws || word "-f" ws || wordHas "--force-with-lease" ws)),
  [bash "git rebase -i main", bash "git commit --amend --no-edit", bash "git push --force origin b"]⟩
/-- A branch created by name: `git branch NAME`, no listing or deletion option. -/
def branchCreate : Pred := ⟨"branchCreate",
  git fun ws => word "branch" ws && ws.length ≥ 3 &&
    !(["-d", "-D", "--delete", "-l", "--list", "-a", "-r", "-v", "-vv", "--show-current", "-m", "-M"].any
      (word · ws)),
  [bash "git branch backup-b"]⟩
def branchDelete : Pred := ⟨"branchDelete", isBranchDelete, [bash "git branch -D old"]⟩
def diffStat : Pred := ⟨"diffStat", git (fun ws => word "diff" ws && word "--stat" ws),
  [bash "git diff --stat backup b"]⟩
def rangeDiff : Pred := ⟨"rangeDiff", git (word "range-diff"), [bash "git range-diff main backup b"]⟩
def logFormat : Pred := ⟨"logFormat",
  git (fun ws => word "log" ws && (wordHas "--format" ws || wordHas "--pretty" ws)),
  [bash "git log --format='%s %an %ad' main..b"]⟩
/-- A deletion: `rm`, a branch deletion, a worktree removal. -/
def deletes : Pred := ⟨"deletes",
  fun e => runsProg "rm" (fun _ => true) e || isBranchDelete e ||
    git (fun ws => word "worktree" ws && word "remove" ws) e,
  [bash "rm -rf out", bash "git branch -D old", bash "git worktree remove ../w"]⟩
def searches : Pred := ⟨"searches",
  fun e => isTool "Grep" e || runsProg "grep" (fun _ => true) e || runsProg "rg" (fun _ => true) e ||
    git (word "grep") e,
  [.call "g" "Grep" [("pattern", "x")], bash "rg -n x", bash "git grep -n x"]⟩
def checksProcesses : Pred := ⟨"checksProcesses",
  fun e => ["ps", "ss", "lsof", "netstat", "pgrep", "fuser"].any (runsProg · (fun _ => true) e),
  [bash "ss -ltnp", bash "ps aux"]⟩
def stopsWork : Pred := ⟨"stopsWork",
  fun e => isTool "TaskStop" e || isTool "KillShell" e || runsProg "kill" (fun _ => true) e ||
    runsProg "pkill" (fun _ => true) e,
  [.call "t" "TaskStop" [("task_id", "b1")], bash "kill 123"]⟩
def installs : Pred := ⟨"installs", installsPackages false, [bash "pip install requests", bash "npm install"]⟩
def dryRunResolve : Pred := ⟨"dryRunResolve", installsPackages true,
  [bash "pip install --dry-run --report r.json torch requests"]⟩
def commitSymbolUse : Pred := ⟨"commitSymbolUse", runsProg "commit_symbol_use.py" (fun _ => true),
  [bash "./tools/commit_symbol_use.py main"]⟩
def handBuiltErrors : Pred := ⟨"handBuiltErrors", runsProg "hand_built_errors.py" (fun _ => true),
  [bash "./tools/hand_built_errors.py main"]⟩
def circularOracle : Pred := ⟨"circularOracle", runsProg "circular_oracle.py" (fun _ => true),
  [bash "python3 tools/circular_oracle.py --base main"]⟩
/-- `--allow` given to hand_built_errors.py or circular_oracle.py. -/
def passesAllow : Pred := ⟨"passesAllow",
  fun e => (runsProg "hand_built_errors.py" (wordHas "--allow") e ||
    runsProg "circular_oracle.py" (wordHas "--allow") e),
  [bash "./tools/hand_built_errors.py main --allow t.py::x"]⟩
def installGitHooks : Pred := ⟨"installGitHooks", runsProg "install-git-hooks.sh" (fun _ => true),
  [bash "./tools/install-git-hooks.sh ~/dev/r"]⟩
def blindCopy : Pred := ⟨"blindCopy", runsProg "blind_copy.py" (fun _ => true),
  [bash "python3 tools/blind_copy.py ~/dev/r tip /tmp/c --base main"]⟩
def timeBoundTests : Pred := ⟨"timeBoundTests", runsProg "time_bound_tests.py" (fun _ => true),
  [bash "python3 tools/time_bound_tests.py main"]⟩
def leadQueueAdd : Pred := ⟨"leadQueueAdd", runsProg "lead_queue.py" (word "add"),
  [bash "python3 tools/lead_queue.py add notebook.html --check x s t"]⟩
/-- Closing a promised item: a queue item, or a request resolved. -/
def closesItem : Pred := ⟨"closesItem",
  fun e => runsProg "lead_queue.py" (word "close") e ||
    runsProg "task_index.py" (fun ws => word "request" ws && word "resolve" ws) e,
  [bash "python3 tools/lead_queue.py close notebook.html x done",
   bash "python3 tools/task_index.py request resolve t 3"]⟩
def taskCheckpoint : Pred := ⟨"taskCheckpoint", runsProg "task_checkpoint.py" (fun _ => true),
  [bash "python3 tools/task_checkpoint.py --entry e.html --message m"]⟩
/-- A checkpoint recording a suite time under a label ending `-own`. -/
def ownTimedCheckpoint : Pred := ⟨"ownTimedCheckpoint", runsProg "task_checkpoint.py" (wordHas "-own="),
  [bash "python3 tools/task_checkpoint.py --suite python3.12-own=40:300 --entry e.html"]⟩
def readerCheck : Pred := ⟨"readerCheck", runsProg "reader_check.py" (fun _ => true),
  [bash "python3 tools/reader_check.py D.md D_EVIDENCE.md"]⟩
def readerCheckAlso : Pred := ⟨"readerCheckAlso", runsProg "reader_check.py" (word "--also"),
  [bash "python3 tools/reader_check.py D.md D_EVIDENCE.md --also prose.md"]⟩
def ledgerAtTip : Pred := ⟨"ledgerAtTip", runsProg "ledger_at_tip.py" (fun _ => true),
  [bash "python3 tools/ledger_at_tip.py L.md ~/dev/r tip"]⟩
def ledgerNew : Pred := ⟨"ledgerNew", runsProg "ledger_new.py" (fun _ => true),
  [bash "python3 tools/ledger_new.py tasks/x/D.md --branch b"]⟩
def branchProse : Pred := ⟨"branchProse", runsProg "branch_prose.py" (fun _ => true),
  [bash "python3 tools/branch_prose.py ~/dev/r main b --out p.md"]⟩
def saveRunOutput : Pred := ⟨"saveRunOutput", runsProg "save-run-output.py" (fun _ => true),
  [bash "python3 tools/save-run-output.py s 3 research/results/x.txt"]⟩
/-- `tools/suite_before_commit.py --run`. -/
def suiteBeforeCommit : Pred := ⟨"suiteBeforeCommit", runsProg "suite_before_commit.py" (word "--run"),
  [bash "python3 tools/suite_before_commit.py --run"]⟩
/-- A run of the framework's tests: its runner or the pre-commit suite. -/
def frameworkTests : Pred := ⟨"frameworkTests",
  fun e => commandHas "tools/tests/run.py" e || commandHas "suite_before_commit.py" e,
  [bash "./compute.sh python3 tools/tests/run.py test_x"]⟩
def viaComputeSh : Pred := ⟨"viaComputeSh", runsProg "compute.sh" (fun _ => true),
  [bash "./compute.sh python3 calc.py"]⟩
def computeStart : Pred := ⟨"computeStart", runsProg "compute.sh" (word "start"),
  [bash "./compute.sh start turn1"]⟩
/-- A timing command continuing a session: a phase, a run, a report or `--session`. -/
def timingContinues : Pred := ⟨"timingContinues",
  runsProg "compute.sh" fun ws => word "phase" ws || word "run" ws || word "report" ws ||
    word "--session" ws,
  [bash "./compute.sh phase turn1 coding", bash "./compute.sh run turn1 -- python3 x.py"]⟩
def computeStatus : Pred := ⟨"computeStatus", runsProg "compute.sh" (word "--status"),
  [bash "./compute.sh --status"]⟩
def controlsSetup : Pred := ⟨"controlsSetup",
  fun e => (programs e).any fun (w, _) => endsWith "resource-controls/setup.py".toList w,
  [bash "python3 resource-controls/setup.py"]⟩
def stressTest : Pred := ⟨"stressTest",
  fun e => commandHas "test_watchdog.py" e || commandHas "test_over_budget.py" e,
  [bash "./compute.sh python3 resource-controls/test_watchdog.py"]⟩
/-- A command running a script kept under `research/`. -/
def runsResearchScript : Pred := ⟨"runsResearchScript",
  fun e => (programs e).any fun (_, ws) => ws.any fun w =>
    occursIn "research/".toList w && (endsWith ".py".toList w || endsWith ".sh".toList w),
  [bash "./compute.sh python3 research/tools/calc.py"]⟩
/-- `compute.sh` run through `bash` or `sh`. -/
def computeViaShell : Pred := ⟨"computeViaShell",
  fun e => match command e with
    | some c => (shellCommands c.toList).any shellBeforeCompute
    | none => false,
  [bash "bash ./compute.sh python3 x.py"]⟩
/-- A non-thread environment assignment before `compute.sh`, which the launcher drops. -/
def envPrefixToCompute : Pred := ⟨"envPrefixToCompute",
  fun e => match command e with
    | some c => (shellCommands c.toList).any envBeforeCompute
    | none => false,
  [bash "FOO=1 ./compute.sh python3 x.py"]⟩
/-- A controller (`compute.sh start` or `run`, `finish-turn.py`, `resume.py`) with a filter, `cd` or
a redirect beside it. -/
def controllerFiltered : Pred := ⟨"controllerFiltered", isFilteredController,
  [bash "./compute.sh start t1 | tail -5", bash "cd /r && python3 tools/resume.py",
   bash "./tools/finish-turn.py t1 > log"]⟩
def pkillPattern : Pred := ⟨"pkillPattern",
  fun e => runsProg "pkill" (word "-f") e || runsProg "pgrep" (word "-f") e,
  [bash "pkill -f server.py", bash "pgrep -f lake"]⟩
def marksGoalAdvanced : Pred := ⟨"marksGoalAdvanced", editText "data-goal-progress=\"advanced\"",
  [.call "e" "Edit" [("file_path", "notebook.html"), ("new_string", "<article data-goal-progress=\"advanced\">")]]⟩
def closesFollowUp : Pred := ⟨"closesFollowUp", editText "Follow-up.</strong> Closed",
  [.call "e" "Edit" [("file_path", "notebook.html"), ("new_string", "<strong>Follow-up.</strong> Closed: x")]]⟩
def editsFormalization : Pred := ⟨"editsFormalization",
  fun e => match writePath e with
    | some p => occursIn "formalization/".toList p.toList
    | none => false,
  [edit "formalization/Main.lean"]⟩
def readsFormalizationAgents : Pred := ⟨"readsFormalizationAgents",
  readsPathEnding "formalization/AGENTS.md", [read "formalization/AGENTS.md"]⟩
def readsFormalizationReadme : Pred := ⟨"readsFormalizationReadme",
  readsPathEnding "formalization/README.md", [read "formalization/README.md"]⟩
def readsComputationRules : Pred := ⟨"readsComputationRules",
  readsPathEnding "COMPUTATION_RULES.md", [read "COMPUTATION_RULES.md"]⟩
def editsLedger : Pred := ⟨"editsLedger", writesPathEnding "_EVIDENCE.md",
  [edit "tasks/x/D_EVIDENCE.md"]⟩
def editsReviewFile : Pred := ⟨"editsReviewFile",
  fun e => match writePath e with
    | some p => occursIn "REVIEW".toList p.toList && endsWith ".md".toList p.toList
    | none => false,
  [edit "tasks/x/MR_REVIEW.md"]⟩

/-- A ledger edit and an edit of the document it is the ledger of (`D_EVIDENCE.md` beside `D.md`). -/
private def ledgerAndDocument (a b : Step) : Bool :=
  match writePath a.event, writePath b.event with
  | some l, some d =>
    endsWith ".md".toList d.toList &&
      l.toList == d.toList.take (d.length - 3) ++ "_EVIDENCE.md".toList
  | _, _ => false

def ledgerWithItsDocument : Rel := ⟨"ledgerWithItsDocument", ledgerAndDocument,
  [(edit "tasks/x/D_EVIDENCE.md", edit "tasks/x/D.md")]⟩

wellFormedPreds preds
  [anyCall, toolResult, agentRun, resumesAgent, loadsPropertyTesting, loadsMrReview, loadsKnowledge,
   gitCommit, gitRebase, gitMerge, gitStage, gitStash, gitTag, readsHistory, formatPatch,
   stagesWholeTree, rewritesHistory, branchCreate, branchDelete, diffStat, rangeDiff, logFormat,
   deletes, searches, checksProcesses, stopsWork, installs, dryRunResolve, commitSymbolUse,
   handBuiltErrors, circularOracle, passesAllow, installGitHooks, blindCopy, timeBoundTests,
   leadQueueAdd, closesItem, taskCheckpoint, ownTimedCheckpoint, readerCheck, readerCheckAlso,
   ledgerAtTip, ledgerNew, branchProse, saveRunOutput, suiteBeforeCommit, frameworkTests,
   viaComputeSh, computeStart, timingContinues, computeStatus, controlsSetup, stressTest,
   runsResearchScript, computeViaShell, envPrefixToCompute, controllerFiltered, pkillPattern,
   marksGoalAdvanced, closesFollowUp, editsFormalization, readsFormalizationAgents,
   readsFormalizationReadme, readsComputationRules, editsLedger, editsReviewFile]

def rels : List Rel := [ledgerWithItsDocument]
theorem rels_wellFormed : rels.all Rel.wellFormed = true := by decide

/-! Atoms: questions about one event. -/

def mergesFindings : Atom := ⟨"mergesFindings",
  "Does this edit merge or reconcile review findings?", .edit⟩
def recordsChangedDependency : Atom := ⟨"recordsChangedDependency",
  "Does this edit record that an upstream commit a rebase brought in changes a logical dependency of the branch?", .edit⟩
def isOpenReview : Atom := ⟨"isOpenReview",
  "Is this subagent run the open review of a branch or plan (the review given what a colleague on the hosting platform sees)?", .call⟩
def briefHasLedger : Atom := ⟨"briefHasLedger",
  "Does this subagent's brief give it an evidence ledger?", .call⟩
def briefAsksLedgerAudit : Atom := ⟨"briefAsksLedgerAudit",
  "Does this subagent's brief ask it to audit an evidence ledger's rows?", .call⟩
def findsStaleHoldingRow : Atom := ⟨"findsStaleHoldingRow",
  "Does this reply find a ledger row stale while the sentence it supports still holds?", .reply⟩
def recordsStaleRowAsFinding : Atom := ⟨"recordsStaleRowAsFinding",
  "Does this edit record a stale ledger row whose sentence holds as a review finding?", .edit⟩
def acceptsReviewerFinding : Atom := ⟨"acceptsReviewerFinding",
  "Does this reply accept a reviewer's finding as holding?", .reply⟩
def enumerableClassPending : Atom := ⟨"enumerableClassPending",
  "Does this review's brief follow a round naming a finding class that the writer's pass can enumerate?", .call⟩
def candidateTooNoisy : Atom := ⟨"candidateTooNoisy",
  "Does this reply find a candidate check for a finding class too noisy?", .reply⟩
def statesPreventionLimit : Atom := ⟨"statesPreventionLimit",
  "Does this reply state a limit of a prevention it adds?", .reply⟩
def closesPreventionLimit : Atom := ⟨"closesPreventionLimit",
  "Does this edit close a prevention's stated limit, or make it a clause-table question for each row?", .edit⟩
def editsTest : Atom := ⟨"editsTest", "Does this edit write, change or rewrite a test?", .edit⟩
def propertyTestOffProfiles : Atom := ⟨"propertyTestOffProfiles",
  "Does this edit write a property test without Hypothesis or outside the profiles of `tools/tests/property_profiles.py`?", .edit⟩
def propertyTestWithoutStatement : Atom := ⟨"propertyTestWithoutStatement",
  "Does this edit write a property test without its statement beside it, as precise as a formula, its domain as the strategy and its outcome as a relation or a model's agreement?", .edit⟩
def readsBodyUnderTest : Atom := ⟨"readsBodyUnderTest",
  "Does this read open the body of code a property test is being written for?", .read⟩
def exampleWithoutFailure : Atom := ⟨"exampleWithoutFailure",
  "Does this edit add an `@example` that holds no failure already found?", .edit⟩
def offersBranchForReview : Atom := ⟨"offersBranchForReview",
  "Does this reply offer a branch for review?", .reply⟩
def symbolFailuresNotFromRecap : Atom := ⟨"symbolFailuresNotFromRecap",
  "Does this reply report commit_symbol_use.py's failures from anywhere but the recap ending its output?", .reply⟩
def commitsInExternalRepository : Atom := ⟨"commitsInExternalRepository",
  "Is this commit made in a repository outside the workspace?", .call⟩
def judgesWithoutIntent : Atom := ⟨"judgesWithoutIntent",
  "Is this subagent asked to judge a change without knowing what it was meant to do?", .call⟩
def blindBriefInWorktree : Atom := ⟨"blindBriefInWorktree",
  "Does this subagent's brief set a reviewer judging without the change's intent to work in a git worktree?", .call⟩
def blindCopyInMrBrief : Atom := ⟨"blindCopyInMrBrief",
  "Does this merge request review's brief give the reviewer a blind copy?", .call⟩
def queuesFailedTest : Atom := ⟨"queuesFailedTest",
  "Does this call queue a test that failed once?", .call⟩
def waitingTestUnforced : Atom := ⟨"waitingTestUnforced",
  "Does this edit write a test that waits with a real-time bound or a sleep that is not the behaviour under test, rather than fixing the time or ordering events with a barrier, an event or a condition variable?", .edit⟩
def keepsRealTimeBound : Atom := ⟨"keepsRealTimeBound",
  "Does this edit keep a real-time bound in a test as the behaviour under test?", .edit⟩
def reviewsBranchBeforePush : Atom := ⟨"reviewsBranchBeforePush",
  "Is this subagent run a review of a branch before its push?", .call⟩
def leavesFlaggedTimeBound : Atom := ⟨"leavesFlaggedTimeBound",
  "Does this reply leave a test time_bound_tests.py flagged neither rewritten nor kept with `--allow`?", .reply⟩
def treatsRepeatAsPass : Atom := ⟨"treatsRepeatAsPass",
  "Does this reply treat a `tools/pytest_queue.py --repeat` run as passing a test?", .reply⟩
def blamesLanguage : Atom := ⟨"blamesLanguage",
  "Does this reply blame the language for a slow suite?", .reply⟩
def commitsPerCallCode : Atom := ⟨"commitsPerCallCode",
  "Does this commit add or change code that runs once per test, session or request?", .call⟩
def dismissesTimeRise : Atom := ⟨"dismissesTimeRise",
  "Does this reply treat a rise in the measured time of code run per test, session or request as other than a defect of the change?", .reply⟩
def targetKeepsOwnTimeCheck : Atom := ⟨"targetKeepsOwnTimeCheck",
  "Does the target repository of this checkpoint keep a time check of its own (a conftest budget, a CI time limit)?", .call⟩
def raisesSuiteBudget : Atom := ⟨"raisesSuiteBudget",
  "Does this edit raise a test suite's time budget?", .edit⟩
def statesBudgetReason : Atom := ⟨"statesBudgetReason",
  "Does this edit give the reason for the budget it raises?", .edit⟩
def usesEvidenceTool : Atom := ⟨"usesEvidenceTool",
  "Does this reply use the output of a tool written to produce evidence?", .reply⟩
def toolHidesUnread : Atom := ⟨"toolHidesUnread",
  "Does this edit write a tool producing evidence that doesn't report what it couldn't read?", .edit⟩
def rejectsFinding : Atom := ⟨"rejectsFinding",
  "Does this reply find a review finding not holding, or a matter of taste?", .reply⟩
def buildsForRejectedFinding : Atom := ⟨"buildsForRejectedFinding",
  "Does this edit build something for a review finding found not holding or a matter of taste?", .edit⟩
def fixBelowFirstRigor : Atom := ⟨"fixBelowFirstRigor",
  "Is this fix held to less rigor (tests, checks, review) than the change it fixes was?", .edit⟩
def largerFixThanNeeded : Atom := ⟨"largerFixThanNeeded",
  "Does this fix of a finding add more than another fix closing it would, without removing what the finding is about?", .edit⟩
def findsDefectInFix : Atom := ⟨"findsDefectInFix",
  "Does this reply find a defect in a fix made for an earlier finding?", .reply⟩
def caveatsMissingAsk : Atom := ⟨"caveatsMissingAsk",
  "Does this reply caveat something the user asked for that the branch lacks, instead of building it?", .reply⟩
def briefHasDescriptionAndAccess : Atom := ⟨"briefHasDescriptionAndAccess",
  "Does this subagent's brief give the branch's description and read access to its repositories?", .call⟩
def reportsReviewWithoutKind : Atom := ⟨"reportsReviewWithoutKind",
  "Does this reply report a review's result without naming which kind ran, a recheck or a fresh review in two stages?", .reply⟩
def freshReviewWithoutHeading : Atom := ⟨"freshReviewWithoutHeading",
  "Does this edit record a fresh review in two stages under a heading that doesn't name \"a fresh-context reviewer in two stages\"?", .edit⟩
def laterPassAfterFresh : Atom := ⟨"laterPassAfterFresh",
  "Does the review file of the branch this request pushes record a pass, such as a recheck, after its latest fresh review?", .call⟩
def writesOutsideDocument : Atom := ⟨"writesOutsideDocument",
  "Does this edit write a document a reader outside the workspace gets (a cover letter, a design, a page, an agenda, a message)?", .edit⟩
def wordsDocumentSentence : Atom := ⟨"wordsDocumentSentence",
  "Does this edit word a sentence stating a fact in a document that has an evidence ledger?", .edit⟩
def writesLedgerRow : Atom := ⟨"writesLedgerRow",
  "Does this edit write a row of an evidence ledger?", .edit⟩
def changesDocumentFact : Atom := ⟨"changesDocumentFact",
  "Does this edit change a fact a document with an evidence ledger states?", .edit⟩
def ledgerWrongColumns : Atom := ⟨"ledgerWrongColumns",
  "Does this edit give an evidence ledger columns other than Fact, Evidence, Checked on and Stated as, in that order?", .edit⟩
def copiesOtherLedger : Atom := ⟨"copiesOtherLedger",
  "Does this edit start a ledger from another task's ledger?", .edit⟩
def rowOnlyNamesSource : Atom := ⟨"rowOnlyNamesSource",
  "Does this edit write a ledger row whose evidence only names a source (a ticket, a page, a repository, the plan)?", .edit⟩
def statedAsExceedsFact : Atom := ⟨"statedAsExceedsFact",
  "Does this edit write a ledger row whose Stated as says more than its Fact?", .edit⟩
def restsOnOwnValue : Atom := ⟨"restsOnOwnValue",
  "Does this edit base a fact about what another system receives on a test of the code's own value rather than on that system's form of the data?", .edit⟩
def rowCitesRun : Atom := ⟨"rowCitesRun",
  "Does this edit write a ledger row citing a run?", .edit⟩
def staleRowsLeft : Atom := ⟨"staleRowsLeft",
  "Does the ledger of the branch this request pushes hold a stale row neither rechecked at the tip nor stating the diff and why its fact holds?", .call⟩
def writesEnvironmentRow : Atom := ⟨"writesEnvironmentRow",
  "Does this edit write a ledger row starting \"How it reaches its environment\"?", .edit⟩
def offersDocument : Atom := ⟨"offersDocument",
  "Does this reply offer a document for a reader outside the workspace?", .reply⟩
def leavesFlaggedFactRowless : Atom := ⟨"leavesFlaggedFactRowless",
  "Does this reply leave a fact reader_check.py flagged without its ledger row?", .reply⟩
def warnsReaderNamesMissing : Atom := ⟨"warnsReaderNamesMissing",
  "Does this result warn that `.reader-names` is missing?", .result⟩
def questionWithoutRoutes : Atom := ⟨"questionWithoutRoutes",
  "Does this edit write a question in a message without \"Routes tried:\" giving the checks run for its answer and what they found?", .edit⟩
def saysWhatItMisleads : Atom := ⟨"saysWhatItMisleads",
  "Does this reply say what the document leads a reader to assume that isn't so, or that it leads to no such assumption?", .reply⟩
def findsCoherenceConflict : Atom := ⟨"findsCoherenceConflict",
  "Does this reply find two sentences of a document conflicting, or a term meaning two things?", .reply⟩
def reviewsDocument : Atom := ⟨"reviewsDocument",
  "Is this subagent run the review of a document and its evidence ledger?", .call⟩
def briefHasDocumentLedgerAndCheck : Atom := ⟨"briefHasDocumentLedgerAndCheck",
  "Does this subagent's brief give the document, its final ledger, reader_check.py's output saved in a file and read access to the rows' sources?", .call⟩
def reviewsUserMessage : Atom := ⟨"reviewsUserMessage",
  "Is this subagent asked to review a message the user will send?", .call⟩
def fixAddsClaim : Atom := ⟨"fixAddsClaim",
  "Does this edit fix a document's finding by adding a factual claim?", .edit⟩
def fixesClaimFinding : Atom := ⟨"fixesClaimFinding",
  "Does this edit fix a finding about a claim?", .edit⟩
def editsDecidedFact : Atom := ⟨"editsDecidedFact",
  "Does this edit change a fact that a decision changed?", .edit⟩
def leavesClaimElsewhere : Atom := ⟨"leavesClaimElsewhere",
  "Does this reply report a claim fixed while another place stating it (a document, a commit message, a code comment) is left unfixed?", .reply⟩
def investigationOutsideReport : Atom := ⟨"investigationOutsideReport",
  "Does this edit write an investigation's artifact anywhere but the task's `REPORT.md`?", .edit⟩
def papersOverGuess : Atom := ⟨"papersOverGuess",
  "Does this edit present a guess in an investigation report as a finding?", .edit⟩
def stackedCutLeavesStateOpen : Atom := ⟨"stackedCutLeavesStateOpen",
  "Does this event cut a branch into stacked parts with a state a part writes ending only in a later part, unstated in the part's description?", .any⟩
def findsGuardSlippable : Atom := ⟨"findsGuardSlippable",
  "Does this reply find a guard whose limit a value can slip under?", .reply⟩
def gateKeysOnWording : Atom := ⟨"gateKeysOnWording",
  "Does this edit make a gate that an agent's action discharges key on the action's wording rather than on its result observed afterwards?", .edit⟩
def reliesOnSource : Atom := ⟨"reliesOnSource",
  "Does this reply rely on a statement of a source (a paper, a library, a recorded result)?", .reply⟩
def sourceHasNewerVersions : Atom := ⟨"sourceHasNewerVersions",
  "Does the source this reply relies on list newer versions?", .reply⟩
def usesPointedSource : Atom := ⟨"usesPointedSource",
  "Does this reply discuss or use a publication or Lean file that the user or a source pointed to?", .reply⟩
def missingEdgesAsIndependence : Atom := ⟨"missingEdgesAsIndependence",
  "Does this reply treat missing dependency edges between claims as their independence?", .reply⟩
def impactAsFalsity : Atom := ⟨"impactAsFalsity",
  "Does this reply treat an impact warning as a verdict that a claim is false?", .reply⟩
def reliesOnEncodingChange : Atom := ⟨"reliesOnEncodingChange",
  "Does this reply rely on a change to a rule, a tree or an encoding?", .reply⟩
def assignsResultStatus : Atom := ⟨"assignsResultStatus",
  "Does this edit assign a status to a new mathematical lemma, theorem, rule or encoding?", .edit⟩
def rerunsOldSuite : Atom := ⟨"rerunsOldSuite",
  "Does this call rerun an old test suite to simulate progress?", .call⟩
def testCannotFalsify : Atom := ⟨"testCannotFalsify",
  "Does this edit write a test or check that no outcome could falsify, or one without its negative control?", .edit⟩
def recordOmitsArgument : Atom := ⟨"recordOmitsArgument",
  "Does this edit record a result without its full argument, actual tests, dependencies, remaining gaps or exact parameter accounting?", .edit⟩
def unconditionalWithOpenGate : Atom := ⟨"unconditionalWithOpenGate",
  "Does this edit give an entry an unconditional status while its verification gate is incomplete?", .edit⟩
def reportsGap : Atom := ⟨"reportsGap",
  "Does this result report a reviewer's gap in an argument?", .result⟩
def reportsUnusedHypothesis : Atom := ⟨"reportsUnusedHypothesis",
  "Does this result report a hypothesis an argument doesn't use?", .result⟩
def reliesOnReviewerSuggestion : Atom := ⟨"reliesOnReviewerSuggestion",
  "Does this reply rely on a reviewer's suggestion or name it as a next step?", .reply⟩
def actsOnStandInObjection : Atom := ⟨"actsOnStandInObjection",
  "Does this edit act on an objection of the stand-in review?", .edit⟩
def commitClaimsEffect : Atom := ⟨"commitClaimsEffect",
  "Does this commit's message claim an effect of a framework change (faster, fewer refusals, fixed)?", .call⟩
def commitStatesUnchecked : Atom := ⟨"commitStatesUnchecked",
  "Does this commit's message state something about the change that wasn't measured or checked?", .call⟩
def reportsTested : Atom := ⟨"reportsTested",
  "Does this reply report a framework change as tested?", .reply⟩
def commitsFrameworkChange : Atom := ⟨"commitsFrameworkChange",
  "Does this commit change the framework (its tools, hooks, tests or site)?", .call⟩
def toolWithoutTestFile : Atom := ⟨"toolWithoutTestFile",
  "Does this commit add a standalone framework tool without its own test file?", .call⟩
def runsLocalWorkload : Atom := ⟨"runsLocalWorkload",
  "Does this call run a computation, a numerical check, a build, a test run or another local workload?", .call⟩
def commitsRecordReader : Atom := ⟨"commitsRecordReader",
  "Does this commit change a framework tool that reads the repository's records or whose work grows with its input?", .call⟩
def toolHidesGrowth : Atom := ⟨"toolHidesGrowth",
  "Does this edit write a tool whose work grows with its input that doesn't print what it grew with?", .edit⟩
def rerunsFinishedJob : Atom := ⟨"rerunsFinishedJob",
  "Does this call rerun a finished job's script or test kept as provenance?", .call⟩
def mixesProgress : Atom := ⟨"mixesProgress",
  "Does this edit report mathematics and goal progress together, not in separate paragraphs?", .edit⟩
def countsNonProgress : Atom := ⟨"countsNonProgress",
  "Does this event count a bigger toolbox, a stronger convenience, an equivalent reformulation or a finite check as goal progress by itself?", .any⟩
def citesNoDeclaredProof : Atom := ⟨"citesNoDeclaredProof",
  "Does this edit mark progress advanced without citing a claim the entry declares with a proof, a conditional reduction or a refutation?", .edit⟩
def assignsLeanWork : Atom := ⟨"assignsLeanWork",
  "Does this message from the user explicitly assign Lean formalization work?", .user⟩
def specialCaseAsFull : Atom := ⟨"specialCaseAsFull",
  "Does this reply treat a verified special case as verifying the full informal claim?", .reply⟩
def noLeanAsIncomplete : Atom := ⟨"noLeanAsIncomplete",
  "Does this reply treat the absence of Lean as mathematical incompleteness?", .reply⟩
def leanScopeInexact : Atom := ⟨"leanScopeInexact",
  "Does this edit record a claim's Lean coverage without its exact scope and file links, or without telling partial coverage or stronger hypotheses from complete verification?", .edit⟩
def restsOnAbstract : Atom := ⟨"restsOnAbstract",
  "Does this closure rest on a source's abstract?", .edit⟩
def declaresNoMechanism : Atom := ⟨"declaresNoMechanism",
  "Does this edit declare an open statement without mechanism?", .edit⟩
def objectionAsGeneralFalsification : Atom := ⟨"objectionAsGeneralFalsification",
  "Does this edit treat a one-step objection as falsifying more than the one formulation it addresses?", .edit⟩
def metaRepeatsPrevention : Atom := ⟨"metaRepeatsPrevention",
  "Does this edit write a Meta paragraph repeating its Prevention's mechanism?", .edit⟩
def metaNamesOnlyMistake : Atom := ⟨"metaNamesOnlyMistake",
  "Does this edit write a Meta paragraph naming only the one mistake?", .edit⟩
def stopsForRequestedChange : Atom := ⟨"stopsForRequestedChange",
  "Does this call stop a running piece of work because the user asked for a change?", .call⟩
def saysDiscardRun : Atom := ⟨"saysDiscardRun",
  "Does this message from the user say to discard the running work?", .user⟩
def multiRunLinesUnlabeled : Atom := ⟨"multiRunLinesUnlabeled",
  "Does this reply give lines read from several runs without labelling which run each came from?", .reply⟩
def omittedPartAsKnown : Atom := ⟨"omittedPartAsKnown",
  "Does this reply state as known a part a line it read omits (a wrapper, a field)?", .reply⟩
def undocumentedOrder : Atom := ⟨"undocumentedOrder",
  "Does this reply count on an order of lines the tool doesn't document?", .reply⟩
def checkShortOfDepth : Atom := ⟨"checkShortOfDepth",
  "Does this reply end or report a check before the depth set before its first result (a replay count, a sample)?", .reply⟩
def rewriteJustified : Atom := ⟨"rewriteJustified",
  "Does this history rewrite have a concrete justification (an MR's history cleanup, removing committed private data)?", .call⟩
def tagIsBackup : Atom := ⟨"tagIsBackup", "Is this tag made as a backup of a branch?", .call⟩
def deletesBackupEarly : Atom := ⟨"deletesBackupEarly",
  "Does this call delete a backup branch before the work it backs up is done?", .call⟩
def movedCheckFails : Atom := ⟨"movedCheckFails",
  "Does this result show a check of moved changes failing?", .result⟩
def callsIncompatible : Atom := ⟨"callsIncompatible",
  "Does this reply call two requirements incompatible?", .reply⟩
def destructiveAction : Atom := ⟨"destructiveAction",
  "Is this call a destructive or cleanup action?", .call⟩
def settlesAtDelivery : Atom := ⟨"settlesAtDelivery",
  "Does this reply settle a requirement at delivery, existence or rendering, without checking what its reader does with it when it matters?", .reply⟩
def parsesExternalAttribute : Atom := ⟨"parsesExternalAttribute",
  "Does this edit make code parse an external attribute or rely on an external query language's comparison semantics?", .edit⟩
def implementsOnAssumption : Atom := ⟨"implementsOnAssumption",
  "Does this edit implement on an assumption that a check could settle?", .edit⟩
def inCommittingScript : Atom := ⟨"inCommittingScript",
  "Is this call part of a script that commits for the agent (a rebase exec, a fixup helper)?", .call⟩
def statesCoverage : Atom := ⟨"statesCoverage",
  "Does this reply state what a reader or a check covers?", .reply⟩
def namesDefinitionAndOmissions : Atom := ⟨"namesDefinitionAndOmissions",
  "Does this reply name the definition the coverage was checked against and the forms it leaves out?", .reply⟩
def claimsBeyondDefinition : Atom := ⟨"claimsBeyondDefinition",
  "Does this reply claim \"each form\" or \"every case\" beyond the definition checked?", .reply⟩
def buildsReviewerFix : Atom := ⟨"buildsReviewerFix",
  "Does this edit build a fix a reviewer proposed?", .edit⟩
def fixesReader : Atom := ⟨"fixesReader",
  "Does this edit fix a reader, a guard or what a check accepts?", .edit⟩
def guardTestsOnlySeenForms : Atom := ⟨"guardTestsOnlySeenForms",
  "Does this edit write a guard's tests trying only the input forms already seen?", .edit⟩
def narrowsGuard : Atom := ⟨"narrowsGuard", "Does this edit narrow a guard?", .edit⟩
def addsRefusal : Atom := ⟨"addsRefusal", "Does this edit add a refusal to a guard?", .edit⟩
def narrowsByRebuilding : Atom := ⟨"narrowsByRebuilding",
  "Does this edit narrow a guard by rebuilding it from a list of forms that should refuse?", .edit⟩
def runsFixTests : Atom := ⟨"runsFixTests", "Does this call run a fix's tests?", .call⟩
def guardPassesUnclassified : Atom := ⟨"guardPassesUnclassified",
  "Does this edit make a guard pass an input it can't classify?", .edit⟩
def fixesLanguageGuard : Atom := ⟨"fixesLanguageGuard",
  "Does this edit fix a guard whose input is a language (the shell, a record's tags)?", .edit⟩
def guardLessonsPartial : Atom := ⟨"guardLessonsPartial",
  "Does this commit add a guard or gate without the guard lessons that another guard of the same change got?", .call⟩
def statesHowCodeRuns : Atom := ⟨"statesHowCodeRuns",
  "Does this reply state how code runs (which copy a loader reads, which path a call takes)?", .reply⟩
def endsGrant : Atom := ⟨"endsGrant", "Does this message from the user end a grant?", .user⟩
def routineInProgress : Atom := ⟨"routineInProgress",
  "Is a routine of several steps in progress at this point?", .any⟩
def callsFailurePreexisting : Atom := ⟨"callsFailurePreexisting",
  "Does this reply call a failure pre-existing?", .reply⟩
def inSharedCheckout : Atom := ⟨"inSharedCheckout",
  "Is this call run in a checkout shared with other sessions?", .call⟩
def statesChangeableState : Atom := ⟨"statesChangeableState",
  "Does this reply state the state of something someone else can change (a remote, a deployment, the user's terminal)?", .reply⟩
def statesNumber : Atom := ⟨"statesNumber",
  "Does this event state a number or result taken from a run's output?", .any⟩
def decisionRestsOnNumber : Atom := ⟨"decisionRestsOnNumber",
  "Does this reply take or propose a decision resting on a number (a duration, a size, a count)?", .reply⟩
def actsOnNumber : Atom := ⟨"actsOnNumber",
  "Does this call act on a number (a timeout, a batch size, a wait)?", .call⟩
def actsOnDerivedNumber : Atom := ⟨"actsOnDerivedNumber",
  "Does this reply rest a decision on a derived number (a rate, a share)?", .reply⟩
def entersMechanism : Atom := ⟨"entersMechanism",
  "Does this call enter an explanation of a mechanism into a commit or a rule?", .call⟩
def readsStatusCode : Atom := ⟨"readsStatusCode",
  "Does this reply read an endpoint's status code as evidence?", .reply⟩
def undefinedFromUseSearch : Atom := ⟨"undefinedFromUseSearch",
  "Does this reply conclude that nothing defines a name from a search finding it only where it is used?", .reply⟩
def changesDependencies : Atom := ⟨"changesDependencies",
  "Does this call change a project's dependencies?", .call⟩
def startsServer : Atom := ⟨"startsServer", "Does this call start a server?", .call⟩
def deletesInput : Atom := ⟨"deletesInput",
  "Does this call delete an input some output was made from?", .call⟩
def statesTipResult : Atom := ⟨"statesTipResult",
  "Does this reply state a check's result for a branch that is ready?", .reply⟩
def countNotFromDiff : Atom := ⟨"countNotFromDiff",
  "Does this event state a test count not generated from the branch's diff?", .any⟩
def unguardedPrecondition : Atom := ⟨"unguardedPrecondition",
  "Does this event hand over a precondition someone else must honour (a merge order, a sync before a step, a check before a deploy) without what makes the wrong way impossible or loud?", .any⟩
def exceedsMemoryBudget : Atom := ⟨"exceedsMemoryBudget",
  "Does this call run work that, with the jobs running beside it, uses more than 70% of MemTotal (floored to whole GiB) of RAM plus swap combined?", .call⟩
def exceedsCpuBudget : Atom := ⟨"exceedsCpuBudget",
  "Does this call run work that, with the jobs running beside it, uses more than 90% of the online logical CPUs (floored), or others than the lowest-numbered?", .call⟩
def memoryHeavyRun : Atom := ⟨"memoryHeavyRun",
  "Does this call run a computation whose memory use is a sizeable share of the budget?", .call⟩
def dropsAvailableRam : Atom := ⟨"dropsAvailableRam",
  "Does this call run work that brings the machine's available RAM below 5% of MemTotal?", .call⟩
def controllerOutputSkimmed : Atom := ⟨"controllerOutputSkimmed",
  "Does this reply act on a controller's output (compute.sh start or run, finish-turn.py, resume.py) having read only part of it?", .reply⟩
def asksToRunSetup : Atom := ⟨"asksToRunSetup",
  "Does this reply ask the user before rerunning resource-controls/setup.py?", .reply⟩
def toResumeWork : Atom := ⟨"toResumeWork",
  "Is this run made to resume work rather than to validate a change to the memory controls?", .call⟩
def showsReboot : Atom := ⟨"showsReboot", "Does this event show that the machine rebooted?", .any⟩

/-! Links: questions about an event and its anchor. -/

def recordsRawFindingsOf : Link := ⟨"recordsRawFindingsOf",
  "Does this edit record, under `### Open review` or `### Enumerated review`, the raw findings the anchored edit merges?"⟩
def readsUpstreamOfRebase : Link := ⟨"readsUpstreamOfRebase",
  "Does this call read the upstream commits the anchored rebase brought in that touch the branch's files or dependencies?"⟩
def recordsDependencyVerdict : Link := ⟨"recordsDependencyVerdict",
  "Does this edit record whether an upstream commit the anchored rebase brought in changes a logical dependency of the branch?"⟩
def fixesThatRow : Link := ⟨"fixesThatRow",
  "Does this edit fix the stale ledger row the anchored reply found?"⟩
def readsPathForClass : Link := ⟨"readsPathForClass",
  "Does this read open the plan's Path to sweep it for the class of the finding the anchored reply accepts?"⟩
def fixesClassInstances : Link := ⟨"fixesClassInstances",
  "Does this edit fix the instances of the class of the finding the anchored reply accepts?"⟩
def recordsMissingCheck : Link := ⟨"recordsMissingCheck",
  "Does this edit record in the task's review file which check of the writer's pass should have caught the finding the anchored reply accepts?"⟩
def runsClassCheck : Link := ⟨"runsClassCheck",
  "Does this call run, on the clause table, a check for the finding class the anchored review's brief follows?"⟩
def remeasuresCandidate : Link := ⟨"remeasuresCandidate",
  "Does this call measure again, rekeyed or narrowed, the candidate check the anchored reply found too noisy?"⟩
def draftsStatementFor : Link := ⟨"draftsStatementFor",
  "Does this edit draft the property statement for the code whose body the anchored read opens?"⟩
def settlesAllowed : Link := ⟨"settlesAllowed",
  "Does this edit make the test raise the real exception, record the library source in the plan, or rewrite the assertion that the anchored `--allow` passes?"⟩
def sameRepository : Link := ⟨"sameRepository",
  "Does this call install the hooks into the repository the anchored commit is made in?"⟩
def runsFailedTestAlone : Link := ⟨"runsFailedTestAlone",
  "Does this call run alone the failed test the anchored call queues?"⟩
def runsInWorkerOrder : Link := ⟨"runsInWorkerOrder",
  "Does this call run the failed test the anchored call queues in the order its worker ran?"⟩
def statesCauseOf : Link := ⟨"statesCauseOf",
  "Does this reply state the cause of the failure of the test the anchored call queues?"⟩
def addsDelayCase : Link := ⟨"addsDelayCase",
  "Does this edit add a case delaying the step the anchored edit's real-time bound limits by a fixed amount, showing the outcome claimed?"⟩
def checksCoreUse : Link := ⟨"checksCoreUse",
  "Does this call check whether the cores are busy during the suite the anchored reply calls slow?"⟩
def profilesTypicalTest : Link := ⟨"profilesTypicalTest",
  "Does this call profile a typical test of the suite the anchored reply calls slow?"⟩
def looksForSleeps : Link := ⟨"looksForSleeps",
  "Does this call look for sleeps or repeated work in the suite the anchored reply calls slow?"⟩
def timesThatCode : Link := ⟨"timesThatCode",
  "Does this call time on a real input the per-call code the anchored commit adds or changes?"⟩
def runsOwnTimeCheck : Link := ⟨"runsOwnTimeCheck",
  "Does this call run the target's own time-check command for the anchored checkpoint?"⟩
def measuresSuite : Link := ⟨"measuresSuite",
  "Does this call measure the suite whose budget the anchored edit raises?"⟩
def runsNegativeControl : Link := ⟨"runsNegativeControl",
  "Does this call run the evidence tool the anchored reply uses on a negative control, a case it must not report?"⟩
def assessesFinding : Link := ⟨"assessesFinding",
  "Does this call assess the finding the anchored edit fixes against the code, the record or a run?"⟩
def recordsRejectionReason : Link := ⟨"recordsRejectionReason",
  "Does this edit record the finding the anchored reply rejects with the reason?"⟩
def appliesFailureModes : Link := ⟨"appliesFailureModes",
  "Does this reply apply the failure-mode list to the fix the anchored edit builds?"⟩
def recordsPassDefect : Link := ⟨"recordsPassDefect",
  "Does this edit record the defect in a fix the anchored reply found as a defect of the pass, with the list item that should have found it?"⟩
def comparesBranchWithAsk : Link := ⟨"comparesBranchWithAsk",
  "Does this reply read the branch the anchored reply offers against the user's words naming the artifact?"⟩
def recordsPerFileReview : Link := ⟨"recordsPerFileReview",
  "Does this edit record, per file of the branch the anchored request pushes, what reading its diff checked?"⟩
def writesLedgerOf : Link := ⟨"writesLedgerOf",
  "Does this edit write the evidence ledger (`tasks/<X>/<DOC>_EVIDENCE.md`) of the document the anchored edit writes?"⟩
def writesRowFor : Link := ⟨"writesRowFor",
  "Does this edit write the ledger row of the fact the anchored edit's sentence states?"⟩
def checksRowFact : Link := ⟨"checksRowFact",
  "Does this call check the fact of the ledger row the anchored edit writes?"⟩
def editsRowOfChangedFact : Link := ⟨"editsRowOfChangedFact",
  "Does this edit change the ledger row of the fact the anchored edit changes?"⟩
def startsThatLedger : Link := ⟨"startsThatLedger",
  "Does this call start the ledger the anchored edit writes?"⟩
def givesProseRows : Link := ⟨"givesProseRows",
  "Does this edit give the commit messages and added comments of the branch the anchored reply offers their ledger rows?"⟩
def savesCitedRun : Link := ⟨"savesCitedRun",
  "Does this call save the run the anchored ledger row cites?"⟩
def writesEnvironmentRowOf : Link := ⟨"writesEnvironmentRowOf",
  "Does this edit write, for the branch the anchored request pushes, the row starting \"How it reaches its environment\" naming what builds it, its dependency versions, the sync and its order among the branches?"⟩
def readsEnvironmentSource : Link := ⟨"readsEnvironmentSource",
  "Does this read open a source (the CI file, the Dockerfile, the sync policy) of the anchored environment row?"⟩
def namesReaderNamesFile : Link := ⟨"namesReaderNamesFile",
  "Does this reply tell the user that `.reader-names`, which the anchored result says is missing, left names unchecked?"⟩
def readsOfferedDocumentWhole : Link := ⟨"readsOfferedDocumentWhole",
  "Does this read open, whole, the document the anchored reply offers?"⟩
def fixesConflictInText : Link := ⟨"fixesConflictInText",
  "Does this edit fix in the document's text the conflict the anchored reply found?"⟩
def reviewsSameDocument : Link := ⟨"reviewsSameDocument",
  "Is this subagent run another review of the document the anchored run reviews?"⟩
def rowForAddedClaim : Link := ⟨"rowForAddedClaim",
  "Does this edit write the ledger row of the claim the anchored fix adds?"⟩
def rechecksChangedParagraphs : Link := ⟨"rechecksChangedParagraphs",
  "Does this message resume the document's reviewer to recheck only the paragraphs the anchored fix changes?"⟩
def searchesClaimWords : Link := ⟨"searchesClaimWords",
  "Does this search look for the words of the claim the anchored edit fixes?"⟩
def searchesFactValue : Link := ⟨"searchesFactValue",
  "Does this search look for the value of the fact the anchored edit changes?"⟩
def rekeysGuard : Link := ⟨"rekeysGuard",
  "Does this edit make the guard the anchored reply found key on the behaviour it stands for?"⟩
def readsSourceHypotheses : Link := ⟨"readsSourceHypotheses",
  "Does this read open the hypotheses of the source the anchored reply relies on?"⟩
def comparesNewerVersions : Link := ⟨"comparesNewerVersions",
  "Does this reply compare individually every newer version of the source the anchored reply relies on?"⟩
def readsItsTheoremStatement : Link := ⟨"readsItsTheoremStatement",
  "Does this read open the theorem statement of the publication or Lean file the anchored reply uses?"⟩
def runsExhaustiveChecker : Link := ⟨"runsExhaustiveChecker",
  "Does this call run the exhaustive checker on the change the anchored reply relies on?"⟩
def reviewsResultCorrectness : Link := ⟨"reviewsResultCorrectness",
  "Does this reply make a focused correctness review of the result whose status the anchored edit assigns?"⟩
def resolvesGap : Link := ⟨"resolvesGap",
  "Does this edit resolve the gap the anchored result reports?"⟩
def dropsOrJustifiesHypothesis : Link := ⟨"dropsOrJustifiesHypothesis",
  "Does this edit drop or justify the unused hypothesis the anchored result reports?"⟩
def verifiesSuggestion : Link := ⟨"verifiesSuggestion",
  "Does this call verify the reviewer's suggestion the anchored reply relies on?"⟩
def checksObjection : Link := ⟨"checksObjection",
  "Does this read check against the record the stand-in objection the anchored edit acts on?"⟩
def measuresClaimedEffect : Link := ⟨"measuresClaimedEffect",
  "Does this call measure the effect the anchored commit's message claims?"⟩
def stagesReportedChange : Link := ⟨"stagesReportedChange",
  "Does this call stage the change the anchored reply reports as tested?"⟩
def coversAffectedTests : Link := ⟨"coversAffectedTests",
  "Does this run cover the tests the anchored commit's change could affect?"⟩
def timesOnRealRepository : Link := ⟨"timesOnRealRepository",
  "Does this call time the anchored commit's tool on the real repository?"⟩
def readsClosureSources : Link := ⟨"readsClosureSources",
  "Does this read open the source statements the anchored closure relies on?"⟩
def developsObjectionItems : Link := ⟨"developsObjectionItems",
  "Does this edit record a development cycle of every item closed by a one-step objection that bears on the statement the anchored edit declares without mechanism?"⟩
def weighsStopping : Link := ⟨"weighsStopping",
  "Does this event weigh what the work the anchored call stops has cost against what stopping saves?"⟩
def readsPlanNeeds : Link := ⟨"readsPlanNeeds",
  "Does this read open what the plan still needs from what the anchored step removes or closes?"⟩
def checksAgainstRemote : Link := ⟨"checksAgainstRemote",
  "Does this call check the branch the anchored call rewrites against its remote?"⟩
def backsUpRewrittenBranch : Link := ⟨"backsUpRewrittenBranch",
  "Does this call create a backup branch of the branch the anchored call rewrites?"⟩
def restoresFromBackup : Link := ⟨"restoresFromBackup",
  "Does this call restore from the backup branch the branch whose check the anchored result shows failing?"⟩
def measuresRealInput : Link := ⟨"measuresRealInput",
  "Does this call measure the real input the requirements the anchored reply calls incompatible are about?"⟩
def checksOrphans : Link := ⟨"checksOrphans",
  "Does this call check for orphaned state left by the anchored destructive action?"⟩
def probesRealValues : Link := ⟨"probesRealValues",
  "Does this call probe the real values or comparison semantics the anchored edit's code relies on?"⟩
def checksAssumption : Link := ⟨"checksAssumption",
  "Does this call check the assumption the anchored edit implements on?"⟩
def checksProposedFix : Link := ⟨"checksProposedFix",
  "Does this call check the reviewer's fix the anchored edit builds?"⟩
def readsPointsAgainstCode : Link := ⟨"readsPointsAgainstCode",
  "Does this read take each point of the item the anchored call closes against the changed code, one at a time?"⟩
def searchesValueForms : Link := ⟨"searchesValueForms",
  "Does this search look for the forms of a value the anchored fix reads in the real inputs the code reads?"⟩
def runsReaderOverInputs : Link := ⟨"runsReaderOverInputs",
  "Does this call run the reader the anchored edit changes over its real inputs, reading what it now reads differently?"⟩
def testsRefusedInputs : Link := ⟨"testsRefusedInputs",
  "Does this edit test the guard the anchored edit narrows with the inputs it exists to refuse?"⟩
def testsHarmlessNeighbour : Link := ⟨"testsHarmlessNeighbour",
  "Does this edit test the refusal the anchored edit adds beside the harmless input next to it that must pass?"⟩
def readsChangedFunction : Link := ⟨"readsChangedFunction",
  "Does this read open from its top the function the fix whose tests the anchored call runs changes?"⟩
def opensLanguageDefinition : Link := ⟨"opensLanguageDefinition",
  "Does this call open the definition of the language the anchored edit's guard reads?"⟩
def testNamesDefinition : Link := ⟨"testNamesDefinition",
  "Does this edit write a test naming the language definition for the guard the anchored edit fixes?"⟩
def runsToCheckSentence : Link := ⟨"runsToCheckSentence",
  "Does this call run the code the anchored reply says how it runs, to check that sentence?"⟩
def listsVerdictInputs : Link := ⟨"listsVerdictInputs",
  "Does this event write down every part of the input that can change the verdict of the reader the anchored edit fixes?"⟩
def testsEachVerdictInput : Link := ⟨"testsEachVerdictInput",
  "Does this edit test each part of the input that can change the verdict of the reader the anchored edit fixes?"⟩
def reassessesScope : Link := ⟨"reassessesScope",
  "Does this event work out again what each step of the routine in progress may touch after the anchored event moved a boundary?"⟩
def runsFailureOnMain : Link := ⟨"runsFailureOnMain",
  "Does this call run, against the main branch in a separate worktree, the failure the anchored reply calls pre-existing?"⟩
def checksThatStateLatest : Link := ⟨"checksThatStateLatest",
  "Is this call the latest check of the state the anchored reply states, with nothing since that could change it?"⟩
def printsThatNumber : Link := ⟨"printsThatNumber",
  "Does this result print the number or result the anchored event states?"⟩
def measuresDecisionNumber : Link := ⟨"measuresDecisionNumber",
  "Does this call measure the number the anchored reply's decision rests on?"⟩
def looksUpMeasurement : Link := ⟨"looksUpMeasurement",
  "Does this call look up, where the record holds it, the measurement of the number the anchored call acts on?"⟩
def recomputesFromSources : Link := ⟨"recomputesFromSources",
  "Does this call recompute the derived number the anchored reply rests on from its inputs' sources, its denominator above all?"⟩
def observationTestsExplanation : Link := ⟨"observationTestsExplanation",
  "Is this result an observation that could have contradicted the explanation the anchored call enters?"⟩
def readsRouteTable : Link := ⟨"readsRouteTable",
  "Does this call take the endpoint's path, whose status code the anchored reply reads, from the code's route table?"⟩
def readsUsePlace : Link := ⟨"readsUsePlace",
  "Does this read open the place the search the anchored reply concludes from found the name used?"⟩
def verifiesOutputOfDeleted : Link := ⟨"verifiesOutputOfDeleted",
  "Does this call verify the written output made from the input the anchored call deletes?"⟩
def resultAtTip : Link := ⟨"resultAtTip",
  "Is this result the one run at the branch's tip of the check whose result the anchored reply states?"⟩
def runsChecksAtTip : Link := ⟨"runsChecksAtTip",
  "Does this call run the branch's checks at the tip of the branch the anchored reply offers?"⟩
def resolvesWholeSet : Link := ⟨"resolvesWholeSet",
  "Does this resolution cover the whole dependency set the anchored install installs, base packages included, at the versions wanted?"⟩
def plansMemoryUse : Link := ⟨"plansMemoryUse",
  "Does this event plan the anchored run's memory below the limit, counting array copies, intermediates, BLAS workspaces and every parallel worker?"⟩

/-! The rules. -/

/-- Rule 281: a review's raw findings are recorded under their headings before any merge. -/
def r281 : Rule where
  number := 281
  keyword := .must
  formula := ev editing ∧ₗ atom mergesFindings ⟹ once (ev editing ∧ₗ link recordsRawFindingsOf)

/-- Rule 282: after a rebase, its upstream commits are read and the verdict on a logical dependency
recorded; a changed dependency calls for a fresh round. -/
def r282 : Rule where
  number := 282
  keyword := .must
  formula :=
    (ev gitRebase ⟹ eventually (ev readsHistory ∧ₗ link readsUpstreamOfRebase) ∧ₗ
      eventually (ev editing ∧ₗ link recordsDependencyVerdict)) ∧ₗ
    (ev editing ∧ₗ atom recordsChangedDependency ⟹ eventually (ev reviewerRun))

/-- Rule 283: no ledger in the open review's brief, and no reviewer auditing ledger rows. -/
def r283 : Rule where
  number := 283
  keyword := .must
  formula := never (ev agentRun ∧ₗ ((atom isOpenReview ∧ₗ atom briefHasLedger) ∨ₗ atom briefAsksLedgerAudit))

/-- Rule 284: a stale ledger row whose sentence holds is fixed by the writer and recorded as no
finding. -/
def r284 : Rule where
  number := 284
  keyword := .must
  formula := (ev reply ∧ₗ atom findsStaleHoldingRow ⟹ eventually (ev editing ∧ₗ link fixesThatRow)) ∧ₗ
    never (ev editing ∧ₗ atom recordsStaleRowAsFinding)

/-- Rule 285: an accepted finding's class is swept across the Path, read from the file, and every
instance fixed. -/
def r285 : Rule where
  number := 285
  keyword := .must
  formula := ev reply ∧ₗ atom acceptsReviewerFinding ⟹
    eventually (ev reading ∧ₗ link readsPathForClass) ∧ₗ eventually (ev editing ∧ₗ link fixesClassInstances)

/-- Rule 286: the review file records which check should have caught an accepted finding. -/
def r286 : Rule where
  number := 286
  keyword := .must
  formula := ev reply ∧ₗ atom acceptsReviewerFinding ⟹ eventually (ev editsReviewFile ∧ₗ link recordsMissingCheck)

/-- Rule 287: an enumerable class gets its check run on the table before the review is sent; a too
noisy candidate is rekeyed or narrowed and measured again. -/
def r287 : Rule where
  number := 287
  keyword := .must
  formula := (ev agentRun ∧ₗ atom enumerableClassPending ⟹ once (ev anyCall ∧ₗ link runsClassCheck)) ∧ₗ
    (ev reply ∧ₗ atom candidateTooNoisy ⟹ eventually (ev anyCall ∧ₗ link remeasuresCandidate))

/-- Rule 288: a prevention's stated limit is closed before the next review. -/
def r288 : Rule where
  number := 288
  keyword := .must
  formula := ev agentRun ⟹
    ¬ₗ since (ev reply ∧ₗ atom statesPreventionLimit) (ev editing ∧ₗ atom closesPreventionLimit)

/-- Rule 289: the property-testing skill is loaded before any test is written or changed. -/
def r289 : Rule where
  number := 289
  keyword := .must
  formula := ev editing ∧ₗ atom editsTest ⟹ once (ev loadsPropertyTesting)

/-- Rule 290: property tests use Hypothesis under the workspace's profiles. -/
def r290 : Rule where
  number := 290
  keyword := .must
  formula := never (ev editing ∧ₗ atom propertyTestOffProfiles)

/-- Rule 291: a property test's statement stands beside it, precise as a formula, drafted before the
body is read. -/
def r291 : Rule where
  number := 291
  keyword := .must
  formula := never (ev editing ∧ₗ atom propertyTestWithoutStatement) ∧ₗ
    (ev reading ∧ₗ atom readsBodyUnderTest ⟹ once (ev editing ∧ₗ link draftsStatementFor))

/-- Rule 292: an `@example` only for a failure already found. -/
def r292 : Rule where
  number := 292
  keyword := .mustNot
  formula := never (ev editing ∧ₗ atom exampleWithoutFailure)

/-- Rule 293: the three branch checks run before a branch is offered for review. -/
def r293 : Rule where
  number := 293
  keyword := .must
  formula := ev reply ∧ₗ atom offersBranchForReview ⟹
    once (ev commitSymbolUse) ∧ₗ once (ev handBuiltErrors) ∧ₗ once (ev circularOracle)

/-- Rule 294: `--allow` only after the real exception, the recorded source or the rewritten
assertion. -/
def r294 : Rule where
  number := 294
  keyword := .must
  formula := ev passesAllow ⟹ once (ev editing ∧ₗ link settlesAllowed)

/-- Rule 295: the git hooks are installed before the first commit in an external repository. -/
def r295 : Rule where
  number := 295
  keyword := .must
  formula := ev gitCommit ∧ₗ atom commitsInExternalRepository ⟹ once (ev installGitHooks ∧ₗ link sameRepository)

/-- Rule 296: commit_symbol_use.py's failures come from its closing recap. -/
def r296 : Rule where
  number := 296
  keyword := .must
  formula := never (ev reply ∧ₗ atom symbolFailuresNotFromRecap)

/-- Rule 297: a reviewer judging without the change's intent works on a blind copy. -/
def r297 : Rule where
  number := 297
  keyword := .must
  formula := ev agentRun ∧ₗ atom judgesWithoutIntent ⟹ once (ev blindCopy)

/-- Rule 298: no blind-copy reviewer briefed in a worktree, no blind copy in an MR review's brief. -/
def r298 : Rule where
  number := 298
  keyword := .mustNot
  formula := never (ev agentRun ∧ₗ (atom blindBriefInWorktree ∨ₗ atom blindCopyInMrBrief))

/-- Rule 299: a test that failed once is run alone and in its worker's order, and its cause found,
before it is queued. -/
def r299 : Rule where
  number := 299
  keyword := .must
  formula := ev leadQueueAdd ∧ₗ atom queuesFailedTest ⟹
    once (ev anyCall ∧ₗ link runsFailedTestAlone) ∧ₗ once (ev anyCall ∧ₗ link runsInWorkerOrder) ∧ₗ
      once (ev reply ∧ₗ link statesCauseOf)

/-- Rule 300: a waiting test forces its timing and keeps only the bounds under test. -/
def r300 : Rule where
  number := 300
  keyword := .must
  formula := never (ev editing ∧ₗ atom waitingTestUnforced)

/-- Rule 301: each real-time bound kept gets a fixed-delay case. -/
def r301 : Rule where
  number := 301
  keyword := .must
  formula := ev editing ∧ₗ atom keepsRealTimeBound ⟹ eventually (ev editing ∧ₗ link addsDelayCase)

/-- Rule 302: time_bound_tests.py runs before a branch's review, and what it flags is rewritten or
allowed. -/
def r302 : Rule where
  number := 302
  keyword := .must
  formula := (ev agentRun ∧ₗ atom reviewsBranchBeforePush ⟹ once (ev timeBoundTests)) ∧ₗ
    never (ev reply ∧ₗ atom leavesFlaggedTimeBound)

/-- Rule 303: `pytest_queue.py --repeat` passes no test. -/
def r303 : Rule where
  number := 303
  keyword := .mustNot
  formula := never (ev reply ∧ₗ atom treatsRepeatAsPass)

/-- Rule 304: before blaming the language for a slow suite, the cores, a profile and the sleeps. -/
def r304 : Rule where
  number := 304
  keyword := .must
  formula := ev reply ∧ₗ atom blamesLanguage ⟹
    once (ev anyCall ∧ₗ link checksCoreUse) ∧ₗ once (ev anyCall ∧ₗ link profilesTypicalTest) ∧ₗ
      once (ev anyCall ∧ₗ link looksForSleeps)

/-- Rule 305: per-call code is timed on a real input before its commit, and a later rise is a
defect. -/
def r305 : Rule where
  number := 305
  keyword := .must
  formula := (ev gitCommit ∧ₗ atom commitsPerCallCode ⟹ once (ev anyCall ∧ₗ link timesThatCode)) ∧ₗ
    never (ev reply ∧ₗ atom dismissesTimeRise)

/-- Rule 306: a checkpoint of a target with its own time check runs it since the previous checkpoint
and records it under an `-own` label. -/
def r306 : Rule where
  number := 306
  keyword := .must
  formula := ev taskCheckpoint ∧ₗ atom targetKeepsOwnTimeCheck ⟹
    ev ownTimedCheckpoint ∧ₗ since (ev anyCall ∧ₗ link runsOwnTimeCheck) (ev taskCheckpoint)

/-- Rule 307: a suite's time budget is raised only on a measurement and with a reason. -/
def r307 : Rule where
  number := 307
  keyword := .mustNot
  formula := ev editing ∧ₗ atom raisesSuiteBudget ⟹
    once (ev anyCall ∧ₗ link measuresSuite) ∧ₗ atom statesBudgetReason

/-- Rule 308: an evidence tool runs on a negative control, and reports what it couldn't read. -/
def r308 : Rule where
  number := 308
  keyword := .must
  formula := (ev reply ∧ₗ atom usesEvidenceTool ⟹ once (ev anyCall ∧ₗ link runsNegativeControl)) ∧ₗ
    never (ev editing ∧ₗ atom toolHidesUnread)

/-- Rule 309: a finding is assessed before its fix; one that doesn't hold is recorded with its reason
and nothing is built for it. -/
def r309 : Rule where
  number := 309
  keyword := .must
  formula :=
    (ev editing ∧ₗ atom fixesReviewFinding ⟹ once (ev anyCall ∧ₗ link assessesFinding)) ∧ₗ
    (ev reply ∧ₗ atom rejectsFinding ⟹ eventually (ev editing ∧ₗ link recordsRejectionReason)) ∧ₗ
    never (ev editing ∧ₗ atom buildsForRejectedFinding)

/-- Rule 310: a fix has the first change's rigor and the failure-mode list applied before it is
built. -/
def r310 : Rule where
  number := 310
  keyword := .must
  formula := (ev editing ∧ₗ atom fixesReviewFinding ⟹ once (ev reply ∧ₗ link appliesFailureModes)) ∧ₗ
    never (ev editing ∧ₗ atom fixBelowFirstRigor)

/-- Rule 311: of the fixes closing a finding, the one adding least, or one removing its cause. -/
def r311 : Rule where
  number := 311
  keyword := .must
  formula := never (ev editing ∧ₗ atom largerFixThanNeeded)

/-- Rule 312: a finding in a fix is recorded as the pass's defect with the item that should have
found it. -/
def r312 : Rule where
  number := 312
  keyword := .must
  formula := ev reply ∧ₗ atom findsDefectInFix ⟹ eventually (ev editing ∧ₗ link recordsPassDefect)

/-- Rule 313: a branch is read against the user's words before it is offered, and what is missing
is built, not caveated. -/
def r313 : Rule where
  number := 313
  keyword := .must
  formula := (ev reply ∧ₗ atom offersBranchForReview ⟹ once (ev reply ∧ₗ link comparesBranchWithAsk)) ∧ₗ
    never (ev reply ∧ₗ atom caveatsMissingAsk)

/-- Rule 314: a push request follows a review under mr-review recorded per file in a review file. -/
def r314 : Rule where
  number := 314
  keyword := .must
  formula := ev requestAdd ∧ₗ atom requestsPush ⟹
    once (ev loadsMrReview) ∧ₗ once (ev editsReviewFile ∧ₗ link recordsPerFileReview)

/-- Rule 315: the open review gets the format-patch commits, the description and read access, and no
ledger. -/
def r315 : Rule where
  number := 315
  keyword := .must
  formula := ev agentRun ∧ₗ atom isOpenReview ⟹
    once (ev formatPatch) ∧ₗ atom briefHasDescriptionAndAccess ∧ₗ ¬ₗ atom briefHasLedger

/-- Rule 316: a review report names its kind, and a fresh review is recorded under its heading. -/
def r316 : Rule where
  number := 316
  keyword := .must
  formula := never (ev reply ∧ₗ atom reportsReviewWithoutKind) ∧ₗ
    never (ev editing ∧ₗ atom freshReviewWithoutHeading)

/-- Rule 317: no push request while the review file records a pass after the fresh review. -/
def r317 : Rule where
  number := 317
  keyword := .mustNot
  formula := never (ev requestAdd ∧ₗ atom requestsPush ∧ₗ atom laterPassAfterFresh)

/-- Rule 318: a document for an outside reader is written from its ledger, built first. -/
def r318 : Rule where
  number := 318
  keyword := .must
  formula := ev editing ∧ₗ atom writesOutsideDocument ⟹ once (ev editsLedger ∧ₗ link writesLedgerOf)

/-- Rule 319: the row, its check done, before the sentence; a changed fact's ledger edit first, in a
message of its own. -/
def r319 : Rule where
  number := 319
  keyword := .must
  formula :=
    (ev editing ∧ₗ atom wordsDocumentSentence ⟹ once (ev editsLedger ∧ₗ link writesRowFor)) ∧ₗ
    (ev editsLedger ∧ₗ atom writesLedgerRow ⟹ once (ev anyCall ∧ₗ link checksRowFact)) ∧ₗ
    (ev editing ∧ₗ atom changesDocumentFact ⟹ once (ev editsLedger ∧ₗ link editsRowOfChangedFact)) ∧ₗ
    never (sameMessage ledgerWithItsDocument)

/-- Rule 320: a ledger's four columns, started by ledger_new.py, never from another task's. -/
def r320 : Rule where
  number := 320
  keyword := .must
  formula := (ev editsLedger ⟹ once (ev ledgerNew ∧ₗ link startsThatLedger)) ∧ₗ
    never (ev editsLedger ∧ₗ (atom ledgerWrongColumns ∨ₗ atom copiesOtherLedger))

/-- Rule 321: no row only naming a source, no Stated as saying more than its Fact. -/
def r321 : Rule where
  number := 321
  keyword := .mustNot
  formula := never (ev editsLedger ∧ₗ (atom rowOnlyNamesSource ∨ₗ atom statedAsExceedsFact))

/-- Rule 322: a fact about what another system receives rests on that system's form of the data. -/
def r322 : Rule where
  number := 322
  keyword := .must
  formula := never (ev editsLedger ∧ₗ atom restsOnOwnValue)

/-- Rule 323: an offered branch's commit messages and comments have ledger rows, written out by
branch_prose.py. -/
def r323 : Rule where
  number := 323
  keyword := .must
  formula := ev reply ∧ₗ atom offersBranchForReview ⟹
    once (ev branchProse) ∧ₗ once (ev editsLedger ∧ₗ link givesProseRows)

/-- Rule 324: before a push request, reader_check.py with `--also` and ledger_at_tip.py, and no stale
row left unexplained. -/
def r324 : Rule where
  number := 324
  keyword := .must
  formula := ev requestAdd ∧ₗ atom requestsPush ⟹
    once (ev readerCheckAlso) ∧ₗ once (ev ledgerAtTip) ∧ₗ ¬ₗ atom staleRowsLeft

/-- Rule 325: a row citing a run cites one saved with save-run-output.py. -/
def r325 : Rule where
  number := 325
  keyword := .must
  formula := ev editsLedger ∧ₗ atom rowCitesRun ⟹ once (ev saveRunOutput ∧ₗ link savesCitedRun)

/-- Rule 326: a pushed branch's ledger has its environment row, each part read at its source. -/
def r326 : Rule where
  number := 326
  keyword := .must
  formula := (ev requestAdd ∧ₗ atom requestsPush ⟹ once (ev editsLedger ∧ₗ link writesEnvironmentRowOf)) ∧ₗ
    (ev editsLedger ∧ₗ atom writesEnvironmentRow ⟹ once (ev reading ∧ₗ link readsEnvironmentSource))

/-- Rule 327: reader_check.py runs on a drafted document, and each fact it flags gets its row. -/
def r327 : Rule where
  number := 327
  keyword := .must
  formula := ev reply ∧ₗ atom offersDocument ⟹ once (ev readerCheck) ∧ₗ ¬ₗ atom leavesFlaggedFactRowless

/-- Rule 328: a missing `.reader-names` is told to the user. -/
def r328 : Rule where
  number := 328
  keyword := .must
  formula := ev toolResult ∧ₗ atom warnsReaderNamesMissing ⟹ eventually (ev reply ∧ₗ link namesReaderNamesFile)

/-- Rule 329: each question in a message carries "Routes tried:". -/
def r329 : Rule where
  number := 329
  keyword := .must
  formula := never (ev editing ∧ₗ atom questionWithoutRoutes)

/-- Rule 330: a document is read whole by object and term before it is offered, and what it misleads
a reader into is said. -/
def r330 : Rule where
  number := 330
  keyword := .must
  formula := ev reply ∧ₗ atom offersDocument ⟹
    once (ev reading ∧ₗ link readsOfferedDocumentWhole) ∧ₗ atom saysWhatItMisleads

/-- Rule 331: a coherence conflict is fixed in the text. -/
def r331 : Rule where
  number := 331
  keyword := .must
  formula := ev reply ∧ₗ atom findsCoherenceConflict ⟹ eventually (ev editing ∧ₗ link fixesConflictInText)

/-- Rule 332: one reviewer, in one pass, given the document, the ledger, saved reader_check output
and the sources. -/
def r332 : Rule where
  number := 332
  keyword := .must
  formula := ev agentRun ∧ₗ atom reviewsDocument ⟹
    atom briefHasDocumentLedgerAndCheck ∧ₗ once (ev readerCheck) ∧ₗ
      ¬ₗ once (ev agentRun ∧ₗ link reviewsSameDocument)

/-- Rule 333: no reviewer for a message the user sends. -/
def r333 : Rule where
  number := 333
  keyword := .mustNot
  formula := never (ev agentRun ∧ₗ atom reviewsUserMessage)

/-- Rule 334: a fix adding a claim gets its row first, and the same reviewer, resumed, rechecks the
changed paragraphs. -/
def r334 : Rule where
  number := 334
  keyword := .must
  formula := ev editing ∧ₗ atom fixAddsClaim ⟹
    once (ev editsLedger ∧ₗ link rowForAddedClaim) ∧ₗ eventually (ev resumesAgent ∧ₗ link rechecksChangedParagraphs)

/-- Rule 335: a claim's fix is searched for by its words and made everywhere; a decided fact's
places are found by its value before it is edited. -/
def r335 : Rule where
  number := 335
  keyword := .must
  formula :=
    (ev editing ∧ₗ atom fixesClaimFinding ⟹ once (ev searches ∧ₗ link searchesClaimWords)) ∧ₗ
    (ev editing ∧ₗ atom editsDecidedFact ⟹ once (ev searches ∧ₗ link searchesFactValue)) ∧ₗ
    never (ev reply ∧ₗ atom leavesClaimElsewhere)

/-- Rule 336: an investigation's artifact is the task's REPORT.md, with no papered-over guess. -/
def r336 : Rule where
  number := 336
  keyword := .must
  formula := never (ev editing ∧ₗ (atom investigationOutsideReport ∨ₗ atom papersOverGuess))

/-- Rule 337: a stacked part ends each state it writes, or its description says which stay open. -/
def r337 : Rule where
  number := 337
  keyword := .must
  formula := never (atom stackedCutLeavesStateOpen)

/-- Rule 338: a guard a value can slip under is rekeyed on the behaviour. -/
def r338 : Rule where
  number := 338
  keyword := .must
  formula := ev reply ∧ₗ atom findsGuardSlippable ⟹ eventually (ev editing ∧ₗ link rekeysGuard)

/-- Rule 339: a gate an action discharges keys on the action's result observed afterwards. -/
def r339 : Rule where
  number := 339
  keyword := .must
  formula := never (ev editing ∧ₗ atom gateKeysOnWording)

/-- Rule 340: a source's hypotheses are read before relying on it, and each newer version compared. -/
def r340 : Rule where
  number := 340
  keyword := .must
  formula := ev reply ∧ₗ atom reliesOnSource ⟹
    once (ev reading ∧ₗ link readsSourceHypotheses) ∧ₗ
      (atom sourceHasNewerVersions ⟹ once (ev reply ∧ₗ link comparesNewerVersions))

/-- Rule 342: a pointed-to publication or Lean file's theorem statement is read first. -/
def r342 : Rule where
  number := 342
  keyword := .must
  formula := ev reply ∧ₗ atom usesPointedSource ⟹ once (ev reading ∧ₗ link readsItsTheoremStatement)

/-- Rule 343: missing edges are no independence, an impact warning no falsity. -/
def r343 : Rule where
  number := 343
  keyword := .mustNot
  formula := never (ev reply ∧ₗ (atom missingEdgesAsIndependence ∨ₗ atom impactAsFalsity))

/-- Rule 344: the exhaustive checker runs on a rule, tree or encoding change before it is relied on. -/
def r344 : Rule where
  number := 344
  keyword := .must
  formula := ev reply ∧ₗ atom reliesOnEncodingChange ⟹ once (ev anyCall ∧ₗ link runsExhaustiveChecker)

/-- Rule 345: a focused correctness review before a new result's status. -/
def r345 : Rule where
  number := 345
  keyword := .must
  formula := ev editing ∧ₗ atom assignsResultStatus ⟹ once (ev reply ∧ₗ link reviewsResultCorrectness)

/-- Rule 346: falsifying tests with controls, and no old suite rerun to simulate progress. -/
def r346 : Rule where
  number := 346
  keyword := .must
  formula := never (ev editing ∧ₗ atom testCannotFalsify) ∧ₗ never (ev anyCall ∧ₗ atom rerunsOldSuite)

/-- Rule 347: full arguments, tests, dependencies, gaps and parameter accounting recorded. -/
def r347 : Rule where
  number := 347
  keyword := .must
  formula := never (ev editing ∧ₗ atom recordOmitsArgument)

/-- Rule 348: an incomplete verification gate means a conditional status. -/
def r348 : Rule where
  number := 348
  keyword := .must
  formula := never (ev editing ∧ₗ atom unconditionalWithOpenGate)

/-- Rule 349: every reviewer gap resolved, every unused hypothesis dropped or justified. -/
def r349 : Rule where
  number := 349
  keyword := .must
  formula := (ev toolResult ∧ₗ atom reportsGap ⟹ eventually (ev editing ∧ₗ link resolvesGap)) ∧ₗ
    (ev toolResult ∧ₗ atom reportsUnusedHypothesis ⟹ eventually (ev editing ∧ₗ link dropsOrJustifiesHypothesis))

/-- Rule 350: a reviewer's suggestion is verified before it is relied on or named as a next step. -/
def r350 : Rule where
  number := 350
  keyword := .must
  formula := ev reply ∧ₗ atom reliesOnReviewerSuggestion ⟹ once (ev anyCall ∧ₗ link verifiesSuggestion)

/-- Rule 351: a stand-in objection is checked against the record before it is acted on. -/
def r351 : Rule where
  number := 351
  keyword := .must
  formula := ev editing ∧ₗ atom actsOnStandInObjection ⟹ once (ev reading ∧ₗ link checksObjection)

/-- Rule 352: a framework commit claims only measured effects. -/
def r352 : Rule where
  number := 352
  keyword := .mustNot
  formula := (ev gitCommit ∧ₗ atom commitClaimsEffect ⟹ once (ev anyCall ∧ₗ link measuresClaimedEffect)) ∧ₗ
    never (ev gitCommit ∧ₗ atom commitStatesUnchecked)

/-- Rule 353: a change reported tested was staged, then run through suite_before_commit.py --run. -/
def r353 : Rule where
  number := 353
  keyword := .must
  formula := ev reply ∧ₗ atom reportsTested ⟹
    once (ev suiteBeforeCommit ∧ₗ once (ev gitStage ∧ₗ link stagesReportedChange))

/-- Rule 354: a framework commit follows the tests it could affect; a new tool brings its test
file. -/
def r354 : Rule where
  number := 354
  keyword := .must
  formula := (ev gitCommit ∧ₗ atom commitsFrameworkChange ⟹ once (ev frameworkTests ∧ₗ link coversAffectedTests)) ∧ₗ
    never (ev gitCommit ∧ₗ atom toolWithoutTestFile)

/-- Rule 355: local workloads run through compute.sh, after COMPUTATION_RULES.md is read. -/
def r355 : Rule where
  number := 355
  keyword := .must
  formula := never (ev anyCall ∧ₗ ¬ₗ ev viaComputeSh ∧ₗ atom runsLocalWorkload) ∧ₗ
    (ev viaComputeSh ⟹ once (ev readsComputationRules))

/-- Rule 356: a record-reading tool gets a timed run on the real repository and prints what its work
grew with. -/
def r356 : Rule where
  number := 356
  keyword := .must
  formula := (ev gitCommit ∧ₗ atom commitsRecordReader ⟹ once (ev anyCall ∧ₗ link timesOnRealRepository)) ∧ₗ
    never (ev editing ∧ₗ atom toolHidesGrowth)

/-- Rule 357: no rerun of a finished job's script under research/. -/
def r357 : Rule where
  number := 357
  keyword := .mustNot
  formula := never (ev runsResearchScript ∧ₗ atom rerunsFinishedJob)

/-- Rule 358: mathematics and goal progress reported apart. -/
def r358 : Rule where
  number := 358
  keyword := .must
  formula := never (ev editing ∧ₗ atom mixesProgress)

/-- Rule 359: no convenience, reformulation or finite check counted as goal progress. -/
def r359 : Rule where
  number := 359
  keyword := .mustNot
  formula := never ((ev reply ∨ₗ ev editing) ∧ₗ atom countsNonProgress)

/-- Rule 360: `data-goal-progress="advanced"` only citing a declared proof, reduction or refutation. -/
def r360 : Rule where
  number := 360
  keyword := .must
  formula := never (ev marksGoalAdvanced ∧ₗ atom citesNoDeclaredProof)

/-- Rule 361: formalization work only under explicit assignment, after its AGENTS.md and README. -/
def r361 : Rule where
  number := 361
  keyword := .mustNot
  formula := ev editsFormalization ⟹
    once (ev user ∧ₗ atom assignsLeanWork) ∧ₗ once (ev readsFormalizationAgents) ∧ₗ
      once (ev readsFormalizationReadme)

/-- Rule 362: a special case verifies no full claim; no Lean is no incompleteness. -/
def r362 : Rule where
  number := 362
  keyword := .mustNot
  formula := never (ev reply ∧ₗ (atom specialCaseAsFull ∨ₗ atom noLeanAsIncomplete))

/-- Rule 363: exact per-claim Lean scope with file links. -/
def r363 : Rule where
  number := 363
  keyword := .must
  formula := never (ev editing ∧ₗ atom leanScopeInexact)

/-- Rule 364: a Closed follow-up reads the source statements it relies on and rests on no
abstract. -/
def r364 : Rule where
  number := 364
  keyword := .mustNot
  formula := ev closesFollowUp ⟹ once (ev reading ∧ₗ link readsClosureSources) ∧ₗ ¬ₗ atom restsOnAbstract

/-- Rule 365: a one-step objection falsifies one formulation; its items get a development cycle
before a statement is declared without mechanism. -/
def r365 : Rule where
  number := 365
  keyword := .must
  formula := (ev editing ∧ₗ atom declaresNoMechanism ⟹ once (ev editing ∧ₗ link developsObjectionItems)) ∧ₗ
    never (ev editing ∧ₗ atom objectionAsGeneralFalsification)

/-- Rule 366: a Meta is neither the Prevention's mechanism nor about the one mistake only. -/
def r366 : Rule where
  number := 366
  keyword := .mustNot
  formula := never (ev editing ∧ₗ (atom metaRepeatsPrevention ∨ₗ atom metaNamesOnlyMistake))

/-- Rule 367: stopping running work follows weighing its cost; a requested change stops it only when
the user said to discard it. -/
def r367 : Rule where
  number := 367
  keyword := .must
  formula := (ev stopsWork ⟹ once (link weighsStopping)) ∧ₗ
    (ev stopsWork ∧ₗ atom stopsForRequestedChange ⟹ since (ev user ∧ₗ atom saysDiscardRun) (ev user))

/-- Rule 368: lines from several runs labelled, omitted parts unknown, orders only where documented. -/
def r368 : Rule where
  number := 368
  keyword := .must
  formula := never (ev reply ∧ₗ (atom multiRunLinesUnlabeled ∨ₗ atom omittedPartAsKnown ∨ₗ atom undocumentedOrder))

/-- Rule 369: a check runs to the depth set before its first result. -/
def r369 : Rule where
  number := 369
  keyword := .must
  formula := never (ev reply ∧ₗ atom checkShortOfDepth)

/-- Rule 370: a deletion, a push or a closed item is preceded by reading what the plan still needs. -/
def r370 : Rule where
  number := 370
  keyword := .must
  formula := ev deletes ∨ₗ ev publish ∨ₗ ev closesItem ⟹ once (ev reading ∧ₗ link readsPlanNeeds)

/-- Rule 371: after a compaction, the recorded knowledge is reloaded before an edit. -/
def r371 : Rule where
  number := 371
  keyword := .must
  formula := ev editing ⟹ ¬ₗ since (ev user ∧ₗ atom isCompactionSummary) (ev loadsKnowledge)

/-- Rule 372: history is rewritten only with a concrete justification. -/
def r372 : Rule where
  number := 372
  keyword := .must
  formula := ev rewritesHistory ⟹ atom rewriteJustified

/-- Rule 373: a rewrite follows a check against the remote and a backup branch, never a tag, kept
until the work is done. -/
def r373 : Rule where
  number := 373
  keyword := .must
  formula :=
    (ev rewritesHistory ⟹ once (ev anyCall ∧ₗ link checksAgainstRemote) ∧ₗ
      once (ev branchCreate ∧ₗ link backsUpRewrittenBranch)) ∧ₗ
    never (ev gitTag ∧ₗ atom tagIsBackup) ∧ₗ never (ev branchDelete ∧ₗ atom deletesBackupEarly)

/-- Rule 374: moved changes are checked by diff --stat, range-diff and a subject, author and date
comparison, and a failed check restores from the backup. -/
def r374 : Rule where
  number := 374
  keyword := .must
  formula :=
    (ev rewritesHistory ∧ₗ atom movesChanges ⟹
      eventually (ev diffStat) ∧ₗ eventually (ev rangeDiff) ∧ₗ eventually (ev logFormat)) ∧ₗ
    (ev toolResult ∧ₗ atom movedCheckFails ⟹ eventually (ev anyCall ∧ₗ link restoresFromBackup))

/-- Rule 375: requirements are called incompatible only after the real input is measured. -/
def r375 : Rule where
  number := 375
  keyword := .must
  formula := ev reply ∧ₗ atom callsIncompatible ⟹ once (ev anyCall ∧ₗ link measuresRealInput)

/-- Rule 376: orphaned state checked before and after a destructive or cleanup action. -/
def r376 : Rule where
  number := 376
  keyword := .must
  formula := ev anyCall ∧ₗ atom destructiveAction ⟹
    once (ev anyCall ∧ₗ link checksOrphans) ∧ₗ eventually (ev anyCall ∧ₗ link checksOrphans)

/-- Rule 377: a requirement is settled by its reader's use, not by delivery or existence. -/
def r377 : Rule where
  number := 377
  keyword := .must
  formula := never (ev reply ∧ₗ atom settlesAtDelivery)

/-- Rule 378: an external attribute's real values are probed, and a checkable assumption checked,
before code relies on them. -/
def r378 : Rule where
  number := 378
  keyword := .must
  formula :=
    (ev editing ∧ₗ atom parsesExternalAttribute ⟹ once (ev anyCall ∧ₗ link probesRealValues)) ∧ₗ
    (ev editing ∧ₗ atom implementsOnAssumption ⟹ once (ev anyCall ∧ₗ link checksAssumption))

/-- Rule 379: a committing script stages by name, never with `-a` or `.`. -/
def r379 : Rule where
  number := 379
  keyword := .must
  formula := never (ev stagesWholeTree ∧ₗ atom inCommittingScript)

/-- Rule 380: coverage stated by its definition and omissions, never beyond it. -/
def r380 : Rule where
  number := 380
  keyword := .must
  formula := ev reply ∧ₗ atom statesCoverage ⟹ atom namesDefinitionAndOmissions ∧ₗ ¬ₗ atom claimsBeyondDefinition

/-- Rule 381: a reviewer's fix is checked before it is built. -/
def r381 : Rule where
  number := 381
  keyword := .must
  formula := ev editing ∧ₗ atom buildsReviewerFix ⟹ once (ev anyCall ∧ₗ link checksProposedFix)

/-- Rule 382: a promised item closes after each point is read against the changed code. -/
def r382 : Rule where
  number := 382
  keyword := .must
  formula := ev closesItem ⟹ once (ev reading ∧ₗ link readsPointsAgainstCode)

/-- Rule 384: a fix's value forms are searched in the real inputs, and the changed reader run over
them. -/
def r384 : Rule where
  number := 384
  keyword := .must
  formula := ev editing ∧ₗ atom fixesReader ⟹
    once (ev searches ∧ₗ link searchesValueForms) ∧ₗ eventually (ev anyCall ∧ₗ link runsReaderOverInputs)

/-- Rule 385: a guard's tests try forms beyond those seen. -/
def r385 : Rule where
  number := 385
  keyword := .must
  formula := never (ev editing ∧ₗ atom guardTestsOnlySeenForms)

/-- Rule 386: a narrowed guard is tested with what it must refuse, an added refusal with its
harmless neighbour. -/
def r386 : Rule where
  number := 386
  keyword := .must
  formula := (ev editing ∧ₗ atom narrowsGuard ⟹ eventually (ev editing ∧ₗ link testsRefusedInputs)) ∧ₗ
    (ev editing ∧ₗ atom addsRefusal ⟹ eventually (ev editing ∧ₗ link testsHarmlessNeighbour))

/-- Rule 387: a guard is narrowed by exempting the harmless form, not rebuilt. -/
def r387 : Rule where
  number := 387
  keyword := .must
  formula := never (ev editing ∧ₗ atom narrowsByRebuilding)

/-- Rule 388: a fix's changed function is read from its top before its tests run. -/
def r388 : Rule where
  number := 388
  keyword := .must
  formula := ev anyCall ∧ₗ atom runsFixTests ⟹ once (ev reading ∧ₗ link readsChangedFunction)

/-- Rule 389: a guard refuses what it can't classify. -/
def r389 : Rule where
  number := 389
  keyword := .must
  formula := never (ev editing ∧ₗ atom guardPassesUnclassified)

/-- Rule 390: a guard over a language opens the language's definition in the step writing the fix
(since the last commit, which ends a step), and its test names it. -/
def r390 : Rule where
  number := 390
  keyword := .must
  formula := ev editing ∧ₗ atom fixesLanguageGuard ⟹
    since (ev anyCall ∧ₗ link opensLanguageDefinition) (ev gitCommit) ∧ₗ
      eventually (ev editing ∧ₗ link testNamesDefinition)

/-- Rule 391: the guard lessons reach every guard a change adds. -/
def r391 : Rule where
  number := 391
  keyword := .must
  formula := never (ev gitCommit ∧ₗ atom guardLessonsPartial)

/-- Rule 392: a sentence about how code runs is checked by running it. -/
def r392 : Rule where
  number := 392
  keyword := .must
  formula := ev reply ∧ₗ atom statesHowCodeRuns ⟹ once (ev anyCall ∧ₗ link runsToCheckSentence)

/-- Rule 393: before a reader's fix, the inputs changing its verdict are written down, and each is
tested. -/
def r393 : Rule where
  number := 393
  keyword := .must
  formula := ev editing ∧ₗ atom fixesReader ⟹
    once (link listsVerdictInputs) ∧ₗ eventually (ev editing ∧ₗ link testsEachVerdictInput)

/-- Rule 394: after a push, a merge or a grant's end, a routine's scope is worked out again. -/
def r394 : Rule where
  number := 394
  keyword := .must
  formula := (ev publish ∨ₗ ev gitMerge ∨ₗ (ev user ∧ₗ atom endsGrant)) ∧ₗ atom routineInProgress ⟹
    eventually (link reassessesScope)

/-- Rule 395: a pre-existing failure is confirmed on main in a separate worktree; no stash in a
shared checkout. -/
def r395 : Rule where
  number := 395
  keyword := .must
  formula := (ev reply ∧ₗ atom callsFailurePreexisting ⟹ once (ev anyCall ∧ₗ link runsFailureOnMain)) ∧ₗ
    never (ev gitStash ∧ₗ atom inSharedCheckout)

/-- Rule 396: state someone else can change is checked again before it is stated. -/
def r396 : Rule where
  number := 396
  keyword := .must
  formula := ev reply ∧ₗ atom statesChangeableState ⟹ once (ev anyCall ∧ₗ link checksThatStateLatest)

/-- Rule 397: a number is copied from output printed before it. -/
def r397 : Rule where
  number := 397
  keyword := .must
  formula := (ev reply ∨ₗ ev editing) ∧ₗ atom statesNumber ⟹ once (ev toolResult ∧ₗ link printsThatNumber)

/-- Rule 398: a number a decision rests on is measured in the turn. -/
def r398 : Rule where
  number := 398
  keyword := .must
  formula := ev reply ∧ₗ atom decisionRestsOnNumber ⟹
    since (ev anyCall ∧ₗ link measuresDecisionNumber) (ev user)

/-- Rule 399: a number acted on is looked up where it was measured; a derived one recomputed from its
sources. -/
def r399 : Rule where
  number := 399
  keyword := .must
  formula := (ev anyCall ∧ₗ atom actsOnNumber ⟹ once (ev anyCall ∧ₗ link looksUpMeasurement)) ∧ₗ
    (ev reply ∧ₗ atom actsOnDerivedNumber ⟹ once (ev anyCall ∧ₗ link recomputesFromSources))

/-- Rule 400: a mechanism's explanation enters a commit or a rule after an observation that could
have contradicted it. -/
def r400 : Rule where
  number := 400
  keyword := .must
  formula := ev anyCall ∧ₗ atom entersMechanism ⟹ once (ev toolResult ∧ₗ link observationTestsExplanation)

/-- Rule 401: an endpoint's path comes from the route table before its status code is evidence. -/
def r401 : Rule where
  number := 401
  keyword := .must
  formula := ev reply ∧ₗ atom readsStatusCode ⟹ once (ev anyCall ∧ₗ link readsRouteTable)

/-- Rule 402: a use-only search proves no absence; its place is read first. -/
def r402 : Rule where
  number := 402
  keyword := .mustNot
  formula := ev reply ∧ₗ atom undefinedFromUseSearch ⟹ once (ev reading ∧ₗ link readsUsePlace)

/-- Rule 403: processes and listeners checked before changing dependencies or starting a server. -/
def r403 : Rule where
  number := 403
  keyword := .must
  formula := ev anyCall ∧ₗ (atom changesDependencies ∨ₗ atom startsServer) ⟹ once (ev checksProcesses)

/-- Rule 404: an input is deleted after its output is written and verified. -/
def r404 : Rule where
  number := 404
  keyword := .must
  formula := ev deletes ∧ₗ atom deletesInput ⟹ once (ev anyCall ∧ₗ link verifiesOutputOfDeleted)

/-- Rule 405: checks run once at the ready branch's tip, and results stated from that run. -/
def r405 : Rule where
  number := 405
  keyword := .must
  formula := (ev reply ∧ₗ atom offersBranchForReview ⟹ once (ev anyCall ∧ₗ link runsChecksAtTip)) ∧ₗ
    (ev reply ∧ₗ atom statesTipResult ⟹ once (ev toolResult ∧ₗ link resultAtTip))

/-- Rule 406: test counts come from the branch diff or are left out. -/
def r406 : Rule where
  number := 406
  keyword := .must
  formula := never ((ev reply ∨ₗ ev editing) ∧ₗ atom countNotFromDiff)

/-- Rule 407: a precondition handed over comes with what makes the wrong way impossible or loud. -/
def r407 : Rule where
  number := 407
  keyword := .must
  formula := never ((ev reply ∨ₗ ev editing ∨ₗ ev requestAdd) ∧ₗ atom unguardedPrecondition)

/-- Rule 408: the whole dependency set resolved by a dry run before an install. -/
def r408 : Rule where
  number := 408
  keyword := .must
  formula := ev installs ⟹ once (ev dryRunResolve ∧ₗ link resolvesWholeSet)

/-- Rule 409: RAM plus swap within 70% of MemTotal across all jobs. -/
def r409 : Rule where
  number := 409
  keyword := .must
  formula := never (ev anyCall ∧ₗ atom exceedsMemoryBudget)

/-- Rule 410: CPUs within 90% of the online logical CPUs, the lowest-numbered. -/
def r410 : Rule where
  number := 410
  keyword := .must
  formula := never (ev anyCall ∧ₗ atom exceedsCpuBudget)

/-- Rule 411: a memory-heavy run's memory is planned below the limit first. -/
def r411 : Rule where
  number := 411
  keyword := .must
  formula := ev anyCall ∧ₗ atom memoryHeavyRun ⟹ once (link plansMemoryUse)

/-- Rule 412: available RAM stays above 5% of MemTotal. -/
def r412 : Rule where
  number := 412
  keyword := .must
  formula := never (ev anyCall ∧ₗ atom dropsAvailableRam)

/-- Rule 413: compute.sh runs directly, never through bash. -/
def r413 : Rule where
  number := 413
  keyword := .must
  formula := never (ev computeViaShell)

/-- Rule 414: the controllers' output read whole, never filtered, and the commands run as named. -/
def r414 : Rule where
  number := 414
  keyword := .must
  formula := never (ev controllerFiltered) ∧ₗ never (ev reply ∧ₗ atom controllerOutputSkimmed)

/-- Rule 415: no `pkill -f` or `pgrep -f`, whose pattern the invoking command always holds. -/
def r415 : Rule where
  number := 415
  keyword := .mustNot
  formula := never (ev pkillPattern)

/-- Rule 416: controls reported inactive are set up again and verified, without asking. -/
def r416 : Rule where
  number := 416
  keyword := .must
  formula := (ev toolResult ∧ₗ atom reportsControlsInactive ⟹
      eventually (ev controlsSetup ∧ₗ eventually (ev computeStatus))) ∧ₗ
    never (ev reply ∧ₗ atom asksToRunSetup)

/-- Rule 417: no resource stress test rerun to resume work. -/
def r417 : Rule where
  number := 417
  keyword := .mustNot
  formula := never (ev stressTest ∧ₗ atom toResumeWork)

/-- Rule 418: after a reboot, timing continues only in a fresh session. -/
def r418 : Rule where
  number := 418
  keyword := .must
  formula := ev timingContinues ⟹ ¬ₗ since (atom showsReboot) (ev computeStart)

/-- Rule 419: no environment prefix before compute.sh, which drops it. -/
def r419 : Rule where
  number := 419
  keyword := .must
  formula := never (ev envPrefixToCompute)

def rules : List Rule :=
  [r281, r282, r283, r284, r285, r286, r287, r288, r289, r290, r291, r292, r293, r294, r295, r296,
   r297, r298, r299, r300, r301, r302, r303, r304, r305, r306, r307, r308, r309, r310, r311, r312,
   r313, r314, r315, r316, r317, r318, r319, r320, r321, r322, r323, r324, r325, r326, r327, r328,
   r329, r330, r331, r332, r333, r334, r335, r336, r337, r338, r339, r340, r342, r343, r344, r345,
   r346, r347, r348, r349, r350, r351, r352, r353, r354, r355, r356, r357, r358, r359, r360, r361,
   r362, r363, r364, r365, r366, r367, r368, r369, r370, r371, r372, r373, r374, r375, r376, r377,
   r378, r379, r380, r381, r382, r384, r385, r386, r387, r388, r389, r390, r391, r392, r393, r394,
   r395, r396, r397, r398, r399, r400, r401, r402, r403, r404, r405, r406, r407, r408, r409, r410,
   r411, r412, r413, r414, r415, r416, r417, r418, r419]

/-- The range holds no MAY rule. -/
def permissions : List Nat := []

/-- Every number of the range outside the sample is in `rules`, in order, once. -/
theorem rules_cover_range :
    rules.map (·.number) = (List.range' 281 139).filter (fun n => n != 341 && n != 383) := by decide

/-- The mechanical predicates refuse their nearest harmless forms: a program whose name only ends in
`rm`, compute.sh run directly or with a thread count before it, a controller with nothing beside
it, a filtered command that is no controller, a kill by name, staging one file, listing or deleting
branches, a dry run, a plain push, a document beside its ledger, a script outside research/. Each
refusal is a theorem of its own, since the kernel holds memory for one declaration's whole
evaluation (task lean-build-memory). -/
theorem name_ending_in_rm_is_no_delete :
    deletes.test (bash "terraform apply") = false := by decide +kernel
theorem direct_compute_is_not_via_shell :
    computeViaShell.test (bash "./compute.sh python3 x.py") = false := by decide +kernel
theorem thread_count_prefix_refused :
    envPrefixToCompute.test (bash "OMP_NUM_THREADS=1 ./compute.sh python3 x.py") = false := by
  decide +kernel
theorem env_inside_compute_refused :
    envPrefixToCompute.test (bash "./compute.sh env FOO=1 python3 x.py") = false := by
  decide +kernel
theorem unfiltered_controller_refused :
    controllerFiltered.test (bash "./compute.sh start t1") = false := by decide +kernel
theorem filtered_run_is_no_controller :
    controllerFiltered.test (bash "./compute.sh python3 x.py | tail -3") = false := by
  decide +kernel
theorem kill_by_name_refused : pkillPattern.test (bash "pkill server") = false := by decide +kernel
theorem one_file_staged_refused : stagesWholeTree.test (bash "git add f.py") = false := by
  decide +kernel
theorem branch_delete_is_no_create : branchCreate.test (bash "git branch -D x") = false := by
  decide +kernel
theorem branch_list_is_no_create : branchCreate.test (bash "git branch") = false := by
  decide +kernel
theorem dry_run_is_no_install :
    installs.test (bash "pip install --dry-run --report r.json x") = false := by decide +kernel
theorem plain_push_is_no_rewrite : rewritesHistory.test (bash "git push origin b") = false := by
  decide +kernel
theorem document_is_no_ledger : editsLedger.test (edit "tasks/x/D.md") = false := by
  decide +kernel
theorem tools_script_is_no_research_script :
    runsResearchScript.test (bash "./compute.sh python3 tools/x.py") = false := by decide +kernel

end Rails.Ruleset.Range3
