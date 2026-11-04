import Rails.Rules
import Rails.Examples
import Rails.Witness

/-!
Rules 561 to 700 of `tasks/agents-on-rails/RULES.md` (the task protocol's theory rereads, Path
checks, loops, review loop, later cycles, queue, requests and stopping), the sample's 605 and 677
left out. Each MUST, MUST NOT, SHOULD or SHOULD NOT rule is a formula; the MAY rules 572 and 661 are
theorems.
-/

namespace Rails.Ruleset.Range5
open Rails Formula Ruleset Rules Examples

/-! Helpers for the predicates' tests. -/

/-- The words hold `s`. -/
def has (s : String) (ws : List (List Char)) : Bool := ws.contains s.toList

/-- Some word starts with `s` (`--fixup=abc` for `--fixup`). -/
def hasStart (s : String) (ws : List (List Char)) : Bool := ws.any (hasPrefix s.toList)

/-- The call's command text holds `s`. -/
def commandHolds (s : String) (e : Event) : Bool :=
  match command e with
  | some c => occursIn s.toList c.toList
  | none => false

/-- The text an edit writes (Edit's `new_string`, Write's `content`) holds `s`. -/
def editHolds (s : String) (e : Event) : Bool :=
  isEdit e && (occursIn s.toList ((e.field "new_string").getD "").toList ||
    occursIn s.toList ((e.field "content").getD "").toList)

/-- A reply whose text holds `s`. -/
def replyHolds (s : String) : Event → Bool
  | .reply t => occursIn s.toList t.toList
  | _ => false

def writesPathEnding (suffix : String) (e : Event) : Bool :=
  match writePath e with
  | some p => endsWith suffix.toList p.toList
  | none => false

def readsPathEnding (suffix : String) (e : Event) : Bool :=
  match readPath e with
  | some p => endsWith suffix.toList p.toList
  | none => false

def isReviewFileEdit (e : Event) : Bool :=
  match writePath e with
  | some p => occursIn "REVIEW".toList p.toList && endsWith ".md".toList p.toList
  | none => false

/-- A `tools/task_index.py` command whose words hold each of `ws`. -/
def taskIndex (ws : List String) : Event → Bool := runs "task_index.py" fun w => ws.all (has · w)

/-- A formula holding before, at or after the position. -/
def anytime (φ : Formula) : Formula := once φ ∨ₗ φ ∨ₗ eventually φ

/-! Event predicates. -/

def agentText : Pred := ⟨"agentText", fun e => isReply e || isThinking e, [.reply "r", .thinking "t"]⟩
def anyCall : Pred := ⟨"anyCall", isCall, [bash "ls"]⟩
def refusalEvent : Pred := ⟨"refusalEvent", isRefusalEvent, [.refusal "stop" "condition unmet"]⟩
def planEdit : Pred := ⟨"planEdit", writesPathEnding "PLAN.md", [edit "tasks/x/PLAN.md"]⟩
def planRead : Pred := ⟨"planRead", readsPathEnding "PLAN.md", [read "tasks/x/PLAN.md"]⟩
def reviewFileEdit : Pred := ⟨"reviewFileEdit", isReviewFileEdit, [edit "tasks/x/REVIEW.md"]⟩
def clauseTableEdit : Pred :=
  ⟨"clauseTableEdit", writesPathEnding "CLAUSE_TABLE.md", [edit "tasks/x/CLAUSE_TABLE.md"]⟩
def frameworkPassRecord : Pred := ⟨"frameworkPassRecord", runs "framework_pass.py" (has "record"),
  [bash "python3 tools/hooks/framework_pass.py record --summary s"]⟩
def theoryRewrap : Pred := ⟨"theoryRewrap", runs "rewrap_md.py" (has "--section"),
  [bash "tools/rewrap_md.py tasks/x/PLAN.md --section \"Theory building\""]⟩
def theoryCheck : Pred := ⟨"theoryCheck", runs "theory_check.py" (fun _ => true),
  [bash "tools/theory_check.py tasks/x/PLAN.md"]⟩
def theoryCheckLoop : Pred := ⟨"theoryCheckLoop", runs "theory_check.py" (has "--loop"),
  [bash "tools/theory_check.py tasks/x/PLAN.md --loop s"]⟩
def theoryCheckFilesOn : Pred := ⟨"theoryCheckFilesOn", runs "theory_check.py" (has "--files-on"),
  [bash "tools/theory_check.py tasks/x/PLAN.md --files-on main b"]⟩
def theoryCheckAbout : Pred := ⟨"theoryCheckAbout", runs "theory_check.py" (has "--about"),
  [bash "tools/theory_check.py tasks/x/PLAN.md --about lock"]⟩
def reread : Pred := ⟨"reread", taskIndex ["reread"], [bash "python3 tools/task_index.py reread x"]⟩
def taskNew : Pred := ⟨"taskNew", taskIndex ["new"], [bash "python3 tools/task_index.py new y"]⟩
def statusSet : Pred := ⟨"statusSet", taskIndex ["set"],
  [bash "python3 tools/task_index.py set x --status in_progress"]⟩
def setWaitsForBlocked : Pred := ⟨"setWaitsForBlocked", taskIndex ["set", "--waits-for", "blocked"],
  [bash "python3 tools/task_index.py set x --waits-for y --status blocked"]⟩
def setBlocked : Pred := ⟨"setBlocked", taskIndex ["set", "blocked"],
  [bash "python3 tools/task_index.py set x --status blocked"]⟩
def setComplete : Pred := ⟨"setComplete", taskIndex ["set", "complete"],
  [bash "python3 tools/task_index.py set x --status complete"]⟩
def requestToOthers : Pred := ⟨"requestToOthers", taskIndex ["request", "add", "--to-others"],
  [bash "python3 tools/task_index.py request add x --to-others --body-file b.md"]⟩
def requiredRequest : Pred := ⟨"requiredRequest", taskIndex ["request", "add", "required"],
  [bash "python3 tools/task_index.py request add x --kind required t"]⟩
def usersBecause : Pred := ⟨"usersBecause", taskIndex ["request", "add", "--users-because"],
  [bash "python3 tools/task_index.py request add x --users-because 'scope' t"]⟩
def requestReady : Pred := ⟨"requestReady", taskIndex ["request", "ready"],
  [bash "python3 tools/task_index.py request ready x 3"]⟩
def requestJudge : Pred := ⟨"requestJudge", taskIndex ["request", "judge"],
  [bash "python3 tools/task_index.py request judge x"]⟩
def requestEditBodyFile : Pred := ⟨"requestEditBodyFile", taskIndex ["request", "edit", "--body-file"],
  [bash "python3 tools/task_index.py request edit x 3 --body-file b.md"]⟩
def clauseTableRun : Pred := ⟨"clauseTableRun", runs "clause_table.py" (fun _ => true),
  [bash "tools/clause_table.py tasks/x/PLAN.md tasks/x/CLAUSE_TABLE.md"]⟩
def clauseTableNumber : Pred := ⟨"clauseTableNumber", runs "clause_table.py" (has "--number"),
  [bash "tools/clause_table.py tasks/x/PLAN.md tasks/x/CLAUSE_TABLE.md --number"]⟩
def clauseTableInit : Pred := ⟨"clauseTableInit", runs "clause_table.py" (has "--init"),
  [bash "tools/clause_table.py tasks/x/PLAN.md tasks/x/CLAUSE_TABLE.md --init"]⟩
def cycleNumbers : Pred := ⟨"cycleNumbers", runs "cycle_numbers.py" (has "--target"),
  [bash "tools/cycle_numbers.py x --target ~/dev/r"]⟩
def taskCheckpoint : Pred := ⟨"taskCheckpoint", runs "task_checkpoint.py" (fun _ => true),
  [bash "tools/task_checkpoint.py --entry e.html --message m"]⟩
/-- A research-record entry appended: by the appender or by the checkpoint given an entry. -/
def entryAppend : Pred := ⟨"entryAppend",
  fun e => runs "notebook-append.py" (fun _ => true) e || runs "task_checkpoint.py" (has "--entry") e,
  [bash "tools/notebook-append.py notebook.html e.html", bash "tools/task_checkpoint.py --entry e.html"]⟩
def recordSkeleton : Pred := ⟨"recordSkeleton", runs "record_skeleton.py" (fun _ => true),
  [bash "tools/record_skeleton.py round --out tasks/x/REVIEW.md"]⟩
def queueAdd : Pred := ⟨"queueAdd", runs "lead_queue.py" (has "add"),
  [bash "tools/lead_queue.py add notebook.html --idea i s t"]⟩
def queueAddBuild : Pred := ⟨"queueAddBuild", runs "lead_queue.py" (fun ws => has "add" ws && has "--build" ws),
  [bash "tools/lead_queue.py add notebook.html --build b s 'Problem: p. Must: m. Not now: n.'"]⟩
def queueCheckOrBuild : Pred := ⟨"queueCheckOrBuild",
  runs "lead_queue.py" (fun ws => has "add" ws && (has "--check" ws || has "--build" ws)),
  [bash "tools/lead_queue.py add notebook.html --check c s 'Problem: p. Must: m.'"]⟩
def problemAndMust : Pred := ⟨"problemAndMust",
  fun e => commandHolds "Problem:" e && commandHolds "Must:" e,
  [bash "tools/lead_queue.py add notebook.html --check c s 'Problem: p. Must: m.'"]⟩
def queueClose : Pred := ⟨"queueClose", runs "lead_queue.py" (has "close"),
  [bash "tools/lead_queue.py close notebook.html i done"]⟩
def gitAny : Pred := ⟨"gitAny", runs "git" (fun _ => true), [bash "git status"]⟩
def gitCommit : Pred := ⟨"gitCommit", runs "git" (has "commit"), [bash "git commit -m fix"]⟩
def fixupCommit : Pred := ⟨"fixupCommit", runs "git" (fun ws => has "commit" ws && hasStart "--fixup" ws),
  [bash "git commit --fixup abc", bash "git commit --fixup=abc"]⟩
def autosquash : Pred := ⟨"autosquash", runs "git" (has "--autosquash"),
  [bash "git rebase -i --autosquash main"]⟩
def gitLog : Pred := ⟨"gitLog", runs "git" (has "log"), [bash "git log --oneline main"]⟩
def gitShow : Pred := ⟨"gitShow", runs "git" (has "show"), [bash "git show main:a.py"]⟩
def searchCall : Pred := ⟨"searchCall",
  fun e => runs "grep" (fun _ => true) e || runs "rg" (fun _ => true) e || isTool "Grep" e,
  [bash "grep -n Loops research/notes/TASK_PROTOCOL.md", .call "g" "Grep" [("pattern", "loop")]]⟩
def ledgerAtTip : Pred := ⟨"ledgerAtTip", runs "ledger_at_tip.py" (fun _ => true),
  [bash "tools/ledger_at_tip.py L.md ~/dev/r HEAD"]⟩
def readerCheck : Pred := ⟨"readerCheck", runs "reader_check.py" (fun _ => true),
  [bash "tools/reader_check.py D.md L.md"]⟩
def backgroundCall : Pred := ⟨"backgroundCall",
  fun e => isTool "Bash" e && e.field "run_in_background" == some "true",
  [.call "b" "Bash" [("command", "tools/theory_check.py tasks/x/PLAN.md --loop s"),
    ("run_in_background", "true")]]⟩
def monitor : Pred := ⟨"monitor", isTool "Monitor", [.call "m" "Monitor" []]⟩
def agentCall : Pred := ⟨"agentCall", isTool "Agent",
  [.call "a" "Agent" [("subagent_type", "general-purpose")]]⟩
def sonnetReviewer : Pred := ⟨"sonnetReviewer",
  fun e => isReviewerRun e && e.field "model" == some "sonnet",
  [.call "a" "Agent" [("subagent_type", "medium-reviewer"), ("model", "sonnet")]]⟩
def sendMessage : Pred := ⟨"sendMessage", isTool "SendMessage", [.call "s" "SendMessage" []]⟩
def metEither : Pred := ⟨"metEither", replyHolds "Met in EITHER end state",
  [.reply "/goal x. Met in EITHER end state.\nCLEAN: a\nCAP: b"]⟩
def loopsApplied : Pred := ⟨"loopsApplied", replyHolds "Loops applied: ",
  [.reply "/goal x\nLoops applied: The review loop"]⟩
def capReachedEdit : Pred := ⟨"capReachedEdit", editHolds "## Cap reached",
  [.call "w" "Write" [("file_path", "tasks/x/REVIEW.md"), ("content", "## Cap reached\n3 rounds")]]⟩
def coverageParagraph : Pred := ⟨"coverageParagraph",
  fun e => editHolds "Found by both:" e && editHolds "Misses:" e && editHolds "Beyond the open review:" e,
  [.call "e" "Edit" [("file_path", "tasks/x/REVIEW.md"),
    ("new_string", "Coverage. Found by both: a. Misses: none. Beyond the open review: b.")]]⟩

def preds : List Pred :=
  [agentText, anyCall, refusalEvent, planEdit, planRead, reviewFileEdit, clauseTableEdit,
   frameworkPassRecord, theoryRewrap, theoryCheck, theoryCheckLoop, theoryCheckFilesOn,
   theoryCheckAbout, reread, taskNew, statusSet, setWaitsForBlocked, setBlocked, setComplete,
   requestToOthers, requiredRequest, usersBecause, requestReady, requestJudge, requestEditBodyFile,
   clauseTableRun, clauseTableNumber, clauseTableInit, cycleNumbers, taskCheckpoint, entryAppend,
   recordSkeleton, queueAdd, queueAddBuild, queueCheckOrBuild, problemAndMust, queueClose, gitAny,
   gitCommit, fixupCommit, autosquash, gitLog, gitShow, searchCall, ledgerAtTip, readerCheck,
   backgroundCall, monitor, agentCall, sonnetReviewer, sendMessage, metEither, loopsApplied,
   capReachedEdit, coverageParagraph]

theorem preds_wellFormed : preds.all Pred.wellFormed = true := by decide

/-! Atoms and links several rules of the range share. -/

def writesPath : Atom := ⟨"writesPath", "Does this edit change the Path section of a task plan?", .edit⟩
def implementationEdit : Atom := ⟨"implementationEdit",
  "Does this edit change what a task delivers (code, configuration, a migration) rather than its records?", .edit⟩
def bringsTheoryGaps : Atom := ⟨"bringsTheoryGaps",
  "Does this reply bring the user gaps a theory reread found?", .reply⟩
def givesGoalPrompt : Atom := ⟨"givesGoalPrompt", "Does this reply give a /goal prompt for a loop?", .reply⟩
def writesReconciliation : Atom := ⟨"writesReconciliation",
  "Does this edit write a review round's reconciliation?", .edit⟩
def reviewsPath : Atom := ⟨"reviewsPath",
  "Does this reviewer run review a task plan's Path or clause table?", .call⟩
def loopRound : Atom := ⟨"loopRound", "Is this reviewer run a round of a review loop?", .call⟩
def underFinishGoal : Atom := ⟨"underFinishGoal",
  "Is the agent working under a goal to finish the task at this point of the session?", .any⟩

def readsWholeTheory : Link := ⟨"readsWholeTheory",
  "Does this read take the whole Theory building section of the anchored event's plan from the file?"⟩
def rechecksFixes : Link := ⟨"rechecksFixes",
  "Does this message resume the enumerated reviewer to recheck the fixes made before the anchored event?"⟩
def checksOurAccess : Link := ⟨"checksOurAccess",
  "Is this call a read-only attempt checking that we lack the access a step of the anchored request needs?"⟩

/-! Rules 561 to 571. -/

def editsFramework : Atom := ⟨"editsFramework",
  "Does this edit change a framework file of the workspace (a tool, hook, rule file, skill or test)?", .edit⟩
def passCoversEdit : Link := ⟨"passCoversEdit",
  "Does this framework-pass record cover the change the anchored edit belongs to?"⟩
def presentsRecordedPass : Link := ⟨"presentsRecordedPass",
  "Does this reply give the user the theory pass the anchored call recorded?"⟩

/-- Rule 561: a framework change starts with a recorded theory pass, given to the user. -/
def frameworkPassFirst : Rule where
  number := 561
  keyword := .must
  domain := .tasks
  formula :=
    (ev editing ∧ₗ atom editsFramework ⟹ once (ev frameworkPassRecord ∧ₗ link passCoversEdit)) ∧ₗ
    (ev frameworkPassRecord ⟹ eventually (ev reply ∧ₗ link presentsRecordedPass))

def outsideTaskBeyondBoundedFix : Atom := ⟨"outsideTaskBeyondBoundedFix",
  "Is this edit part of a change outside any task that is larger than a bounded fix?", .edit⟩
def opensTaskForEdit : Link := ⟨"opensTaskForEdit",
  "Does this call open the task the anchored edit's change belongs to?"⟩

/-- Rule 562: a change beyond a bounded fix outside any task gets its own task first. -/
def taskBeforeLargeChange : Rule where
  number := 562
  keyword := .must
  domain := .tasks
  formula := ev editing ∧ₗ atom outsideTaskBeyondBoundedFix ⟹ once (ev taskNew ∧ₗ link opensTaskForEdit)

def batchesReread : Link := ⟨"batchesReread",
  "Does this text check every theory entry of the anchored edit's plan in one exhaustive pass?"⟩

/-- Rule 563: a reread, whole and from the file, before the Path is written. -/
def rereadBeforePlan : Rule where
  number := 563
  keyword := .must
  domain := .tasks
  formula := ev planEdit ∧ₗ atom writesPath ⟹
    once (ev planRead ∧ₗ link readsWholeTheory) ∧ₗ once (ev agentText ∧ₗ link batchesReread)

/-- Rule 564: the Theory building section is rewrapped after every edit to it. -/
def rewrapTheory : Rule where
  number := 564
  keyword := .must
  domain := .tasks
  formula := ev planEdit ∧ₗ atom editsTheory ⟹ eventually (ev theoryRewrap)

def checksEntriesAgainstChecklist : Link := ⟨"checksEntriesAgainstChecklist",
  "Does this text check every theory entry against the protocol's checklist, before the anchored reread?"⟩
def quotesEachRequirement : Link := ⟨"quotesEachRequirement",
  "Does this edit give each ticket acceptance criterion and user requirement an entry quoting it, met by a Path case?"⟩

/-- Rule 565: every entry through one checklist, requirements quoted and met by Path cases. -/
def checklistEveryEntry : Rule where
  number := 565
  keyword := .must
  domain := .tasks
  formula := ev reread ⟹
    once (ev agentText ∧ₗ link checksEntriesAgainstChecklist) ∧ₗ
    once (ev planEdit ∧ₗ link quotesEachRequirement)

def asksTicketDeparture : Atom := ⟨"asksTicketDeparture",
  "Does this request ask to depart from a ticket's proposal?", .call⟩
def departsFromTicketProposal : Atom := ⟨"departsFromTicketProposal",
  "Does this edit depart from a proposal a ticket makes?", .edit⟩
def licensesThisDeparture : Link := ⟨"licensesThisDeparture",
  "Does this message from the user license departing from the very proposal the anchored edit departs from?"⟩

/-- Rule 566: a ticket departure is a required request, and a licence covers its proposal alone. -/
def ticketDepartureRequired : Rule where
  number := 566
  keyword := .must
  domain := .tasks
  formula :=
    (ev requestAdd ∧ₗ atom asksTicketDeparture ⟹ ev requiredRequest) ∧ₗ
    (ev editing ∧ₗ atom departsFromTicketProposal ⟹ once (ev user ∧ₗ link licensesThisDeparture))

def readsEntriesByObject : Link := ⟨"readsEntriesByObject",
  "Does this text list the design's objects and read every entry touching each side by side, for the anchored reread's plan?"⟩

/-- Rule 567: entries checked together by shared object. -/
def sharedObjectCheck : Rule where
  number := 567
  keyword := .must
  domain := .tasks
  formula := ev reread ⟹ once (ev agentText ∧ₗ link readsEntriesByObject)

/-- Rule 568: `theory_check.py` at each pass's start and before gaps are brought. -/
def theoryCheckEachPass : Rule where
  number := 568
  keyword := .must
  domain := .tasks
  formula :=
    (ev reread ⟹ since (ev theoryCheck) (ev reread)) ∧ₗ
    (ev reply ∧ₗ atom bringsTheoryGaps ⟹ once (ev theoryCheck))

/-- Rule 569: the theory check's loop runs in the background, watched. -/
def theoryLoopWatched : Rule where
  number := 569
  keyword := .must
  domain := .tasks
  formula := ev theoryCheckLoop ⟹ ev backgroundCall ∧ₗ eventually (ev monitor)

def taskSpansBranches : Atom := ⟨"taskSpansBranches",
  "Do the decisions of the task in progress change files on more than one branch?", .any⟩
def portsFile : Atom := ⟨"portsFile", "Does this edit port or change a file another branch also holds?", .edit⟩
def readsLandingState : Link := ⟨"readsLandingState",
  "Does this call read the anchored edit's file as it stands on the branch the step lands on?"⟩

/-- Rule 570: `--files-on` for a task over several branches; a port starts from the landing
branch's file. -/
def filesOnBranches : Rule where
  number := 570
  keyword := .must
  domain := .tasks
  formula :=
    (ev reread ∧ₗ atom taskSpansBranches ⟹ since (ev theoryCheckFilesOn) (ev reread)) ∧ₗ
    (ev editing ∧ₗ atom portsFile ⟹ once ((ev reading ∨ₗ ev gitShow) ∧ₗ link readsLandingState))

def stopsAtFirstGap : Atom := ⟨"stopsAtFirstGap",
  "Does this reply end a theory pass at the first gap it found?", .reply⟩
def gapVoidsPass : Atom := ⟨"gapVoidsPass",
  "Does this reply name a gap that makes the rest of the pass meaningless?", .reply⟩
def bringsAllGapsAtOnce : Atom := ⟨"bringsAllGapsAtOnce",
  "Does this reply bring every gap the pass found, in this one message?", .reply⟩
def leavesStaleTextUnfixed : Atom := ⟨"leavesStaleTextUnfixed",
  "Does this reply report stale theory text the agent left unfixed?", .reply⟩
def rereadReportsChange : Atom := ⟨"rereadReportsChange",
  "Is this the result of a reread record saying the pass changed the theory?", .result⟩
def recordsGapsWithProposals : Link := ⟨"recordsGapsWithProposals",
  "Does this edit record in Open questions, each with a proposal, the gaps the anchored reply brings?"⟩

/-- Rule 571: no stop at the first gap; every gap recorded with a proposal and brought at once,
stale text fixed, and the pass repeated until nothing is new. -/
def everyGapOnePass : Rule where
  number := 571
  keyword := .mustNot
  domain := .tasks
  formula :=
    never (ev reply ∧ₗ atom stopsAtFirstGap ∧ₗ ¬ₗ atom gapVoidsPass) ∧ₗ
    (ev reply ∧ₗ atom bringsTheoryGaps ⟹
      atom bringsAllGapsAtOnce ∧ₗ once (ev planEdit ∧ₗ link recordsGapsWithProposals)) ∧ₗ
    never (ev reply ∧ₗ atom leavesStaleTextUnfixed) ∧ₗ
    (ev passingResult ∧ₗ atom rereadReportsChange ⟹ eventually (ev reread))

/-! Rules 573 to 594. -/

def recordsDecision : Atom := ⟨"recordsDecision",
  "Does this edit record a proposal or decision of the theory pass?", .edit⟩
def updatesDependents : Atom := ⟨"updatesDependents",
  "Does this edit also bring up to date every entry depending on the decision it records?", .edit⟩
def checksOwnOutput : Link := ⟨"checksOwnOutput",
  "Does this text put the anchored edit's decision through the checklist and the shared-object check?"⟩

/-- Rule 573: the pass's own output through the checks, dependents updated in the same edit. -/
def checkOwnOutput : Rule where
  number := 573
  keyword := .must
  domain := .tasks
  formula := ev planEdit ∧ₗ atom recordsDecision ⟹
    atom updatesDependents ∧ₗ once (ev agentText ∧ₗ link checksOwnOutput)

def recordsUserNeed : Atom := ⟨"recordsUserNeed",
  "Does this edit record something needing the user (an approval, an install, a decision)?", .edit⟩
def planWithRequest : Rel := ⟨"planWithRequest",
  fun s t => writesPathEnding "PLAN.md" s.event && isRequestAdd t.event,
  [(edit "tasks/x/PLAN.md", bash "python3 tools/task_index.py request add x")]⟩

def rels : List Rel := [planWithRequest]
theorem rels_wellFormed : rels.all Rel.wellFormed = true := by decide

/-- Rule 574: what needs the user becomes a request in the same edit. -/
def userNeedIsRequest : Rule where
  number := 574
  keyword := .must
  domain := .tasks
  formula := ev planEdit ∧ₗ atom recordsUserNeed ⟹ sameMessage planWithRequest

def reportsPassDone : Atom := ⟨"reportsPassDone", "Does this reply report a finished theory pass?", .reply⟩

/-- Rule 575: a pass ends with `task_index.py reread`. -/
def passEndsWithReread : Rule where
  number := 575
  keyword := .must
  domain := .tasks
  formula := ev reply ∧ₗ atom reportsPassDone ⟹ since (ev reread) (ev planEdit)

def recordsUnchanged : Atom := ⟨"recordsUnchanged",
  "Does this reread call record the theory as unchanged?", .call⟩

/-- Rule 576: an unchanged reread follows a whole read of the section since the previous one. -/
def unchangedNeedsRead : Rule where
  number := 576
  keyword := .must
  domain := .tasks
  formula := ev reread ∧ₗ atom recordsUnchanged ⟹ since (ev planRead ∧ₗ link readsWholeTheory) (ev reread)

def carriesEveryClause : Link := ⟨"carriesEveryClause",
  "Does this text carry each decision clause of the anchored edit's theory, exceptions, fallbacks and never-clauses included, to a step and a failing acceptance case, or say why it has none?"⟩

/-- Rule 577: each decision clause carried to its step and case. -/
def carryEachClause : Rule where
  number := 577
  keyword := .must
  domain := .tasks
  formula := ev planEdit ∧ₗ atom writesPath ⟹ once (ev agentText ∧ₗ link carriesEveryClause)

def pathOfLongTheory : Atom := ⟨"pathOfLongTheory",
  "Does this edit write the Path of a plan whose theory has several hundred decision clauses?", .edit⟩

/-- Rule 578: a clause table for a long theory, checked with `clause_table.py`. -/
def clauseTableForLongTheory : Rule where
  number := 578
  keyword := .must
  domain := .tasks
  formula :=
    (ev planEdit ∧ₗ atom pathOfLongTheory ⟹ anytime (ev clauseTableEdit)) ∧ₗ
    (ev clauseTableEdit ⟹ eventually (ev clauseTableRun))

/-- Rule 579: no clause-table maintenance once implementation has started. -/
def clauseTableStops : Rule where
  number := 579
  keyword := .must
  domain := .tasks
  formula := ev clauseTableEdit ⟹ ¬ₗ once (ev editing ∧ₗ atom implementationEdit)

def addsCases : Atom := ⟨"addsCases", "Does this edit add acceptance cases?", .edit⟩
def citesCaseByQuote : Atom := ⟨"citesCaseByQuote",
  "Does this edit cite a case by quoting it where the case has an id?", .edit⟩
def rewordsCase : Atom := ⟨"rewordsCase", "Does this edit reword a numbered case?", .edit⟩
def reopensCitingRows : Link := ⟨"reopensCitingRows",
  "Does this edit reopen the audit of the rows citing the case the anchored edit reworded?"⟩

/-- Rule 580: cases numbered at once, cited by id, and a reworded case's rows reopened. -/
def caseIds : Rule where
  number := 580
  keyword := .must
  domain := .tasks
  formula :=
    (ev clauseTableEdit ∧ₗ atom addsCases ⟹ anytime (ev clauseTableNumber)) ∧ₗ
    never (ev clauseTableEdit ∧ₗ atom citesCaseByQuote) ∧ₗ
    (ev clauseTableEdit ∧ₗ atom rewordsCase ⟹ anytime (ev clauseTableEdit ∧ₗ link reopensCitingRows))

def addsTagOrMember : Atom := ⟨"addsTagOrMember",
  "Does this edit add a tag in a code span or a listed member to the table?", .edit⟩
def answersFormsOfAnchor : Link := ⟨"answersFormsOfAnchor",
  "Does this edit answer, in Value forms or Members, the tag or member the anchored edit added (its forms, cases and empty form, or why none)?"⟩

/-- Rule 581: every tag and member answered in its section. -/
def answerTagsAndMembers : Rule where
  number := 581
  keyword := .must
  domain := .tasks
  formula := ev clauseTableEdit ∧ₗ atom addsTagOrMember ⟹
    anytime (ev clauseTableEdit ∧ₗ link answersFormsOfAnchor)

def answersSharedTagRule : Atom := ⟨"answersSharedTagRule",
  "Does this edit answer a rule given to several tags at once?", .edit⟩
def listsEveryTagForm : Atom := ⟨"listsEveryTagForm",
  "Does this edit list and try every deciding form of each tag the rule names?", .edit⟩
def readsJoinedRowsTogether : Link := ⟨"readsJoinedRowsTogether",
  "Does this text read side by side the rows of the tags the anchored edit's rule joins?"⟩

/-- Rule 582: a rule over several tags is a rule over each tag and form. -/
def tagFormPairs : Rule where
  number := 582
  keyword := .must
  domain := .tasks
  formula := ev clauseTableEdit ∧ₗ atom answersSharedTagRule ⟹
    atom listsEveryTagForm ∧ₗ anytime (ev agentText ∧ₗ link readsJoinedRowsTogether)

def fillsRow : Atom := ⟨"fillsRow", "Does this edit fill a clause-table row?", .edit⟩
def namesFailingCasePerRule : Link := ⟨"namesFailingCasePerRule",
  "Does this text take the anchored row's clause apart and name, for each of its rules, the case a violating implementation fails?"⟩

/-- Rule 583: a row read part by part before it is filled. -/
def rowPartByPart : Rule where
  number := 583
  keyword := .must
  domain := .tasks
  formula := ev clauseTableEdit ∧ₗ atom fillsRow ⟹ once (ev agentText ∧ₗ link namesFailingCasePerRule)

def writesNewDecision : Atom := ⟨"writesNewDecision", "Does this edit write a new decision?", .edit⟩
def writesCasesForNewDecision : Atom := ⟨"writesCasesForNewDecision",
  "Does this edit write the acceptance cases of a decision it writes, one for each members and value-forms row the decision adds?", .edit⟩

/-- Rule 584: a new decision's cases in the same edit, after `clause_table.py --init`. -/
def casesWithDecision : Rule where
  number := 584
  keyword := .must
  domain := .tasks
  formula :=
    (ev planEdit ∧ₗ atom writesNewDecision ⟹ atom writesCasesForNewDecision) ∧ₗ
    (ev planEdit ∧ₗ atom writesCasesForNewDecision ⟹ once (ev clauseTableInit))

def firstPathReview : Atom := ⟨"firstPathReview",
  "Is this reviewer run the first review of a task's Path or clause table?", .call⟩
def recordsRiskyIncrements : Link := ⟨"recordsRiskyIncrements",
  "Does this edit record the list of increments whose failure can damage something outside the tool's scratch, for the anchored review?"⟩
def auditsRiskyRowsFully : Link := ⟨"auditsRiskyRowsFully",
  "Does this text audit in full the rows of the risky increments before the anchored review?"⟩

/-- Rule 585: before the first review, the risky increments named, audited first and in full. -/
def riskyIncrementsFirst : Rule where
  number := 585
  keyword := .must
  domain := .tasks
  formula := ev reviewerRun ∧ₗ atom firstPathReview ⟹
    anytime (ev editing ∧ₗ link recordsRiskyIncrements) ∧ₗ once (ev agentText ∧ₗ link auditsRiskyRowsFully)

def needDeliveredLater : Atom := ⟨"needDeliveredLater",
  "Does this edit leave a Path step needing what only a later step delivers, with no interim rule stated?", .edit⟩
def listsStepNeeds : Link := ⟨"listsStepNeeds",
  "Does this text list, for each step of the anchored edit's Path, what it needs and the earlier step delivering each?"⟩

/-- Rule 586: each step's needs listed with the earlier step delivering them. -/
def stepNeeds : Rule where
  number := 586
  keyword := .must
  domain := .tasks
  formula := ev planEdit ∧ₗ atom writesPath ⟹
    ¬ₗ atom needDeliveredLater ∧ₗ once (ev agentText ∧ₗ link listsStepNeeds)

def pathItemsNotNested : Atom := ⟨"pathItemsNotNested",
  "Does this edit write a Path step's dependencies, deliverables, substeps or cases other than as nested list items each on its own line?", .edit⟩

/-- Rule 587: Path parts as nested list items. -/
def nestedPathItems : Rule where
  number := 587
  keyword := .must
  domain := .tasks
  formula := never (ev planEdit ∧ₗ atom pathItemsNotNested)

def stepLacksMembers : Atom := ⟨"stepLacksMembers",
  "Does this edit leave a step working through a set an inventory or count fixes without each member listed under it with its state?", .edit⟩

/-- Rule 588: a fixed set's members listed under its step. -/
def membersUnderStep : Rule where
  number := 588
  keyword := .must
  domain := .tasks
  formula := never (ev planEdit ∧ₗ atom stepLacksMembers)

def stepHoldsSeveralArtifacts : Atom := ⟨"stepHoldsSeveralArtifacts",
  "Does this edit leave a step holding several artifacts without a substep with its own acceptance for each?", .edit⟩

/-- Rule 589: one artifact per step, a substep per artifact. -/
def oneArtifactPerStep : Rule where
  number := 589
  keyword := .must
  domain := .tasks
  formula := never (ev planEdit ∧ₗ atom stepHoldsSeveralArtifacts)

def longStepUnsplit : Atom := ⟨"longStepUnsplit",
  "Does this edit leave a step over 8 acceptance cases or 400 words with neither substeps nor a `Not split:` reason?", .edit⟩

/-- Rule 590: a step within 8 cases and 400 words, or split, or `Not split:`. -/
def stepBounds : Rule where
  number := 590
  keyword := .should
  domain := .tasks
  formula := ev planEdit ∧ₗ atom longStepUnsplit ⟹ atom justified

def pathMakesDecision : Atom := ⟨"pathMakesDecision",
  "Does this edit put into the Path a statement the theory doesn't make (an interface detail, an exemption, a check's result, an interim rule)?", .edit⟩
def pathCitesNewEntry : Atom := ⟨"pathCitesNewEntry",
  "Does this edit make the Path cite a theory entry written in this cycle?", .edit⟩

/-- Rule 591: no decision in the Path; a new statement goes to the theory, reread, then cited. -/
def noDecisionInPath : Rule where
  number := 591
  keyword := .mustNot
  domain := .tasks
  formula :=
    never (ev planEdit ∧ₗ atom pathMakesDecision) ∧ₗ
    (ev planEdit ∧ₗ atom pathCitesNewEntry ⟹ since (ev reread) (ev planEdit ∧ₗ atom editsTheory))

def movesOrRenamesStep : Atom := ⟨"movesOrRenamesStep", "Does this edit move or rename a Path step?", .edit⟩
def checksStepReferences : Link := ⟨"checksStepReferences",
  "Does this text check the tables, slice headers, status paragraphs and next-lists against the steps the anchored edit moved or renamed?"⟩

/-- Rule 592: references checked after a move or rename. -/
def referencesAfterMove : Rule where
  number := 592
  keyword := .must
  domain := .tasks
  formula := ev planEdit ∧ₗ atom movesOrRenamesStep ⟹ eventually (ev agentText ∧ₗ link checksStepReferences)

def checksPathYourself : Link := ⟨"checksPathYourself",
  "Does this text check the Path against the theory (carry, needs, acceptance), for the anchored event?"⟩

/-- Rule 593: the writer checks the Path before a reviewer sees it and after every edit. -/
def writerChecksPath : Rule where
  number := 593
  keyword := .must
  domain := .tasks
  formula :=
    (ev reviewerRun ∧ₗ atom reviewsPath ⟹
      since (ev agentText ∧ₗ link checksPathYourself) (ev planEdit ∧ₗ atom writesPath)) ∧ₗ
    (ev planEdit ∧ₗ atom writesPath ⟹ eventually (ev agentText ∧ₗ link checksPathYourself))

def asksMembersAndForms : Link := ⟨"asksMembersAndForms",
  "Does this text read each clause the Path's last edits changed by its own words and ask its members and forms questions?"⟩

/-- Rule 594: changed clauses read by their words before the next review. -/
def changedClausesRead : Rule where
  number := 594
  keyword := .must
  domain := .tasks
  formula := ev reviewerRun ∧ₗ atom reviewsPath ⟹
    since (ev agentText ∧ₗ link asksMembersAndForms) (ev planEdit ∧ₗ atom writesPath)

/-! Rules 595 to 614, loops. -/

def proposesLoop : Atom := ⟨"proposesLoop", "Does this reply say the work ahead is a loop?", .reply⟩
def statesLoopCost : Atom := ⟨"statesLoopCost",
  "Does this reply design the loop for cost, saying what each round costs?", .reply⟩

/-- Rule 595: a loop comes with its `/goal` prompt, designed for cost. -/
def loopHasGoal : Rule where
  number := 595
  keyword := .must
  domain := .tasks
  formula := ev reply ∧ₗ atom proposesLoop ⟹ atom givesGoalPrompt ∧ₗ atom statesLoopCost

def goalMissesExit : Atom := ⟨"goalMissesExit",
  "Does this reply give a /goal condition lacking success, a cap on rounds, or non-convergence with what to record then?", .reply⟩

/-- Rule 596: every way out in the goal's condition. -/
def everyExitInCondition : Rule where
  number := 596
  keyword := .must
  domain := .tasks
  formula := never (ev reply ∧ₗ atom goalMissesExit)

def invokesRoundCap : Atom := ⟨"invokesRoundCap",
  "Does this reply stop or report work by invoking a cap on rounds?", .reply⟩
def setsGoal : Atom := ⟨"setsGoal", "Does this message from the user set a /goal?", .user⟩
def goalHasCap : Atom := ⟨"goalHasCap",
  "Does this message from the user set a /goal whose condition has a cap on rounds?", .user⟩

/-- Rule 597: no cap the latest user goal lacks. -/
def noInventedCap : Rule where
  number := 597
  keyword := .mustNot
  domain := .tasks
  formula := ev reply ∧ₗ atom invokesRoundCap ⟹
    since (ev user ∧ₗ atom goalHasCap) (ev user ∧ₗ atom setsGoal)

def reportsGoalStatus : Atom := ⟨"reportsGoalStatus",
  "Does this reply report on a goal's condition?", .reply⟩
def firstSentenceStatesCondition : Atom := ⟨"firstSentenceStatesCondition",
  "Does this reply's first sentence say, in the condition's words and with the evidence, whether the goal's condition holds?", .reply⟩
def otherWorkApart : Atom := ⟨"otherWorkApart",
  "Does this reply report the plan's other work apart, as outside the goal?", .reply⟩

/-- Rule 598: a goal report in the condition's words, first sentence first. -/
def reportInConditionWords : Rule where
  number := 598
  keyword := .must
  domain := .tasks
  formula := ev reply ∧ₗ atom reportsGoalStatus ⟹ atom firstSentenceStatesCondition ∧ₗ atom otherWorkApart

def stepCountAsGoalStatus : Atom := ⟨"stepCountAsGoalStatus",
  "Does this reply give a count of the plan's steps as the goal's status?", .reply⟩

/-- Rule 599: no step count as goal status. -/
def noStepCountStatus : Rule where
  number := 599
  keyword := .mustNot
  domain := .tasks
  formula := never (ev reply ∧ₗ atom stepCountAsGoalStatus)

def judgeRefusesHeldCondition : Atom := ⟨"judgeRefusesHeldCondition",
  "Is this refusal the goal's judge refusing a condition that holds?", .refusal⟩
def correctsReport : Link := ⟨"correctsReport",
  "Does this reply correct the goal report the anchored refusal refused, once?"⟩
def doesRefusalWork : Link := ⟨"doesRefusalWork",
  "Does this call do the work the anchored refusal names, or add a request with a corrected /goal prompt?"⟩

/-- Rule 600: a refused report corrected once; refused again, a call. -/
def judgeRefusal : Rule where
  number := 600
  keyword := .must
  domain := .tasks
  formula :=
    (ev refusalEvent ∧ₗ atom judgeRefusesHeldCondition ⟹
      eventually (ev reply ∧ₗ link correctsReport)) ∧ₗ
    (ev refusalEvent ∧ₗ atom judgeRefusesHeldCondition ∧ₗ
        once (ev refusalEvent ∧ₗ atom judgeRefusesHeldCondition) ⟹
      eventually (ev anyCall ∧ₗ link doesRefusalWork))

def offersIdea : Atom := ⟨"offersIdea",
  "Does this message from the user offer an idea (\"I think\", \"I wonder\") rather than decide?", .user⟩
def recordsIdeaAsDecision : Atom := ⟨"recordsIdeaAsDecision",
  "Does this edit record an idea the user offered as a plan decision?", .edit⟩
def recordsIdeaAsOpenQuestion : Link := ⟨"recordsIdeaAsOpenQuestion",
  "Does this edit record the anchored message's idea as an open question with the agent's assessment and any pushback?"⟩
def decidesIdea : Link := ⟨"decidesIdea",
  "Does this message from the user decide the idea the anchored edit records as a decision?"⟩

/-- Rule 601: a user's idea stays an open question until the user decides. -/
def ideaStaysOpen : Rule where
  number := 601
  keyword := .must
  domain := .tasks
  formula :=
    (ev user ∧ₗ atom offersIdea ⟹ eventually (ev planEdit ∧ₗ link recordsIdeaAsOpenQuestion)) ∧ₗ
    (ev planEdit ∧ₗ atom recordsIdeaAsDecision ⟹ once (ev user ∧ₗ link decidesIdea))

def capSaysSuccessNeedNotHold : Atom := ⟨"capSaysSuccessNeedNotHold",
  "Does this reply's /goal cap end state say the success conditions need not hold in it?", .reply⟩

/-- Rule 602: two end states, "Met in EITHER end state", the cap's saying success need not hold. -/
def twoEndStates : Rule where
  number := 602
  keyword := .must
  domain := .tasks
  formula := ev reply ∧ₗ atom givesGoalPrompt ⟹ ev metEither ∧ₗ atom capSaysSuccessNeedNotHold

def capNamesHeading : Atom := ⟨"capNamesHeading",
  "Does this reply's /goal cap end state check a `## Cap reached` heading listing rounds, each round's finding count and the open findings?", .reply⟩
def capSectionComplete : Atom := ⟨"capSectionComplete",
  "Does this `## Cap reached` section list the rounds run, each one's count of findings, and the findings still open or none?", .edit⟩
def runsAnotherRound : Atom := ⟨"runsAnotherRound", "Does this call run another round of the loop?", .call⟩
def reportsCapReached : Atom := ⟨"reportsCapReached", "Does this reply report the loop's cap reached?", .reply⟩

/-- Rule 603: the cap's one artifact, written on reaching it, and then a stop. -/
def capArtifact : Rule where
  number := 603
  keyword := .must
  domain := .tasks
  formula :=
    (ev reply ∧ₗ atom givesGoalPrompt ⟹ atom capNamesHeading) ∧ₗ
    (ev reply ∧ₗ atom reportsCapReached ⟹ once (ev capReachedEdit)) ∧ₗ
    (ev capReachedEdit ⟹ atom capSectionComplete ∧ₗ ¬ₗ eventually (ev anyCall ∧ₗ atom runsAnotherRound))

def listsRoundRuns : Atom := ⟨"listsRoundRuns",
  "Does this reply list what one round runs and what each run buys, with no run whose result a later round produces anyway?", .reply⟩

/-- Rule 604: a round's runs listed with what each buys. -/
def roundRunsListed : Rule where
  number := 604
  keyword := .must
  domain := .tasks
  formula := ev reply ∧ₗ atom givesGoalPrompt ⟹ atom listsRoundRuns

def namesRunInputs : Atom := ⟨"namesRunInputs",
  "Does this reply name what each run of the loop reads from another?", .reply⟩
def serializesIndependentRuns : Atom := ⟨"serializesIndependentRuns",
  "Does this text start or plan, one after another, runs that read nothing of each other?", .any⟩
def addsHookOrder : Atom := ⟨"addsHookOrder", "Does this edit make a hook hold an order between runs?", .edit⟩
def orderNamesOutput : Atom := ⟨"orderNamesOutput",
  "Does the order this edit adds name the output the later run reads?", .edit⟩

/-- Rule 606: runs' inputs named, independent runs together, a held order naming its output. -/
def runDependencies : Rule where
  number := 606
  keyword := .must
  domain := .tasks
  formula :=
    (ev reply ∧ₗ atom givesGoalPrompt ⟹ atom namesRunInputs) ∧ₗ
    never (ev agentText ∧ₗ atom serializesIndependentRuns) ∧ₗ
    (ev editing ∧ₗ atom addsHookOrder ⟹ atom orderNamesOutput)

def briefBoundsInput : Atom := ⟨"briefBoundsInput",
  "Does this reviewer run's brief bound what it reads (the new or unread part)?", .call⟩
def recordsCoverageOfRun : Link := ⟨"recordsCoverageOfRun",
  "Does this edit record in a file what the anchored run covered?"⟩

/-- Rule 607: each run's input bounded, its coverage tracked in a file. -/
def boundedTrackedRuns : Rule where
  number := 607
  keyword := .must
  domain := .tasks
  formula := ev reviewerRun ∧ₗ atom loopRound ⟹
    atom briefBoundsInput ∧ₗ anytime (ev editing ∧ₗ link recordsCoverageOfRun)

def declaresCleanEnd : Atom := ⟨"declaresCleanEnd", "Does this reply declare a loop's clean end?", .reply⟩
def roundWithNothingAboveBar : Link := ⟨"roundWithNothingAboveBar",
  "Is this result a review round with no finding above its bar, the one the anchored reply's clean end rests on?"⟩
def changesReviewedBeyondNotes : Atom := ⟨"changesReviewedBeyondNotes",
  "Does this edit change what a review read, beyond fixing that review's notes?", .edit⟩
def fixesReviewNote : Atom := ⟨"fixesReviewNote", "Does this edit fix a review's note?", .edit⟩

/-- Rule 608: a clean end is a round with nothing above the bar and nothing changed after but its
notes' fixes, which a recheck reads. -/
def cleanEnd : Rule where
  number := 608
  keyword := .must
  domain := .tasks
  formula :=
    (ev reply ∧ₗ atom declaresCleanEnd ⟹
      since (ev passingResult ∧ₗ link roundWithNothingAboveBar) (ev editing ∧ₗ atom changesReviewedBeyondNotes)) ∧ₗ
    (ev editing ∧ₗ atom fixesReviewNote ⟹ eventually (ev sendMessage ∧ₗ link rechecksFixes))

def statesCapSizing : Atom := ⟨"statesCapSizing",
  "Does this reply size the cap as the rounds to cover everything once plus expected repair rounds, stated with the prompt?", .reply⟩

/-- Rule 609: the cap sized from the work, with the prompt. -/
def capSized : Rule where
  number := 609
  keyword := .must
  domain := .tasks
  formula := ev reply ∧ₗ atom givesGoalPrompt ⟹ atom statesCapSizing

def conditionHoldsProcedure : Atom := ⟨"conditionHoldsProcedure",
  "Does this reply write a procedure step (rather than an end state) into a /goal condition?", .reply⟩

/-- Rule 610: no procedure in a loop condition. -/
def noProcedureInCondition : Rule where
  number := 610
  keyword := .mustNot
  domain := .tasks
  formula := never (ev reply ∧ₗ atom conditionHoldsProcedure)

def roundDepartsFromCondition : Atom := ⟨"roundDepartsFromCondition",
  "Does this run make a loop round depart from the goal's condition?", .call⟩
def announcesDeparture : Link := ⟨"announcesDeparture",
  "Does this reply say the anchored run's round departs from the condition, giving the corrected prompt?"⟩

/-- Rule 611: a departing round announced first, with the corrected prompt. -/
def departureAnnounced : Rule where
  number := 611
  keyword := .must
  domain := .tasks
  formula := ev anyCall ∧ₗ atom roundDepartsFromCondition ⟹ once (ev reply ∧ₗ link announcesDeparture)

def briefHandsWholeRecord : Atom := ⟨"briefHandsWholeRecord",
  "Does this reviewer run's brief hand over a whole plan, Path, theory or notebook rather than an excerpt file and the rows to judge?", .call⟩

/-- Rule 612: a reviewer gets an excerpt and its rows. -/
def excerptBrief : Rule where
  number := 612
  keyword := .must
  domain := .tasks
  formula := never (ev reviewerRun ∧ₗ atom briefHandsWholeRecord)

def roundTooSmall : Atom := ⟨"roundTooSmall",
  "Does this reviewer run serve a round too small to be worth a run?", .call⟩

/-- Rule 613: a round too small is folded into the next or audited by the writer. -/
def foldSmallRound : Rule where
  number := 613
  keyword := .should
  domain := .tasks
  formula := ev reviewerRun ∧ₗ atom roundTooSmall ⟹ atom justified

def runsLoopReview : Atom := ⟨"runsLoopReview",
  "Does this agent run make a review, a reconciliation or a row audit of a Path or clause table?", .call⟩

/-- Rule 614: those runs on the `medium-reviewer` with Sonnet. -/
def sonnetReviews : Rule where
  number := 614
  keyword := .must
  domain := .tasks
  formula := ev agentCall ∧ₗ atom runsLoopReview ⟹ ev sonnetReviewer

/-! Rules 615 to 622, the review loop. -/

def reconciliationOffHeading : Atom := ⟨"reconciliationOffHeading",
  "Does this edit write a reconciliation anywhere but under the round's `### Reconciliation` heading?", .edit⟩
def reconciliationIncomplete : Atom := ⟨"reconciliationIncomplete",
  "Does this reconciliation leave a finding unconfirmed or unrefuted with evidence, or a missed open finding unclassified, or make a second pass over the list?", .edit⟩
def resumesOpenReviewer : Link := ⟨"resumesOpenReviewer",
  "Does this message resume the open reviewer with the enumerated review's output, the list and the ledgers, for the anchored reconciliation?"⟩

/-- Rule 615: the reconciliation under its heading, by the resumed open reviewer. -/
def reconciliation : Rule where
  number := 615
  keyword := .must
  domain := .tasks
  formula :=
    never (ev reviewFileEdit ∧ₗ atom reconciliationOffHeading) ∧ₗ
    (ev reviewFileEdit ∧ₗ atom writesReconciliation ⟹
      ¬ₗ atom reconciliationIncomplete ∧ₗ once (ev sendMessage ∧ₗ link resumesOpenReviewer))

def assessesEveryFinding : Link := ⟨"assessesEveryFinding",
  "Does this edit record the agent's own assessment of every finding of the anchored reconciliation under the bar?"⟩

/-- Rule 616: every finding assessed by the writer after the reconciliation. -/
def assessFindings : Rule where
  number := 616
  keyword := .must
  domain := .tasks
  formula := ev reviewFileEdit ∧ₗ atom writesReconciliation ⟹
    anytime (ev reviewFileEdit ∧ₗ link assessesEveryFinding)

def classifiesMisses : Atom := ⟨"classifiesMisses",
  "Does this Coverage paragraph classify each miss as a coverage miss or an execution miss?", .edit⟩

/-- Rule 617: misses classified in a `Coverage.` paragraph with its three labels. -/
def coverageParagraphRule : Rule where
  number := 617
  keyword := .must
  domain := .tasks
  formula :=
    (ev reviewFileEdit ∧ₗ atom writesReconciliation ⟹ anytime (ev coverageParagraph)) ∧ₗ
    (ev coverageParagraph ⟹ atom classifiesMisses)

def roundWithoutOpenReview : Atom := ⟨"roundWithoutOpenReview",
  "Does this run make a review round without the open review?", .call⟩
def dropsOpenReview : Atom := ⟨"dropsOpenReview",
  "Does this message from the user decide, on several changes' records, to drop the open review?", .user⟩

/-- Rule 618: the open review stays unless the user drops it. -/
def keepOpenReview : Rule where
  number := 618
  keyword := .mustNot
  domain := .tasks
  formula := ev reviewerRun ∧ₗ atom roundWithoutOpenReview ⟹ once (ev user ∧ₗ atom dropsOpenReview)

def startsNewRound : Atom := ⟨"startsNewRound", "Does this reviewer run start a new review round?", .call⟩

/-- Rule 619: fixes rechecked by the resumed enumerated reviewer between rounds. -/
def recheckBetweenRounds : Rule where
  number := 619
  keyword := .must
  domain := .tasks
  formula := ev reviewerRun ∧ₗ atom startsNewRound ∧ₗ once (ev editing ∧ₗ atom fixesReviewFinding) ⟹
    since (ev sendMessage ∧ₗ link rechecksFixes) (ev editing ∧ₗ atom fixesReviewFinding)

def recordsFinalReviewFailure : Atom := ⟨"recordsFinalReviewFailure",
  "Does this edit record a Failure in the final fresh review?", .edit⟩
def downgradesWithoutRejected : Atom := ⟨"downgradesWithoutRejected",
  "Does this edit downgrade a raw Failure without a nested `Rejected:` giving the reason?", .edit⟩
def freshReviewAfterFix : Link := ⟨"freshReviewAfterFix",
  "Is this reviewer run a fresh review following the fix of the anchored Failure?"⟩

/-- Rule 620: a final-review Failure fixed, rechecked and followed by another fresh review. -/
def finalFailureFixed : Rule where
  number := 620
  keyword := .must
  domain := .tasks
  formula :=
    (ev reviewFileEdit ∧ₗ atom recordsFinalReviewFailure ⟹
      eventually (ev editing ∧ₗ atom fixesReviewFinding) ∧ₗ
      eventually (ev sendMessage ∧ₗ link rechecksFixes) ∧ₗ
      eventually (ev reviewerRun ∧ₗ link freshReviewAfterFix)) ∧ₗ
    never (ev reviewFileEdit ∧ₗ atom downgradesWithoutRejected)

def fixesCleanNoteOnly : Atom := ⟨"fixesCleanNoteOnly",
  "Does this edit fix a clean round's note while changing no code (a commit message, a description)?", .edit⟩
def freshReviewOfNoteFix : Link := ⟨"freshReviewOfNoteFix",
  "Is this reviewer run a fresh review made for the anchored note fix alone?"⟩

/-- Rule 621: a note fix changing no code gets the recheck alone. -/
def noteFixRecheck : Rule where
  number := 621
  keyword := .must
  domain := .tasks
  formula := ev editing ∧ₗ atom fixesCleanNoteOnly ⟹
    eventually (ev sendMessage ∧ₗ link rechecksFixes) ∧ₗ
    ¬ₗ eventually (ev reviewerRun ∧ₗ link freshReviewOfNoteFix)


/-- Rule 622: ledgers kept current with `ledger_at_tip.py` and `reader_check.py`. -/
def ledgersCurrent : Rule where
  number := 622
  keyword := .should
  domain := .tasks
  formula := ev requestAdd ∧ₗ atom requestsPush ⟹
    (once (ev ledgerAtTip) ∧ₗ once (ev readerCheck)) ∨ₗ atom justified

/-! Rules 623 to 658, later cycles. -/

/-- Rule 623: Theory building updated in the cycle before any implementation edit. -/
def theoryFirstEachCycle : Rule where
  number := 623
  keyword := .must
  domain := .tasks
  formula := ev editing ∧ₗ atom implementationEdit ⟹
    since (ev planEdit ∧ₗ atom editsTheory) (ev taskCheckpoint)

def findingChangesPlan : Atom := ⟨"findingChangesPlan",
  "Does this text report a finding that changes the plan?", .any⟩
def updatesPathFor : Link := ⟨"updatesPathFor",
  "Does this edit change the Path for the finding the anchored text reports?"⟩

/-- Rule 624: the Path updated for a finding, and the status set each cycle. -/
def pathAndStatus : Rule where
  number := 624
  keyword := .must
  domain := .tasks
  formula :=
    (ev agentText ∧ₗ atom findingChangesPlan ⟹ eventually (ev planEdit ∧ₗ link updatesPathFor)) ∧ₗ
    (ev taskCheckpoint ⟹ since (ev statusSet) (ev taskCheckpoint))

def aboutObjectsOfEdit : Link := ⟨"aboutObjectsOfEdit",
  "Does this `theory_check.py --about` run name the design objects the anchored edit touches?"⟩

/-- Rule 625: the entries about an object read with `--about` before building on it. -/
def readEntriesAbout : Rule where
  number := 625
  keyword := .must
  domain := .tasks
  formula := ev editing ∧ₗ atom implementationEdit ⟹ once (ev theoryCheckAbout ∧ₗ link aboutObjectsOfEdit)

def runsPerSubstep : Atom := ⟨"runsPerSubstep",
  "Does this call run the suite, a mutation batch or a checkpoint for one substep where independent substeps could share one?", .call⟩

/-- Rule 626: independent substeps batched into one run of each. -/
def batchSubsteps : Rule where
  number := 626
  keyword := .should
  domain := .tasks
  formula := ev anyCall ∧ₗ atom runsPerSubstep ⟹ atom justified

def findsDefect : Atom := ⟨"findsDefect", "Does this text report a defect just found?", .any⟩
def recordsDefect : Link := ⟨"recordsDefect",
  "Does this edit write the theory entry of the defect the anchored text reports?"⟩

/-- Rule 627: a defect's theory entry written as it is found. -/
def defectEntryAtOnce : Rule where
  number := 627
  keyword := .must
  domain := .tasks
  formula := ev agentText ∧ₗ atom findsDefect ⟹ eventually (ev planEdit ∧ₗ link recordsDefect)

def fixesMrFinding : Atom := ⟨"fixesMrFinding", "Does this commit fix a finding of an MR review round?", .call⟩
def testsThisFix : Link := ⟨"testsThisFix",
  "Is this passing result the tests of the fix the anchored commit makes?"⟩

/-- Rule 628: an MR round's fixes as fixups, each tested as made, then one fold. -/
def mrFixesBatch : Rule where
  number := 628
  keyword := .must
  domain := .tasks
  formula :=
    (ev gitCommit ∧ₗ atom fixesMrFinding ⟹ ev fixupCommit) ∧ₗ
    (ev fixupCommit ⟹ once (ev passingResult ∧ₗ link testsThisFix)) ∧ₗ
    (ev autosquash ⟹ ¬ₗ since (ev autosquash) (ev reviewerRun))

def fixupLinesChangedLater : Atom := ⟨"fixupLinesChangedLater",
  "Does this fixup commit change lines a later commit of the branch changes?", .call⟩

/-- Rule 629: a fix whose lines a later commit changes is made at an edit stop. -/
def editStopFix : Rule where
  number := 629
  keyword := .must
  domain := .tasks
  formula := never (ev fixupCommit ∧ₗ atom fixupLinesChangedLater)

def reportsTheoryStable : Link := ⟨"reportsTheoryStable",
  "Is this result a `tools/task_index.py stable` run reporting stable the theory of the anchored edit's task?"⟩

/-- Rule 630: implementation from a ready theory. -/
def readyTheory : Rule where
  number := 630
  keyword := .must
  domain := .tasks
  formula := ev editing ∧ₗ atom implementationEdit ⟹ once (ev passingResult ∧ₗ link reportsTheoryStable)

def addsEntryOfOtherKind : Atom := ⟨"addsEntryOfOtherKind",
  "Does this edit add a Theory building entry recording neither a wrong decision, an undecided user-visible behaviour, nor a choice with a real trade-off?", .edit⟩

/-- Rule 631: during execution, only three kinds of new theory entry. -/
def executionEntries : Rule where
  number := 631
  keyword := .must
  domain := .tasks
  formula := never (ev planEdit ∧ₗ atom addsEntryOfOtherKind ∧ₗ once (ev editing ∧ₗ atom implementationEdit))

def recordsBuildShape : Atom := ⟨"recordsBuildShape",
  "Does this edit record in the theory how a decided thing is built (an interface, a name, a record's shape)?", .edit⟩
def commitsBuiltDecision : Atom := ⟨"commitsBuiltDecision",
  "Does this commit build a decided thing whose interface, names or record shape its message leaves unstated?", .call⟩

/-- Rule 632: how a decided thing is built goes in the commit message, not the theory. -/
def buildShapeInCommit : Rule where
  number := 632
  keyword := .must
  domain := .tasks
  formula := never (ev planEdit ∧ₗ atom recordsBuildShape) ∧ₗ never (ev gitCommit ∧ₗ atom commitsBuiltDecision)

def addsSeveralEntriesForIncrement : Atom := ⟨"addsSeveralEntriesForIncrement",
  "Does this edit add several new theory entries an increment needs?", .edit⟩
def readsIncrementPart : Link := ⟨"readsIncrementPart",
  "Does this read take, in one pass, the part of the theory the anchored edit's increment touches?"⟩

/-- Rule 633: several entries for an increment decided together after one reread of its part. -/
def entriesTogether : Rule where
  number := 633
  keyword := .must
  domain := .tasks
  formula := ev planEdit ∧ₗ atom addsSeveralEntriesForIncrement ⟹ once (ev planRead ∧ₗ link readsIncrementPart)

def waitsForUser : Atom := ⟨"waitsForUser", "Does this reply stop work to wait for the user?", .reply⟩
def entryNamesMissingDecisions : Atom := ⟨"entryNamesMissingDecisions",
  "Does the entry this call appends say which decisions were missing?", .call⟩

/-- Rule 634: under a goal to finish, no waiting, and the entry names the missing decisions. -/
def finishGoalKeepsWorking : Rule where
  number := 634
  keyword := .must
  domain := .tasks
  formula :=
    never (ev reply ∧ₗ atom waitsForUser ∧ₗ atom underFinishGoal) ∧ₗ
    (ev entryAppend ∧ₗ atom underFinishGoal ⟹ atom entryNamesMissingDecisions)

def writesEvidenceProse : Atom := ⟨"writesEvidenceProse",
  "Does this edit write a prose account of its own into evidence under research/results/?", .edit⟩
def retellsEntry : Atom := ⟨"retellsEntry",
  "Does this commit's message retell the cycle's notebook entry?", .call⟩

/-- Rule 635: evidence without prose of its own; commit messages don't retell the entry. -/
def evidenceWithoutProse : Rule where
  number := 635
  keyword := .must
  domain := .tasks
  formula := never (ev editing ∧ₗ atom writesEvidenceProse) ∧ₗ never (ev gitCommit ∧ₗ atom retellsEntry)

def leavesStaleStatus : Atom := ⟨"leavesStaleStatus",
  "Does this checkpoint leave a status text (Where we stand, Proposed next step, the Path's status, the record's note) saying what is no longer true in a way that matters to the next decision?", .call⟩
def changesStatusNeedlessly : Atom := ⟨"changesStatusNeedlessly",
  "Does this edit change a status text whose statement is still true in every way that matters?", .edit⟩

/-- Rule 636: status text changed when it stops being true in a way that matters, else left. -/
def statusText : Rule where
  number := 636
  keyword := .must
  domain := .tasks
  formula := never (ev taskCheckpoint ∧ₗ atom leavesStaleStatus) ∧ₗ never (ev editing ∧ₗ atom changesStatusNeedlessly)

/-- Rule 637: `cycle_numbers.py --target` before each entry. -/
def cycleNumbersFirst : Rule where
  number := 637
  keyword := .must
  domain := .tasks
  formula := ev entryAppend ⟹ since (ev cycleNumbers) (ev entryAppend)

def entryHasProcess : Atom := ⟨"entryHasProcess",
  "Does the entry this call appends hold a paragraph starting <strong>Process.</strong> weighing wall-clock time, tokens, quality and friction, each with evidence?", .call⟩

/-- Rule 638: a Process paragraph weighing the four. -/
def processParagraph : Rule where
  number := 638
  keyword := .must
  domain := .tasks
  formula := ev entryAppend ⟹ atom entryHasProcess

def correctsAgent : Atom := ⟨"correctsAgent",
  "Does this message from the user correct the agent's work or how it works?", .user⟩
def namesCheckPerCorrection : Atom := ⟨"namesCheckPerCorrection",
  "Does the entry this call appends name, for each user correction of the cycle, the check that now finds its class?", .call⟩

/-- Rule 639: each correction with the check that now finds its class. -/
def correctionCheck : Rule where
  number := 639
  keyword := .must
  domain := .tasks
  formula := ev entryAppend ∧ₗ since (ev user ∧ₗ atom correctsAgent) (ev entryAppend) ⟹
    atom namesCheckPerCorrection

def notNowOutside : Atom := ⟨"notNowOutside",
  "Does this queued build's `Not now:` name what outside the agent's work stops it (an answer, an approval, an install, an access, another team, a merge, a running job)?", .call⟩
def identifiesBoundedFix : Atom := ⟨"identifiesBoundedFix",
  "Does this text identify a clear, bounded fix of the process?", .any⟩
def commitsFixApart : Link := ⟨"commitsFixApart",
  "Does this commit hold the fix the anchored text identifies, apart from the task's work?"⟩

/-- Rule 640: a bounded fix made and committed apart in the cycle; a build queued only with an
outside `Not now:`. -/
def boundedFixNow : Rule where
  number := 640
  keyword := .must
  domain := .tasks
  formula :=
    (ev agentText ∧ₗ atom identifiesBoundedFix ⟹
      eventually (ev gitCommit ∧ₗ link commitsFixApart) ∨ₗ eventually (ev taskCheckpoint ∧ₗ link commitsFixApart)) ∧ₗ
    (ev queueAddBuild ⟹ atom notNowOutside)

def mistakeRecursWhileQueued : Atom := ⟨"mistakeRecursWhileQueued",
  "Does this text report a mistake recurring while the build queued against it waits?", .any⟩
def buildsQueuedPrevention : Link := ⟨"buildsQueuedPrevention",
  "Does this edit build the queued prevention of the mistake the anchored text reports?"⟩

/-- Rule 641: a recurring mistake makes its queued build the next work. -/
def recurrenceBuildsNext : Rule where
  number := 641
  keyword := .must
  domain := .tasks
  formula := ev agentText ∧ₗ atom mistakeRecursWhileQueued ⟹
    eventually (ev editing ∧ₗ link buildsQueuedPrevention)

def tradesQualityForSpeed : Atom := ⟨"tradesQualityForSpeed",
  "Does this edit make a fix that saves time or tokens at a loss of quality?", .edit⟩

/-- Rule 642: no fix trading quality for time or tokens. -/
def qualityFirst : Rule where
  number := 642
  keyword := .mustNot
  domain := .tasks
  formula := never (ev editing ∧ₗ atom tradesQualityForSpeed)

def processInventsChange : Atom := ⟨"processInventsChange",
  "Does the entry this call appends invent a change to fill its Process paragraph?", .call⟩
def auditsForProcess : Atom := ⟨"auditsForProcess",
  "Does this call run a wider framework audit to fill a Process paragraph?", .call⟩

/-- Rule 643: no invented change and no wider audit for the Process paragraph. -/
def noInventedProcess : Rule where
  number := 643
  keyword := .mustNot
  domain := .tasks
  formula := never (ev entryAppend ∧ₗ atom processInventsChange) ∧ₗ never (ev anyCall ∧ₗ atom auditsForProcess)

def preventionFollowsProcess : Atom := ⟨"preventionFollowsProcess",
  "Does the entry this call appends follow its Process paragraph with a <strong>Prevention.</strong> paragraph naming the committed check, rule or queued build for each mistake, or why none applies, ending the assessment?", .call⟩

/-- Rule 644: Process followed by Prevention. -/
def preventionParagraph : Rule where
  number := 644
  keyword := .must
  domain := .tasks
  formula := ev entryAppend ⟹ atom preventionFollowsProcess

def preventionHomeUnnamed : Atom := ⟨"preventionHomeUnnamed",
  "Does a Prevention or Meta paragraph this call writes name its change's home other than by a framework path or file name (a target repository's check by its path from the home directory)?", .call⟩
def homeIsTaskFile : Atom := ⟨"homeIsTaskFile",
  "Does a Prevention or Meta paragraph this call writes name a task's files or archived results as its change's home?", .call⟩

/-- Rule 645: a Prevention or Meta home named by its path. -/
def homeByPath : Rule where
  number := 645
  keyword := .must
  domain := .tasks
  formula := never ((ev entryAppend ∨ₗ ev reviewFileEdit) ∧ₗ atom preventionHomeUnnamed)

/-- Rule 646: no task file as a Prevention or Meta home. -/
def noTaskFileHome : Rule where
  number := 646
  keyword := .mustNot
  domain := .tasks
  formula := never ((ev entryAppend ∨ₗ ev reviewFileEdit) ∧ₗ atom homeIsTaskFile)

def checkpointsByHand : Atom := ⟨"checkpointsByHand",
  "Does this commit make a task cycle's checkpoint (its notebook entry and records) by hand rather than through tools/task_checkpoint.py?", .call⟩

/-- Rule 647: the checkpoint through `task_checkpoint.py`. -/
def checkpointTool : Rule where
  number := 647
  keyword := .must
  domain := .tasks
  formula := never (ev gitCommit ∧ₗ atom checkpointsByHand)

def carriesStandInReview : Atom := ⟨"carriesStandInReview",
  "Does this result carry a stand-in review's objections?", .result⟩
def answersStandInReview : Atom := ⟨"answersStandInReview",
  "Does the entry this checkpoint commits hold `Review.` and `Meta.` paragraphs saying what became of each objection of the last stand-in review?", .call⟩

/-- Rule 648: an unanswered stand-in review answered in the next entry. -/
def answerStandIn : Rule where
  number := 648
  keyword := .must
  domain := .tasks
  formula := ev taskCheckpoint ∧ₗ since (ev passingResult ∧ₗ atom carriesStandInReview) (ev taskCheckpoint) ⟹
    atom answersStandInReview

def breaksGitRules : Atom := ⟨"breaksGitRules",
  "Does this git command break the engineering-discipline skill's git rules (commits split by logical line, history cleanup for an MR, a backup before a rewrite, no attribution)?", .call⟩

/-- Rule 649: the step's git operations under the skill's git rules. -/
def gitUnderSkill : Rule where
  number := 649
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev gitAny ∧ₗ atom breaksGitRules)

/-- Rule 650: the plan, entry and task record committed locally with the work. -/
def commitRecords : Rule where
  number := 650
  keyword := .must
  domain := .tasks
  formula := ev planEdit ⟹ eventually (ev gitCommit ∨ₗ ev taskCheckpoint)

def fixesProse : Atom := ⟨"fixesProse", "Does this edit fix prose a review found false?", .edit⟩
def removesFalseStatement : Atom := ⟨"removesFalseStatement",
  "Does this edit remove the false statement, replacing it only where its audience uses the information?", .edit⟩
def growsProse : Atom := ⟨"growsProse", "Does this edit make the prose longer?", .edit⟩
def explainsGrowth : Link := ⟨"explainsGrowth", "Does this text say why the anchored prose fix grows the prose?"⟩

/-- Rule 651: a prose fix removes the false statement, and a growing one says why. -/
def proseFixShrinks : Rule where
  number := 651
  keyword := .must
  domain := .tasks
  formula := ev editing ∧ₗ atom fixesProse ⟹
    atom removesFalseStatement ∧ₗ (atom growsProse ⟹ anytime (ev agentText ∧ₗ link explainsGrowth))

def proposesNewLoopOrRule : Atom := ⟨"proposesNewLoopOrRule",
  "Does this reply propose a new loop or rule?", .reply⟩
def searchesForRuleToExtend : Link := ⟨"searchesForRuleToExtend",
  "Does this call search the protocol's loops section and the protocol for a loop or rule the anchored proposal could extend?"⟩

/-- Rule 652: the protocol searched for a loop or rule to extend before a new one. -/
def extendExistingLoop : Rule where
  number := 652
  keyword := .must
  domain := .tasks
  formula := ev reply ∧ₗ atom proposesNewLoopOrRule ⟹
    once ((ev reading ∨ₗ ev searchCall) ∧ₗ link searchesForRuleToExtend)

/-- Rule 653: the applied loops named on a `Loops applied:` line. -/
def loopsAppliedLine : Rule where
  number := 653
  keyword := .must
  domain := .tasks
  formula := ev reply ∧ₗ atom givesGoalPrompt ⟹ ev loopsApplied

def startsRoundRecord : Atom := ⟨"startsRoundRecord",
  "Does this edit start a review round's record?", .edit⟩
def recordsThisRound : Link := ⟨"recordsThisRound",
  "Does this edit record the anchored reviewer run's round in a review file of the task's directory?"⟩

/-- Rule 654: every round in a `*REVIEW*.md`, written with `record_skeleton.py`. -/
def roundsRecorded : Rule where
  number := 654
  keyword := .must
  domain := .tasks
  formula :=
    (ev reviewerRun ∧ₗ atom loopRound ⟹ eventually (ev reviewFileEdit ∧ₗ link recordsThisRound)) ∧ₗ
    (ev reviewFileEdit ∧ₗ atom startsRoundRecord ⟹ once (ev recordSkeleton))

def findingWithoutClass : Atom := ⟨"findingWithoutClass",
  "Does this edit record a finding with neither a `Class:` nor a `Rejected:` reason?", .edit⟩

/-- Rule 655: each finding with a class or a rejection. -/
def findingClass : Rule where
  number := 655
  keyword := .must
  domain := .tasks
  formula := never (ev reviewFileEdit ∧ₗ atom findingWithoutClass)

def classedRoundLacksPreventionMeta : Atom := ⟨"classedRoundLacksPreventionMeta",
  "Does this edit leave a round with a class without a `Prevention.` and a `Meta.`, each naming by path the file, skill, check, hook or tool holding its change?", .edit⟩

/-- Rule 656: a round with a class writes Prevention and Meta, each with its home's path. -/
def classedRoundPrevention : Rule where
  number := 656
  keyword := .must
  domain := .tasks
  formula := never (ev reviewFileEdit ∧ₗ atom classedRoundLacksPreventionMeta)

def recurringClassUnmarked : Atom := ⟨"recurringClassUnmarked",
  "Does this edit record a class an earlier round held without `Recurrence:` naming that round?", .edit⟩
def recurrenceWithoutStrengthened : Atom := ⟨"recurrenceWithoutStrengthened",
  "Does this edit mark a `Recurrence:` whose Prevention doesn't say what was `Strengthened:`?", .edit⟩

/-- Rule 657: a recurring class marked, its Prevention saying what was strengthened. -/
def recurrenceMarked : Rule where
  number := 657
  keyword := .must
  domain := .tasks
  formula :=
    never (ev reviewFileEdit ∧ₗ atom recurringClassUnmarked) ∧ₗ
    never (ev reviewFileEdit ∧ₗ atom recurrenceWithoutStrengthened)

def findingWithoutOrigin : Atom := ⟨"findingWithoutOrigin",
  "Does this edit record a finding without its origin after `Origin:`?", .edit⟩

/-- Rule 658: each finding's origin named. -/
def findingOrigin : Rule where
  number := 658
  keyword := .must
  domain := .tasks
  formula := never (ev reviewFileEdit ∧ₗ atom findingWithoutOrigin)

/-! Rules 659 to 670, the queue and outside repositories. -/

def leavesWorkUndone : Atom := ⟨"leavesWorkUndone",
  "Does this text leave undone some work that came up?", .any⟩
def queuesThatWork : Link := ⟨"queuesThatWork",
  "Does this call queue the work the anchored text leaves undone?"⟩

/-- Rule 659: work left undone queued at once, a check or build with `Problem:` and `Must:`. -/
def queueUndoneWork : Rule where
  number := 659
  keyword := .must
  domain := .tasks
  formula :=
    (ev agentText ∧ₗ atom leavesWorkUndone ⟹ eventually (ev queueAdd ∧ₗ link queuesThatWork)) ∧ₗ
    (ev queueCheckOrBuild ⟹ ev problemAndMust)

def queuesLargeBuildWhole : Atom := ⟨"queuesLargeBuildWhole",
  "Does this call queue a large build whole, with no smaller part of it that acts at the step built first?", .call⟩

/-- Rule 660: the smallest part of a large build that acts at the step first. -/
def smallestPartFirst : Rule where
  number := 660
  keyword := .should
  domain := .tasks
  formula := ev queueAddBuild ∧ₗ atom queuesLargeBuildWhole ⟹ atom justified

def leavesUnplacedWork : Atom := ⟨"leavesUnplacedWork",
  "Does the entry this call appends hold a sentence leaving work for later without naming its place (queued, a request, the next step, or dropped and why)?", .call⟩

/-- Rule 662: no sentence leaving work for later without its place. -/
def placedWork : Rule where
  number := 662
  keyword := .mustNot
  domain := .tasks
  formula := never (ev entryAppend ∧ₗ atom leavesUnplacedWork)

def queuesBlocker : Atom := ⟨"queuesBlocker",
  "Does this call queue a thing the task is blocked on?", .call⟩
def findsTaskBlocker : Atom := ⟨"findsTaskBlocker",
  "Does this text find a thing the task is blocked on?", .any⟩

/-- Rule 663: a blocker is a task of its own, the original waiting for it, never a queue item. -/
def blockerIsTask : Rule where
  number := 663
  keyword := .must
  domain := .tasks
  formula :=
    never (ev queueAdd ∧ₗ atom queuesBlocker) ∧ₗ
    (ev agentText ∧ₗ atom findsTaskBlocker ⟹ eventually (ev taskNew) ∧ₗ eventually (ev setWaitsForBlocked))

def requestBlocksTask : Atom := ⟨"requestBlocksTask",
  "Does this request leave the task blocked on the user?", .call⟩

/-- Rule 664: a task blocked on the user goes blocked with its request. -/
def blockedOnUser : Rule where
  number := 664
  keyword := .must
  domain := .tasks
  formula := ev requestAdd ∧ₗ atom requestBlocksTask ⟹ anytime (ev setBlocked)

def autonomousCycle : Atom := ⟨"autonomousCycle",
  "Is the entry this call appends for a cycle the agent chose its work for autonomously?", .call⟩
def statesWhyWorkTaken : Atom := ⟨"statesWhyWorkTaken",
  "Does the entry this call appends say why it took the work it took?", .call⟩
def passesOverUnblockedTask : Atom := ⟨"passesOverUnblockedTask",
  "Does the entry this call appends take the queue's head or another item while an unblocked task waited?", .call⟩

/-- Rule 665: autonomously, an unblocked task first, else the queue's head, saying why. -/
def autonomousOrder : Rule where
  number := 665
  keyword := .must
  domain := .tasks
  formula := ev entryAppend ∧ₗ atom autonomousCycle ⟹
    atom statesWhyWorkTaken ∧ₗ ¬ₗ atom passesOverUnblockedTask

def developsUserPick : Atom := ⟨"developsUserPick",
  "Does the entry this call appends develop a queue item the user picked?", .call⟩
def hasPickedTagAndQuote : Atom := ⟨"hasPickedTagAndQuote",
  "Does the entry this call appends carry data-picked=\"user\" and a <strong>Picked.</strong> paragraph quoting the user's words?", .call⟩

/-- Rule 666: a user pick tagged and quoted. -/
def userPickTagged : Rule where
  number := 666
  keyword := .must
  domain := .tasks
  formula := ev entryAppend ∧ₗ atom developsUserPick ⟹ atom hasPickedTagAndQuote

def closesWaitingItem : Atom := ⟨"closesWaitingItem",
  "Does this call close a queue item that waits on the user's input?", .call⟩
def itemWaitsOnUser : Atom := ⟨"itemWaitsOnUser",
  "Does the entry this call appends pass over a queue item that needs the user's input?", .call⟩
def followUpWaiting : Atom := ⟨"followUpWaiting",
  "Does the entry this call appends end that item's follow-up `Waiting:` with a link to the task's USER_REQUESTS.md and the item (or the question)?", .call⟩

/-- Rule 667: an item waiting on the user stays queued, its follow-up `Waiting:`. -/
def waitingItemQueued : Rule where
  number := 667
  keyword := .must
  domain := .tasks
  formula :=
    never (ev queueClose ∧ₗ atom closesWaitingItem) ∧ₗ
    (ev entryAppend ∧ₗ atom itemWaitsOnUser ⟹ atom followUpWaiting)

def idlesOnWaitingItem : Atom := ⟨"idlesOnWaitingItem",
  "Does this reply stop work because an item waits, while other unblocked work remains?", .reply⟩

/-- Rule 668: the next unblocked thing while an item waits. -/
def nextUnblocked : Rule where
  number := 668
  keyword := .must
  domain := .tasks
  formula := never (ev reply ∧ₗ atom idlesOnWaitingItem)

def externalEditBreaksConventions : Atom := ⟨"externalEditBreaksConventions",
  "Does this edit in a repository outside the workspace break that repository's conventions or the branch's workplace rules, following the workspace's instead?", .edit⟩

/-- Rule 669: an outside repository's conventions, not this workspace's. -/
def repositoryConventions : Rule where
  number := 669
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom externalEditBreaksConventions)

def externalCommit : Atom := ⟨"externalCommit",
  "Is this commit in a repository outside the workspace?", .call⟩
def titleBreaksScopePrefix : Atom := ⟨"titleBreaksScopePrefix",
  "Does this commit's title break the repository's scope-prefix convention or the form of the branch's other titles?", .call⟩
def readsTrunkTitles : Link := ⟨"readsTrunkTitles",
  "Does this call read the trunk's commit titles of the anchored commit's repository?"⟩

/-- Rule 670: the trunk's scope-prefix convention, read from its history, across the branch. -/
def scopePrefixTitles : Rule where
  number := 670
  keyword := .must
  domain := .softwareEngineering
  formula := ev gitCommit ∧ₗ atom externalCommit ⟹
    once (ev gitLog ∧ₗ link readsTrunkTitles) ∧ₗ ¬ₗ atom titleBreaksScopePrefix

/-! Rules 671 to 676, before asking the user. -/

def asksMinorDetail : Atom := ⟨"asksMinorDetail",
  "Does this event put to the user a minor detail with no real trade-off for them?", .any⟩
def decidesMinorDetail : Atom := ⟨"decidesMinorDetail",
  "Does this text decide a minor detail?", .any⟩
def recordsOwnDecision : Link := ⟨"recordsOwnDecision",
  "Does this edit record in Theory building, as the agent's decision, the detail the anchored text decides?"⟩
def mentionsDecision : Link := ⟨"mentionsDecision",
  "Does this reply's summary mention the decision the anchored text makes?"⟩

/-- Rule 671: minor details decided, recorded as decisions and mentioned. -/
def decideMinorDetails : Rule where
  number := 671
  keyword := .must
  domain := .tasks
  formula :=
    never ((ev requestAdd ∨ₗ ev reply) ∧ₗ atom asksMinorDetail) ∧ₗ
    (ev agentText ∧ₗ atom decidesMinorDetail ⟹
      anytime (ev planEdit ∧ₗ link recordsOwnDecision) ∧ₗ anytime (ev reply ∧ₗ link mentionsDecision))

def recommendsFixLeftUnmade : Atom := ⟨"recommendsFixLeftUnmade",
  "Does this reply recommend a fix within the task's scope that it hasn't made?", .reply⟩
def makesRecommendedFix : Atom := ⟨"makesRecommendedFix",
  "Is this edit a fix the agent recommended?", .edit⟩

/-- Rule 672: a recommended fix in scope made in the same turn, before the user's next message. -/
def makeRecommendedFix : Rule where
  number := 672
  keyword := .must
  domain := .tasks
  formula := ev user ⟹
    ¬ₗ since (ev reply ∧ₗ atom recommendsFixLeftUnmade) (ev editing ∧ₗ atom makesRecommendedFix)

def bringsNonUserChoice : Atom := ⟨"bringsNonUserChoice",
  "Does this event bring the user a choice that isn't theirs (not scope, policy, who may do what, a trade-off they would weigh, anything outward-facing)?", .any⟩

/-- Rule 673: only the user's choices go to the user. -/
def onlyUsersChoices : Rule where
  number := 673
  keyword := .must
  domain := .tasks
  formula := never ((ev requestAdd ∨ₗ ev reply) ∧ₗ atom bringsNonUserChoice)

def asksOnlyBecauseReviewerRaised : Atom := ⟨"asksOnlyBecauseReviewerRaised",
  "Does this request put to the user a question only because a reviewer raised it?", .call⟩

/-- Rule 674: a reviewer's question isn't the user's by being raised. -/
def reviewerQuestionNotUsers : Rule where
  number := 674
  keyword := .mustNot
  domain := .tasks
  formula := never (ev requestAdd ∧ₗ atom asksOnlyBecauseReviewerRaised)

def asksUserQuestion : Atom := ⟨"asksUserQuestion",
  "Does this reply ask the user a question that needs their answer?", .reply⟩
def agentCouldSettle : Atom := ⟨"agentCouldSettle",
  "Does this request ask what the agent could settle from evidence?", .call⟩
def requestHoldsQuestion : Link := ⟨"requestHoldsQuestion",
  "Does this request hold the question the anchored reply asks?"⟩

/-- Rule 675: a question for the user is a request first, `--users-because` where the agent
could settle it. -/
def questionIsRequest : Rule where
  number := 675
  keyword := .must
  domain := .tasks
  formula :=
    (ev reply ∧ₗ atom asksUserQuestion ⟹ once (ev requestAdd ∧ₗ link requestHoldsQuestion)) ∧ₗ
    (ev requestAdd ∧ₗ atom agentCouldSettle ⟹ ev usersBecause)

def endsTurnOnQuestion : Atom := ⟨"endsTurnOnQuestion",
  "Does this reply end the turn on an open question to the user?", .reply⟩

/-- Rule 676: the independent work done; a turn ends on a question only when all else waits on it. -/
def workAroundQuestion : Rule where
  number := 676
  keyword := .must
  domain := .tasks
  formula := ev reply ∧ₗ atom endsTurnOnQuestion ⟹ atom nothingUnblocked

/-! Rules 678 to 694, requests for someone else's action. -/

def needsOthersAction : Atom := ⟨"needsOthersAction",
  "Does this text find a step only someone else can take?", .any⟩
def ourPartReady : Atom := ⟨"ourPartReady",
  "Does this request go out with our part finished and its merge request ready to merge?", .call⟩
def earlyForSavingOfWork : Atom := ⟨"earlyForSavingOfWork",
  "Does this request go out early for a clear, significant saving of work, such as a design outline for review?", .call⟩

/-- Rule 678: a step for someone else is a request, sent with our part finished. -/
def othersStepIsRequest : Rule where
  number := 678
  keyword := .must
  domain := .tasks
  formula :=
    (ev agentText ∧ₗ atom needsOthersAction ⟹ eventually (ev requestToOthers)) ∧ₗ
    (ev requestToOthers ⟹ atom ourPartReady ∨ₗ atom earlyForSavingOfWork)

/-- Rule 679: reaching out early only for a significant saving. -/
def earlyOnlyForSaving : Rule where
  number := 679
  keyword := .should
  domain := .tasks
  formula := ev requestToOthers ∧ₗ ¬ₗ atom ourPartReady ⟹ atom earlyForSavingOfWork ∨ₗ atom justified

def bodySettlesEachStep : Atom := ⟨"bodySettlesEachStep",
  "Does this request settle for each step the access it needs, that we lack it, who holds it, whether it can be avoided or merged, whether the procedure is current, and whether one answer will do?", .call⟩

/-- Rule 680: each step settled before the request, our lack checked by a read-only attempt. -/
def settleEachStep : Rule where
  number := 680
  keyword := .must
  domain := .tasks
  formula := ev requestToOthers ⟹ atom bodySettlesEachStep ∧ₗ once (ev anyCall ∧ₗ link checksOurAccess)

def asksForHeldOrUncheckedAccess : Atom := ⟨"asksForHeldOrUncheckedAccess",
  "Does this request ask for a step whose access we hold, or whose lack nobody checked?", .call⟩

/-- Rule 681: no request for access we hold or never checked. -/
def noRequestForHeldAccess : Rule where
  number := 681
  keyword := .mustNot
  domain := .tasks
  formula := never (ev requestToOthers ∧ₗ atom asksForHeldOrUncheckedAccess)

def holderUnknown : Atom := ⟨"holderUnknown", "Does this request leave a step's holder unknown?", .call⟩
def addressesClosestHolder : Atom := ⟨"addressesClosestHolder",
  "Does this request address each step to the holder closest to the work?", .call⟩
def readsHolderSources : Link := ⟨"readsHolderSources",
  "Does this call read role assignments, owner or member lists, CODEOWNERS or commit history for a step of the anchored request?"⟩

/-- Rule 682: no unknown holder while the sources naming holders are unread; the closest holder
addressed. -/
def holderKnown : Rule where
  number := 682
  keyword := .mustNot
  domain := .tasks
  formula := ev requestToOthers ⟹
    (atom holderUnknown ⟹ once (ev anyCall ∧ₗ link readsHolderSources)) ∧ₗ atom addressesClosestHolder

def splitsWhereOneHolds : Atom := ⟨"splitsWhereOneHolds",
  "Does this request address several people where one holds every step's access?", .call⟩

/-- Rule 683: one person holding every step's access gets the whole request. -/
def oneHolder : Rule where
  number := 683
  keyword := .must
  domain := .tasks
  formula := never (ev requestToOthers ∧ₗ atom splitsWhereOneHolds)

def saysWhyAlternativesNotTaken : Atom := ⟨"saysWhyAlternativesNotTaken",
  "Does this request say, for each route around a step that needs no access we lack, why it isn't taken?", .call⟩
def readsTodaysPath : Link := ⟨"readsTodaysPath",
  "Does this call read how the system performs a step of the anchored request today for its existing instances?"⟩

/-- Rule 684: today's path read, routes around looked for, each refusal said. -/
def todaysPath : Rule where
  number := 684
  keyword := .must
  domain := .tasks
  formula := ev requestToOthers ⟹ once (ev anyCall ∧ₗ link readsTodaysPath) ∧ₗ atom saysWhyAlternativesNotTaken

def duplicatesAccessStep : Atom := ⟨"duplicatesAccessStep",
  "Does this request hold two steps needing the same access to the same resource?", .call⟩

/-- Rule 685: two steps of one access to one resource are one. -/
def mergeSameAccess : Rule where
  number := 685
  keyword := .must
  domain := .tasks
  formula := never (ev requestToOthers ∧ₗ atom duplicatesAccessStep)

def reliesOnDocProcedure : Atom := ⟨"reliesOnDocProcedure",
  "Does this request rely on a procedure taken from documentation?", .call⟩
def checksProcedureAgainstCode : Link := ⟨"checksProcedureAgainstCode",
  "Does this call check the anchored request's documented procedure against the current code or configuration?"⟩

/-- Rule 686: a documented procedure checked against current code first. -/
def procedureCurrent : Rule where
  number := 686
  keyword := .must
  domain := .tasks
  formula := ev requestToOthers ∧ₗ atom reliesOnDocProcedure ⟹
    once (ev anyCall ∧ₗ link checksProcedureAgainstCode)

def foldsFollowUps : Atom := ⟨"foldsFollowUps",
  "Does this request fold in the follow-up for each answer it could get?", .call⟩

/-- Rule 687: the follow-up for each possible answer folded in. -/
def oneAnswerDoes : Rule where
  number := 687
  keyword := .must
  domain := .tasks
  formula := ev requestToOthers ⟹ atom foldsFollowUps

def handsOverCommand : Atom := ⟨"handsOverCommand", "Does this request hand over a command to run?", .call⟩
def statesTested : Atom := ⟨"statesTested",
  "Does this request state under `Tested:` the stand-in the command ran on and its predicted output for each answer?", .call⟩
def runsCommandOnStandIn : Link := ⟨"runsCommandOnStandIn",
  "Does this call run the anchored request's command on the nearest stand-in we can reach?"⟩

/-- Rule 688: a handed command run first on the nearest stand-in, stated under `Tested:`. -/
def standInFirst : Rule where
  number := 688
  keyword := .must
  domain := .tasks
  formula := ev requestToOthers ∧ₗ atom handsOverCommand ⟹
    once (ev anyCall ∧ₗ link runsCommandOnStandIn) ∧ₗ atom statesTested

def handsAmbiguousCommand : Atom := ⟨"handsAmbiguousCommand",
  "Does this request hand over a command whose output two answers share, that reports a match without naming it, or whose answer needs a second question?", .call⟩

/-- Rule 689: no ambiguous command handed over. -/
def noAmbiguousCommand : Rule where
  number := 689
  keyword := .mustNot
  domain := .tasks
  formula := never (ev requestToOthers ∧ₗ atom handsAmbiguousCommand)

def asksOthersAction : Atom := ⟨"asksOthersAction",
  "Does this request ask for someone else's action?", .call⟩
def bodyHasStepLabels : Atom := ⟨"bodyHasStepLabels",
  "Does this request's body give prose context, then one top-level item per step with `Access needed:`, `Checked missing:`, `Held by:`, `Today:` and `Alternatives:`, then `Ours:`?", .call⟩

/-- Rule 690: a request to others in its format, through `--to-others`. -/
def requestFormat : Rule where
  number := 690
  keyword := .must
  domain := .tasks
  formula := ev requestAdd ∧ₗ atom asksOthersAction ⟹ ev requestToOthers ∧ₗ atom bodyHasStepLabels

def includesOursAloneStep : Atom := ⟨"includesOursAloneStep",
  "Does this request hold a step that is ours alone?", .call⟩

/-- Rule 691: a step ours alone belongs in the Path. -/
def oursInPath : Rule where
  number := 691
  keyword := .mustNot
  domain := .tasks
  formula := never (ev requestToOthers ∧ₗ atom includesOursAloneStep)

def offersRequestForForwarding : Atom := ⟨"offersRequestForForwarding",
  "Does this reply hand the user a request with an `Ours:` part to forward?", .reply⟩
def readiesThatRequest : Link := ⟨"readiesThatRequest",
  "Does this call mark ready the request the anchored reply hands over?"⟩

/-- Rule 692: our parts recorded done before a request with `Ours:` is forwarded. -/
def readyBeforeForwarding : Rule where
  number := 692
  keyword := .must
  domain := .tasks
  formula := ev reply ∧ₗ atom offersRequestForForwarding ⟹ once (ev requestReady ∧ₗ link readiesThatRequest)

def judgeRefusesRequest : Atom := ⟨"judgeRefusesRequest",
  "Is this result the request judge refusing a request?", .result⟩

/-- Rule 693: the requests judged once recorded, a refused one fixed with `request edit
--body-file`. -/
def judgeRequests : Rule where
  number := 693
  keyword := .must
  domain := .tasks
  formula :=
    (ev requestAdd ⟹ eventually (ev requestJudge)) ∧ₗ
    (ev passingResult ∧ₗ atom judgeRefusesRequest ⟹ eventually (ev requestEditBodyFile))

def mentionsRequest : Atom := ⟨"mentionsRequest", "Does this reply mention a request?", .reply⟩
def judgesMentionedRequest : Link := ⟨"judgesMentionedRequest",
  "Does this run judge the request the anchored reply mentions, in its current form?"⟩

/-- Rule 694: no mention of a request before it is judged. -/
def mentionAfterJudge : Rule where
  number := 694
  keyword := .mustNot
  domain := .tasks
  formula := ev reply ∧ₗ atom mentionsRequest ⟹ once (ev requestJudge ∧ₗ link judgesMentionedRequest)

/-! Rules 695 to 700, stopping and the artifact. -/

def openQuestionsLeft : Atom := ⟨"openQuestionsLeft",
  "Does the task this call closes still have an entry in Open questions?", .call⟩
def readsWholeBranch : Link := ⟨"readsWholeBranch",
  "Does this call read the whole branch or diff of the task the anchored call closes?"⟩

/-- Rule 695: a final pass, the whole diff read and every open question resolved, before done or
blocked. -/
def finalPass : Rule where
  number := 695
  keyword := .must
  domain := .tasks
  formula := ev setComplete ∨ₗ ev setBlocked ⟹
    once (ev anyCall ∧ₗ link readsWholeBranch) ∧ₗ ¬ₗ atom openQuestionsLeft

def artifactCompleteNothingOutstanding : Atom := ⟨"artifactCompleteNothingOutstanding",
  "Does the task this call closes as complete have its artifact complete, the final pass having found nothing outstanding?", .call⟩
def closingEntry : Link := ⟨"closingEntry",
  "Does this call append the entry closing the anchored call's task with the matching status (task complete, task blocked)?"⟩
def removesTaskParagraph : Link := ⟨"removesTaskParagraph",
  "Does this edit remove the anchored call's task paragraph from Where we stand?"⟩
def reportsArtifactLocation : Link := ⟨"reportsArtifactLocation",
  "Does this reply report the location of the artifact of the task the anchored call completes?"⟩

/-- Rule 696: done only with the artifact complete; the closing entry, status, paragraph, commit
and report. -/
def stopDone : Rule where
  number := 696
  keyword := .must
  domain := .tasks
  formula := ev setComplete ⟹
    atom artifactCompleteNothingOutstanding ∧ₗ anytime (ev entryAppend ∧ₗ link closingEntry) ∧ₗ
    anytime (ev editing ∧ₗ link removesTaskParagraph) ∧ₗ eventually (ev gitCommit ∨ₗ ev taskCheckpoint) ∧ₗ
    eventually (ev reply ∧ₗ link reportsArtifactLocation)

def everythingMovableDone : Atom := ⟨"everythingMovableDone",
  "Does the task this call sets blocked have everything movable without the user done and every item needing the user recorded as a request?", .call⟩
def reportsBlockers : Link := ⟨"reportsBlockers",
  "Does this reply report plainly the blockers of the task the anchored call sets blocked?"⟩

/-- Rule 697: blocked only with all else done and requested; the entry, status and report. -/
def stopBlocked : Rule where
  number := 697
  keyword := .must
  domain := .tasks
  formula := ev setBlocked ⟹
    atom everythingMovableDone ∧ₗ anytime (ev entryAppend ∧ₗ link closingEntry) ∧ₗ
    eventually (ev reply ∧ₗ link reportsBlockers)

def stopsTaskEarly : Atom := ⟨"stopsTaskEarly",
  "Does this reply stop work on a task for a finished cycle or a large next step while it is neither done nor fully blocked?", .reply⟩

/-- Rule 698: no stop after one cycle; cycles until done or blocked. -/
def keepCycling : Rule where
  number := 698
  keyword := .mustNot
  domain := .tasks
  formula := never (ev reply ∧ₗ atom stopsTaskEarly)

def unblockedStepRemains : Atom := ⟨"unblockedStepRemains",
  "Does the task this checkpoint is for have a Path step left that waits on no one?", .call⟩
def listsOwnWorkAsOpen : Atom := ⟨"listsOwnWorkAsOpen",
  "Does this reply list as open work that waits on no one else?", .reply⟩

/-- Rule 699: the next unblocked step started in the checkpoint's turn; only others' waits listed
open. -/
def nextStepSameTurn : Rule where
  number := 699
  keyword := .must
  domain := .tasks
  formula :=
    (ev user ⟹ ¬ₗ since (ev taskCheckpoint ∧ₗ atom unblockedStepRemains) (ev editing)) ∧ₗ
    never (ev reply ∧ₗ atom listsOwnWorkAsOpen)

def namesArtifactKind : Link := ⟨"namesArtifactKind",
  "Does this edit name, in the Path, the kind of artifact of the task the anchored call completes?"⟩

/-- Rule 700: the artifact's kind named in the Path before finishing. -/
def artifactKindNamed : Rule where
  number := 700
  keyword := .must
  domain := .tasks
  formula := ev setComplete ⟹ once (ev planEdit ∧ₗ link namesArtifactKind)

/-! The range's rules, and its MAY rules as theorems. -/

def rules : List Rule :=
  [frameworkPassFirst, taskBeforeLargeChange, rereadBeforePlan, rewrapTheory, checklistEveryEntry,
   ticketDepartureRequired, sharedObjectCheck, theoryCheckEachPass, theoryLoopWatched,
   filesOnBranches, everyGapOnePass, checkOwnOutput, userNeedIsRequest, passEndsWithReread,
   unchangedNeedsRead, carryEachClause, clauseTableForLongTheory, clauseTableStops, caseIds,
   answerTagsAndMembers, tagFormPairs, rowPartByPart, casesWithDecision, riskyIncrementsFirst,
   stepNeeds, nestedPathItems, membersUnderStep, oneArtifactPerStep, stepBounds, noDecisionInPath,
   referencesAfterMove, writerChecksPath, changedClausesRead, loopHasGoal, everyExitInCondition,
   noInventedCap, reportInConditionWords, noStepCountStatus, judgeRefusal, ideaStaysOpen,
   twoEndStates, capArtifact, roundRunsListed, runDependencies, boundedTrackedRuns, cleanEnd,
   capSized, noProcedureInCondition, departureAnnounced, excerptBrief, foldSmallRound,
   sonnetReviews, reconciliation, assessFindings, coverageParagraphRule, keepOpenReview,
   recheckBetweenRounds, finalFailureFixed, noteFixRecheck, ledgersCurrent, theoryFirstEachCycle,
   pathAndStatus, readEntriesAbout, batchSubsteps, defectEntryAtOnce, mrFixesBatch, editStopFix,
   readyTheory, executionEntries, buildShapeInCommit, entriesTogether, finishGoalKeepsWorking,
   evidenceWithoutProse, statusText, cycleNumbersFirst, processParagraph, correctionCheck,
   boundedFixNow, recurrenceBuildsNext, qualityFirst, noInventedProcess, preventionParagraph,
   homeByPath, noTaskFileHome, checkpointTool, answerStandIn, gitUnderSkill, commitRecords,
   proseFixShrinks, extendExistingLoop, loopsAppliedLine, roundsRecorded, findingClass,
   classedRoundPrevention, recurrenceMarked, findingOrigin, queueUndoneWork, smallestPartFirst,
   placedWork, blockerIsTask, blockedOnUser, autonomousOrder, userPickTagged, waitingItemQueued,
   nextUnblocked, repositoryConventions, scopePrefixTitles, decideMinorDetails, makeRecommendedFix,
   onlyUsersChoices, reviewerQuestionNotUsers, questionIsRequest, workAroundQuestion,
   othersStepIsRequest, earlyOnlyForSaving, settleEachStep, noRequestForHeldAccess, holderKnown,
   oneHolder, todaysPath, mergeSameAccess, procedureCurrent, oneAnswerDoes, standInFirst,
   noAmbiguousCommand, requestFormat, oursInPath, readyBeforeForwarding, judgeRequests,
   mentionAfterJudge, finalPass, stopDone, stopBlocked, keepCycling, nextStepSameTurn,
   artifactKindNamed]

/-- Rule 572 (MAY): stopping a pass at a gap that makes the rest of it meaningless keeps rule 571. -/
theorem r572_stop_at_voiding_gap : run everyGapOnePass (seq [.reply "stopping: this gap voids the pass"])
    [(Examples.atom stopsAtFirstGap 0, true), (Examples.atom gapVoidsPass 0, true),
     (Examples.atom bringsTheoryGaps 0, false), (Examples.atom leavesStaleTextUnfixed 0, false)] =
    .kept := by decide

/-- The permission reaches no further: stopping at a gap that doesn't void the pass breaks 571. -/
theorem r572_stop_at_other_gap : run everyGapOnePass (seq [.reply "stopping at this gap"])
    [(Examples.atom stopsAtFirstGap 0, true), (Examples.atom gapVoidsPass 0, false),
     (Examples.atom bringsTheoryGaps 0, false), (Examples.atom leavesStaleTextUnfixed 0, false)] =
    .broken := by decide

/-- Rule 661 (MAY): queuing a proposal with `--idea` keeps the queue rules 640, 659 and 660, with
nothing asked of a model. -/
theorem r661_idea_allowed :
    [boundedFixNow, queueUndoneWork, smallestPartFirst].all (fun r =>
      run r (seq [bash "python3 tools/lead_queue.py add notebook.html --idea i s 'weigh x'"]) [] ==
        .kept) = true := by decide

/-- A check or build queued without `Problem:` and `Must:` breaks rule 659, where an idea doesn't. -/
theorem r659_build_without_parts : run queueUndoneWork
    (seq [bash "python3 tools/lead_queue.py add notebook.html --check c s 'look at x'"]) [] = .broken := by
  decide

def permissions : List Nat := [572, 661]

end Rails.Ruleset.Range5
