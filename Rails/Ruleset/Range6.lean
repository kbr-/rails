import Rails.Rules
import Rails.Examples
import Rails.Witness

/-!
Rules 701 to 840 of `tasks/agents-on-rails/RULES.md`, the sample's 838 left out: the task
protocol's artifacts, test speed and queue settings (701 to 716), restoration and the research
discipline (717 to 756), goal progress, reviews and the notebook's metadata (757 to 806), worktrees,
merges and requests (807 to 821), the framework's rules on mistakes, instruction files and tools
(822 to 835), and the Claude-specific rules (836 to 840). The MAY rules 706 and 785 are theorems.
-/

namespace Rails.Ruleset.Range6
open Rails Formula Ruleset Rules Examples

/-! Helpers for the predicates' tests. -/

private def hasW (s : String) (ws : List (List Char)) : Bool := ws.contains s.toList

private def cmdHas (s : String) (e : Event) : Bool :=
  match command e with
  | some c => occursIn s.toList c.toList
  | none => false

private def pathHas (s : String) : Option String → Bool
  | some p => occursIn s.toList p.toList
  | none => false

private def pathEnds (s : String) : Option String → Bool
  | some p => endsWith s.toList p.toList
  | none => false

/-- A script run by its path, through `python3` with a path to the interpreter, or through
`compute.sh`, with `p` holding of its words. -/
private def script (name : String) (p : List (List Char) → Bool) (e : Event) : Bool :=
  runs name p e || runs "python3" (fun ws => ws.any (endsWith name.toList) && p ws) e ||
    runs "compute.sh" (fun ws => ws.any (endsWith name.toList) && p ws) e

private def any' : List (List Char) → Bool := fun _ => true

/-! Event predicates. -/

def anyCall : Pred := ⟨"anyCall", isCall, [bash "ls"]⟩
def anyResult : Pred := ⟨"anyResult", isResult, [.result "c" "out"]⟩
def failedResult : Pred :=
  ⟨"failedResult", (fun | .result _ _ f => f | _ => false), [.result "c" "Exit code 1" true]⟩
def gitCommit : Pred := ⟨"gitCommit", runs "git" (hasW "commit"), [bash "git commit -m x"]⟩
def gitCommitNoEdit : Pred :=
  ⟨"gitCommitNoEdit", runs "git" (fun ws => hasW "commit" ws && hasW "--no-edit" ws),
    [bash "git commit --no-edit"]⟩
def gitRm : Pred := ⟨"gitRm", runs "git" (hasW "rm"), [bash "git rm tasks/x/FOO_BUG.md"]⟩
def gitRebase : Pred := ⟨"gitRebase", runs "git" (hasW "rebase"), [bash "git rebase origin/main"]⟩
def gitBranch : Pred := ⟨"gitBranch", runs "git" (hasW "branch"), [bash "git branch backup-x"]⟩
def worktreeAdd : Pred :=
  ⟨"worktreeAdd", runs "git" (fun ws => hasW "worktree" ws && hasW "add" ws),
    [bash "git worktree add p", bash "git worktree add --track -b n p main"]⟩
def worktreeAddTracked : Pred :=
  ⟨"worktreeAddTracked",
    runs "git" (fun ws => hasW "worktree" ws && hasW "add" ws && hasW "--track" ws && hasW "-b" ws),
    [bash "git worktree add --track -b n p main"]⟩
def fastForward : Pred :=
  ⟨"fastForward", runs "git" (fun ws => hasW "merge" ws && hasW "--ff-only" ws),
    [bash "git merge --ff-only 1a2b3c"]⟩
def coverLetterEdit : Pred :=
  ⟨"coverLetterEdit", fun e => pathHas "tasks/" (writePath e) && pathEnds "_MR.md" (writePath e),
    [edit "tasks/x/X_MR.md"]⟩
def ledgerEdit : Pred :=
  ⟨"ledgerEdit", fun e => pathEnds "_EVIDENCE.md" (writePath e), [edit "tasks/x/X_MR_EVIDENCE.md"]⟩
def bugDocEdit : Pred := ⟨"bugDocEdit", fun e => pathEnds "_BUG.md" (writePath e),
  [edit "tasks/x/FOO_BUG.md"]⟩
def planEdit : Pred := ⟨"planEdit", fun e => pathEnds "PLAN.md" (writePath e),
  [edit "tasks/x/PLAN.md"]⟩
def testEdit : Pred := ⟨"testEdit", fun e => pathHas "test" (writePath e),
  [edit "tests/test_a.py"]⟩
def notebookEdit : Pred := ⟨"notebookEdit", fun e => pathHas "notebook.html" (writePath e),
  [edit "notebook.html"]⟩
def claimIndexEdit : Pred := ⟨"claimIndexEdit", fun e => pathHas "claims/index.json" (writePath e),
  [edit "research/claims/index.json"]⟩
def notebookOrClaimEdit : Pred :=
  ⟨"notebookOrClaimEdit",
    fun e => pathHas "notebook.html" (writePath e) || pathHas "claims/index.json" (writePath e),
    [edit "notebook.html", edit "research/claims/index.json"]⟩
def claimViewEdit : Pred := ⟨"claimViewEdit", fun e => pathHas "CLAIM_INDEX.md" (writePath e),
  [edit "research/CLAIM_INDEX.md"]⟩
def scratchWrite : Pred :=
  ⟨"scratchWrite", fun e => pathHas "scratchpad" (writePath e) || pathHas "/tmp/" (writePath e),
    [edit "/tmp/claude/scratchpad/a.py"]⟩
def agentsMdEdit : Pred := ⟨"agentsMdEdit", fun e => pathEnds "AGENTS.md" (writePath e),
  [edit "AGENTS.md"]⟩
def instructionEdit : Pred :=
  ⟨"instructionEdit", fun e => ["AGENTS.md", "COMPUTATION_RULES.md", "TASK_PROTOCOL.md",
    "SKILL.md"].any (pathEnds · (writePath e)),
    [edit "AGENTS.md", edit "skills/engineering-discipline/SKILL.md"]⟩
def budgetsEdit : Pred :=
  ⟨"budgetsEdit", fun e => pathHas "instruction-budgets.json" (writePath e),
    [edit "research/instruction-budgets.json"]⟩
def toolEdit : Pred :=
  ⟨"toolEdit", fun e => pathHas "tools/" (writePath e) && pathEnds ".py" (writePath e),
    [edit "tools/lead_queue.py"]⟩
def toolRead : Pred :=
  ⟨"toolRead", fun e => pathHas "tools/" (readPath e) && pathEnds ".py" (readPath e),
    [read "tools/lead_queue.py"]⟩
/-- A framework test written beside the code it tests, outside `tools/tests/`. -/
def testBesideCode : Pred :=
  ⟨"testBesideCode", fun e => pathHas "tools/" (writePath e) && pathHas "/test_" (writePath e) &&
    !pathHas "tools/tests/" (writePath e), [edit "tools/hooks/test_guard.py"]⟩
def promptsRead : Pred := ⟨"promptsRead", fun e => pathHas "PROMPTS.md" (readPath e),
  [read "PROMPTS.md"]⟩
def aifiRead : Pred := ⟨"aifiRead", fun e => pathHas "AIFI.md" (readPath e),
  [read "research/notes/AIFI.md"]⟩
def pngRead : Pred := ⟨"pngRead", fun e => pathEnds ".png" (readPath e), [read "plot.png"]⟩
/-- A read of the notebook or the claim index with no line limit. -/
def wholeRecordRead : Pred :=
  ⟨"wholeRecordRead", fun e => (pathHas "notebook.html" (readPath e) ||
    pathHas "claims/index.json" (readPath e)) && e.field "limit" == none, [read "notebook.html"]⟩
def resumeRun : Pred := ⟨"resumeRun", script "resume.py" (fun ws => !hasW "--read" ws),
  [bash "python3 tools/resume.py"]⟩
def resumePartRead : Pred := ⟨"resumePartRead", script "resume.py" (hasW "--read"),
  [bash "/home/u/.local/bin/python3 tools/resume.py --read b --part 2"]⟩
/-- A read of the task protocol, by its file or a part of the resume bundle carrying it. -/
def protocolRead : Pred :=
  ⟨"protocolRead", fun e => pathHas "TASK_PROTOCOL.md" (readPath e) || script "resume.py" (hasW "--read") e,
    [read "research/notes/TASK_PROTOCOL.md"]⟩
def pytestRun : Pred :=
  ⟨"pytestRun", fun e => runs "pytest" any' e || runs "-m" (hasW "pytest") e ||
    runs "compute.sh" (fun ws => ws.any (endsWith "pytest".toList)) e,
    [bash "pytest tests", bash "python3 -m pytest", bash "./compute.sh python3 -m pytest tests"]⟩
def pytestQueue : Pred := ⟨"pytestQueue", script "pytest_queue.py" any',
  [bash "python3 tools/pytest_queue.py"]⟩
def pytestQueueIsolated : Pred := ⟨"pytestQueueIsolated", script "pytest_queue.py" (hasW "--isolate"),
  [bash "python3 tools/pytest_queue.py --isolate db.py"]⟩
def taskCheckpoint : Pred := ⟨"taskCheckpoint", script "task_checkpoint.py" any',
  [bash "python3 tools/task_checkpoint.py x"]⟩
def checkpointWithSuite : Pred := ⟨"checkpointWithSuite", script "task_checkpoint.py" (hasW "--suite"),
  [bash "python3 tools/task_checkpoint.py x --suite py=3:10"]⟩
def checkpointSlowReason : Pred :=
  ⟨"checkpointSlowReason", script "task_checkpoint.py" (hasW "--slow-because"),
    [bash "python3 tools/task_checkpoint.py x --suite py=9:10 --slow-because more-tests"]⟩
def mutationBatch : Pred := ⟨"mutationBatch", script "mutation_batch.py" any',
  [bash "./compute.sh python3 tools/mutation_batch.py root spec.py"]⟩
def cycleStart : Pred := ⟨"cycleStart", runs "compute.sh" (hasW "start"),
  [bash "./compute.sh start t1"]⟩
def finishTurn : Pred := ⟨"finishTurn", script "finish-turn.py" any', [bash "./tools/finish-turn.py t1"]⟩
def finishTurnViaLauncher : Pred :=
  ⟨"finishTurnViaLauncher", runs "compute.sh" (fun ws => ws.any (endsWith "finish-turn.py".toList)),
    [bash "./compute.sh python3 tools/finish-turn.py t1"]⟩
def entryAppend : Pred := ⟨"entryAppend", script "notebook-append.py" any',
  [bash "python3 tools/notebook-append.py notebook.html e.html"]⟩
def backlinksSearch : Pred := ⟨"backlinksSearch", script "notebook-excerpt.py" (hasW "--backlinks"),
  [bash "python3 tools/notebook-excerpt.py a --backlinks --tail 20"]⟩
def reviewTestsRead : Pred := ⟨"reviewTestsRead", script "notebook-excerpt.py" (hasW "--review-tests"),
  [bash "python3 tools/notebook-excerpt.py --review-tests"]⟩
def searchClaims : Pred := ⟨"searchClaims", script "search-claims.py" any',
  [bash "python3 tools/search-claims.py rank bound"]⟩
def claimGraph : Pred := ⟨"claimGraph", script "claim-index.py" (hasW "graph"),
  [bash "python3 tools/claim-index.py graph --claim c"]⟩
def claimAuthorBuild : Pred :=
  ⟨"claimAuthorBuild", script "claim-index.py" (fun ws => hasW "author" ws && hasW "build" ws),
    [bash "python3 tools/claim-index.py author build spec.json"]⟩
def claimRender : Pred := ⟨"claimRender", script "claim-index.py" (hasW "render"),
  [bash "python3 tools/claim-index.py render"]⟩
def claimCheck : Pred :=
  ⟨"claimCheck", fun e => script "check-claims.py" any' e || script "claim-index.py" (hasW "changed") e,
    [bash "python3 tools/check-claims.py", bash "python3 tools/claim-index.py changed --base HEAD"]⟩
def checkRecordsDiff : Pred := ⟨"checkRecordsDiff", script "check_records.py" (hasW "--diff"),
  [bash "./tools/check_records.py --diff"]⟩
def notebookContext : Pred := ⟨"notebookContext", script "notebook_context.py" any',
  [bash "python3 tools/notebook_context.py"]⟩
def notebookContextAll : Pred := ⟨"notebookContextAll", script "notebook_context.py" (hasW "--all"),
  [bash "python3 tools/notebook_context.py --all"]⟩
def leadQueueAppend : Pred := ⟨"leadQueueAppend", script "lead_queue.py" (hasW "append"),
  [bash "python3 tools/lead_queue.py append notebook.html r"]⟩
def leadQueueAdd : Pred :=
  ⟨"leadQueueAdd", script "lead_queue.py"
    (fun ws => hasW "add" ws && (hasW "--check" ws || hasW "--build" ws)),
    [bash "python3 tools/lead_queue.py add notebook.html --check i s 'Problem: x. Must: y.'"]⟩
def queueTextHasProblemMust : Pred :=
  ⟨"queueTextHasProblemMust", fun e => leadQueueAdd.test e && cmdHas "Problem:" e && cmdHas "Must:" e,
    [bash "python3 tools/lead_queue.py add notebook.html --check i s 'Problem: x. Must: y.'"]⟩
def leadQueueClose : Pred := ⟨"leadQueueClose", script "lead_queue.py" (hasW "close"),
  [bash "python3 tools/lead_queue.py close notebook.html i 'Closed: merged into j'"]⟩
def closeSaysMergedInto : Pred :=
  ⟨"closeSaysMergedInto", fun e => leadQueueClose.test e && cmdHas "merged into" e,
    [bash "python3 tools/lead_queue.py close notebook.html i 'Closed: merged into j'"]⟩
def patternIndexRead : Pred :=
  ⟨"patternIndexRead", fun e => pathHas "PATTERN_INDEX.md" (readPath e) || cmdHas "PATTERN_INDEX.md" e,
    [read "research/PATTERN_INDEX.md", bash "grep -n label research/PATTERN_INDEX.md"]⟩
def confluencePush : Pred := ⟨"confluencePush", script "confluence_page.py" any',
  [bash "python3 tools/confluence_page.py push D.md"]⟩
def ffBase : Pred :=⟨"ffBase", script "ff-base.sh" any', [bash "tools/ff-base.sh"]⟩
def mergeMain : Pred := ⟨"mergeMain", script "merge_main.py" any',
  [bash "python3 tools/merge_main.py main"]⟩
def notebookRebaseContinue : Pred :=
  ⟨"notebookRebaseContinue", script "notebook_rebase.py" (hasW "--continue"),
    [bash "python3 tools/notebook_rebase.py --continue"]⟩
/-- A request to the user filed: a task's request, or a line in the Git-ignored `user_requests`. -/
def userRequestFiled : Pred :=
  ⟨"userRequestFiled", fun e => isRequestAdd e || pathHas "user_requests" (writePath e),
    [bash "python3 tools/task_index.py request add x", edit "user_requests"]⟩
/-- A user message with repeated question marks. -/
def frustratedUser : Pred :=
  ⟨"frustratedUser", (fun | .user t => occursIn "??".toList t.toList | _ => false),
    [.user "why did it stop??"]⟩
/-- A file written through the shell: `sed -i`, a redirect of `cat`, or `tee`. -/
def shellFileWrite : Pred :=
  ⟨"shellFileWrite", fun e => runs "sed" (hasW "-i") e || cmdHas "cat >" e || runs "tee" any' e,
    [bash "sed -i s/a/b/ f", bash "cat > f <<'EOF'\nx\nEOF"]⟩
def heredocCall : Pred := ⟨"heredocCall", cmdHas "<<", [bash "python3 t.py <<'EOF'\nx\nEOF"]⟩
def scheduleWakeup : Pred :=
  ⟨"scheduleWakeup", isTool "ScheduleWakeup", [.call "w" "ScheduleWakeup" [("delaySeconds", "60")]]⟩
def agentRun : Pred := ⟨"agentRun", isTool "Agent",
  [reviewer, .call "g" "Agent" [("subagent_type", "general-purpose")]]⟩

/-- A command of a checkpoint batch: the finisher, the records check, provenance, the archive,
staging or the commit. -/
private def isCheckpointCmd (e : Event) : Bool :=
  script "finish-turn.py" any' e || script "check_records.py" any' e ||
    script "record-provenance.py" any' e || script "archive-session.py" any' e ||
    runs "git" (fun ws => hasW "add" ws || hasW "commit" ws) e

def checkpointStepCall : Pred := ⟨"checkpointStepCall", isCheckpointCmd,
  [bash "./tools/finish-turn.py t1", bash "git add notebook.html"]⟩

wellFormedPreds preds
  [anyCall, anyResult, failedResult, gitCommit, gitCommitNoEdit, gitRm, gitRebase, gitBranch,
   worktreeAdd, worktreeAddTracked, fastForward, coverLetterEdit, ledgerEdit, bugDocEdit, planEdit,
   testEdit, notebookEdit, claimIndexEdit, notebookOrClaimEdit, claimViewEdit, scratchWrite,
   agentsMdEdit, instructionEdit, budgetsEdit, toolEdit, toolRead, testBesideCode, promptsRead,
   aifiRead, pngRead, wholeRecordRead, resumeRun, resumePartRead, protocolRead, pytestRun,
   pytestQueue, pytestQueueIsolated, taskCheckpoint, checkpointWithSuite, checkpointSlowReason,
   mutationBatch, cycleStart, finishTurn, finishTurnViaLauncher, entryAppend, backlinksSearch,
   reviewTestsRead, searchClaims, claimGraph, claimAuthorBuild, claimRender, claimCheck,
   checkRecordsDiff, notebookContext, notebookContextAll, leadQueueAppend, leadQueueAdd,
   queueTextHasProblemMust, leadQueueClose, closeSaysMergedInto, patternIndexRead, confluencePush, ffBase,
   mergeMain, notebookRebaseContinue, userRequestFiled, frustratedUser, shellFileWrite, heredocCall,
   scheduleWakeup, agentRun, checkpointStepCall]

/-! Relations. -/

/-- Two steps of one message are both commands of a checkpoint batch. -/
def checkpointStepsTogether : Rel :=
  ⟨"checkpointStepsTogether", fun s t => isCheckpointCmd s.event && isCheckpointCmd t.event,
    [(bash "git add f", bash "git commit -m x")]⟩

def rels : List Rel := [checkpointStepsTogether]

theorem rels_wellFormed : rels.all Rel.wellFormed = true := by decide

/-! Atoms: artifacts, test speed and the queue's settings (701 to 716). -/

def oneLogicalChange : Atom := ⟨"oneLogicalChange",
  "Does this commit hold one logical change and nothing else, as one step of a clean sequence on its branch?", .call⟩
def offersMultiCommitBranch : Atom := ⟨"offersMultiCommitBranch",
  "Does this reply offer a branch of several commits as a code-change artifact?", .reply⟩
def inCoverLetterFormat : Atom := ⟨"inCoverLetterFormat",
  "Does this edit write the cover letter in the mr-cover-letter skill's format?", .edit⟩
def offersCoverLetter : Atom := ⟨"offersCoverLetter",
  "Does this reply offer a cover letter (an MR description) for review or a push?", .reply⟩
def offersReworkedBranch : Atom := ⟨"offersReworkedBranch",
  "Does this reply offer a branch that was reworked after a review?", .reply⟩
def addsVersionNote : Atom := ⟨"addsVersionNote",
  "Does this edit add a version note describing the rework to the branch's cover letter?", .edit⟩
def addsVersionNoteRows : Atom := ⟨"addsVersionNoteRows",
  "Does this edit add ledger rows for the facts of the cover letter's version note?", .edit⟩
def reportsOtherArtifactDone : Atom := ⟨"reportsOtherArtifactDone",
  "Does this reply report as finished an artifact that is neither a code change nor an investigation report?", .reply⟩
def writesOtherArtifact : Atom := ⟨"writesOtherArtifact",
  "Does this edit write an artifact that is neither a code change nor an investigation report (a migration script, a design, a reproduction)?", .edit⟩
def statesWhatWasNotAchieved : Atom := ⟨"statesWhatWasNotAchieved",
  "Does the artifact this edit writes say honestly what was and wasn't achieved?", .edit⟩
def writesConfluencePage : Atom := ⟨"writesConfluencePage",
  "Does this tool call create or change a Confluence page?", .call⟩
def findsTangentialBug : Atom := ⟨"findsTangentialBug",
  "Does this reply note a bug or gap tangential to the task (or feedback on its work deferred for later)?", .reply⟩
def saysBugTrackedElsewhere : Atom := ⟨"saysBugTrackedElsewhere",
  "Does this reply say a task's bug write-up is now tracked elsewhere, such as in a Jira issue?", .reply⟩
def worksOnTask : Atom := ⟨"worksOnTask",
  "Does this tool call work on the task in progress itself, rather than on a tangential bug?", .call⟩
def runsWholeSuite : Atom := ⟨"runsWholeSuite",
  "Does this call run a repository's whole test suite?", .call⟩
def runsSuiteSerially : Atom := ⟨"runsSuiteSerially",
  "Does this call run a non-pytest test suite serially, without its ecosystem's parallel runner?", .call⟩
def suiteUsesService : Atom := ⟨"suiteUsesService",
  "Do tests this call runs use a service such as a test database?", .call⟩
def testChecksSeveralThings : Atom := ⟨"testChecksSeveralThings",
  "Does this edit write a test checking several independent things that could each fail alone?", .edit⟩
def setsSuiteBudget : Atom := ⟨"setsSuiteBudget",
  "Does this edit set or change the repository's time budget for its parallel test suite?", .edit⟩
def budgetNearOneAndHalf : Atom := ⟨"budgetNearOneAndHalf",
  "Is the suite budget this edit sets near one and a half times the measured parallel suite time?", .edit⟩
def suiteGrewOverFifth : Atom := ⟨"suiteGrewOverFifth",
  "Does the suite time this checkpoint records exceed the last checkpoint's by more than a fifth?", .call⟩
def claimsSpeedFix : Atom := ⟨"claimsSpeedFix",
  "Does this reply say a change made the tests or a tool faster?", .reply⟩
def runsUntouchedTests : Atom := ⟨"runsUntouchedTests",
  "Does this call, during a cycle and not at its checkpoint, run test files the change doesn't touch?", .call⟩
def runsMutants : Atom := ⟨"runsMutants",
  "Does this call run mutants, targeted or generic?", .call⟩
def specsWithEvidence : Atom := ⟨"specsWithEvidence",
  "Are the mutant specs this call runs kept with the task's evidence?", .call⟩
def changesQueueCounting : Atom := ⟨"changesQueueCounting",
  "Does this edit set the lead queue's data-counted to other than task, or its data-backpressure to other than off?", .edit⟩

/-! Atoms: restoration and the research discipline (717 to 756). -/

def asksToRestoreContext : Atom := ⟨"asksToRestoreContext",
  "Does this message from the user ask the agent to resume or restore context?", .user⟩
def actsOnNamedPrompt : Atom := ⟨"actsOnNamedPrompt",
  "Does this tool call act on a named prompt (Resume, Task, Spin, Formalize and the like) the user gave?", .call⟩
def loadsRecordWholesale : Atom := ⟨"loadsRecordWholesale",
  "Does this call load the notebook's growing record or the claim index whole, rather than a targeted passage?", .call⟩
def aifiTaskInProgress : Atom := ⟨"aifiTaskInProgress",
  "Is an AiFi task in progress at this point of the session?", .any⟩
def startsResearchCycle : Atom := ⟨"startsResearchCycle",
  "Does this call start a research cycle, rather than a task cycle or an admin turn?", .call⟩
def isResearchEntry : Atom := ⟨"isResearchEntry",
  "Does this call append a research entry (data-kind research) to the notebook?", .call⟩
def readsOpenStatements : Atom := ⟨"readsOpenStatements",
  "Does this call read the notebook's Open statements section?", .call⟩
def namesAdvancedStatement : Atom := ⟨"namesAdvancedStatement",
  "Does the entry this call appends name the open statement and the top-level route item it advances?", .call⟩
def choosesNextStep : Atom := ⟨"choosesNextStep",
  "Does this reply choose the research's next step?", .reply⟩
def choosesByObligationThenRisk : Atom := ⟨"choosesByObligationThenRisk",
  "Does this reply's choice put a necessary unproved obligation first, and among those the item the latest review names highest risk?", .reply⟩
def reopensOlderQuestion : Atom := ⟨"reopensOlderQuestion",
  "Does this reply reopen a question an older entry of the record settled or parked?", .reply⟩
def reportsRestrictedExamples : Atom := ⟨"reportsRestrictedExamples",
  "Does the entry this call appends report restricted examples or finite cases?", .call⟩
def namesGeneralHypothesis : Atom := ⟨"namesGeneralHypothesis",
  "Does the entry this call appends name the general hypothesis, obstruction or mechanism its examples test?", .call⟩
def hasGeneralStatement : Atom := ⟨"hasGeneralStatement",
  "Does the entry this call appends have a General statement. paragraph citing the registered claim ID of its all-parameter claim?", .call⟩
def finiteCheckOnly : Atom := ⟨"finiteCheckOnly",
  "Does the entry this call appends register only finite checks?", .call⟩
def exceedsFiniteCheckShare : Atom := ⟨"exceedsFiniteCheckShare",
  "Would the entry this call appends be the fourth of five consecutive research entries on its route registering new finite checks other than refutations?", .call⟩
def leavesImplicationUntouched : Atom := ⟨"leavesImplicationUntouched",
  "Does the entry this call appends leave the route's required implication untouched?", .call⟩
def usesDifferentMechanism : Atom := ⟨"usesDifferentMechanism",
  "Does the entry this call appends address the route with a different mechanism, a lead or a bridge?", .call⟩
def recordsForScheduledReview : Atom := ⟨"recordsForScheduledReview",
  "Does the entry this call appends record the repeated failure for the scheduled review?", .call⟩
def rechecksStandingHypotheses : Atom := ⟨"rechecksStandingHypotheses",
  "Does the entry this call appends recheck the standing hypotheses against the goal's instances?", .call⟩
def reportsUpperBoundExclusion : Atom := ⟨"reportsUpperBoundExclusion",
  "Does the entry this call appends report an upper bound ruling out a candidate family?", .call⟩
def extractsStructuralReason : Atom := ⟨"extractsStructuralReason",
  "Does the entry this call appends extract the structural reason the bound rules the family out?", .call⟩
def checksOtherCandidates : Atom := ⟨"checksOtherCandidates",
  "Does the entry this call appends check whether that reason applies to the other candidates?", .call⟩
def recordsBoundLesson : Atom := ⟨"recordsBoundLesson",
  "Does the entry this call appends record what the bound teaches beside the exclusion?", .call⟩
def adoptsSpecRefinement : Atom := ⟨"adoptsSpecRefinement",
  "Does the entry this call appends adopt a refinement of an evolving formula specification?", .call⟩
def provesNonVacuityWitness : Atom := ⟨"provesNonVacuityWitness",
  "Does the entry this call appends prove a non-vacuity witness for the refinement at unbounded variable counts within the encoding budget?", .call⟩
def marksRefinementProvisional : Atom := ⟨"marksRefinementProvisional",
  "Does the entry this call appends mark the refinement provisional?", .call⟩
def runsLargerSize : Atom := ⟨"runsLargerSize",
  "Does this call run a larger size, degree or sample of an earlier series of runs?", .call⟩
def namesQuestionChangingImplication : Atom := ⟨"namesQuestionChangingImplication",
  "Does this run come with a question the finished runs can't answer, whose answer would change the goal's missing implication?", .call⟩
def fitsFormula : Atom := ⟨"fitsFormula",
  "Does this reply fit a formula to computed witnesses?", .reply⟩
def proposesStepOrNamesResult : Atom := ⟨"proposesStepOrNamesResult",
  "Does this reply propose a next step, or name or develop a result?", .reply⟩
def formulatesNewLemma : Atom := ⟨"formulatesNewLemma",
  "Does this reply formulate a new lemma?", .reply⟩
def draftsLemmaProof : Atom := ⟨"draftsLemmaProof",
  "Does this edit draft the proof of a new lemma?", .edit⟩
def draftsCorollary : Atom := ⟨"draftsCorollary",
  "Does this edit draft a corollary?", .edit⟩
def writesComposition : Atom := ⟨"writesComposition",
  "Does this edit state a composition of results?", .edit⟩
def compositionIsCompleteLemma : Atom := ⟨"compositionIsCompleteLemma",
  "Does this edit state the composition as a lemma in one common setting with a complete proof, never a reference to a sketch?", .edit⟩
def commitsToDirection : Atom := ⟨"commitsToDirection",
  "Does this reply commit the research to a direction?", .reply⟩
def recordsRediscoveryOrRefinement : Atom := ⟨"recordsRediscoveryOrRefinement",
  "Does this edit record a rediscovery or a refinement of an earlier result?", .edit⟩
def labelsAndLinksOriginal : Atom := ⟨"labelsAndLinksOriginal",
  "Does this edit label it a rediscovery or refinement and link the original?", .edit⟩
def isReviewerSpawn : Atom := ⟨"isReviewerSpawn",
  "Does this call spawn a fresh-context reviewer for the research cycle?", .call⟩
def givenOnlyStableDrafts : Atom := ⟨"givenOnlyStableDrafts",
  "Is this reviewer given only the stable drafts and dependency anchors or excerpts, near the cycle's end?", .call⟩
def spawnsCodexMediumReviewer : Atom := ⟨"spawnsCodexMediumReviewer",
  "Does this call spawn, in Codex, a native subagent with explicit medium effort as the reviewer protocol says?", .call⟩
def isHigherEffortReviewer : Atom := ⟨"isHigherEffortReviewer",
  "Does this call spawn a reviewer at higher than medium effort?", .call⟩
def saysMediumUnavailable : Atom := ⟨"saysMediumUnavailable",
  "Does this reply say a medium-effort reviewer is unavailable?", .reply⟩
def startsRootSessionForReview : Atom := ⟨"startsRootSessionForReview",
  "Does this call start a new root session to run a review?", .call⟩
def briefNamesExactAnchors : Atom := ⟨"briefNamesExactAnchors",
  "Does this reviewer brief name exact files and anchors?", .call⟩
def briefAtMostTwoSearches : Atom := ⟨"briefAtMostTwoSearches",
  "Does this reviewer brief ask for at most one or two named claim searches?", .call⟩
def briefExcerptsInScratchFile : Atom := ⟨"briefExcerptsInScratchFile",
  "Does this reviewer brief give the dependency excerpts in a scratch file?", .call⟩
def briefChangesAsBullets : Atom := ⟨"briefChangesAsBullets",
  "Does this reviewer brief ask for required changes as short bullets?", .call⟩
def briefAsksProcessAudit : Atom := ⟨"briefAsksProcessAudit",
  "Does this reviewer brief ask for a process audit?", .call⟩
def isNoveltyReviewer : Atom := ⟨"isNoveltyReviewer",
  "Does this call spawn a separate novelty reviewer?", .call⟩
def hasReviewerSuggestions : Atom := ⟨"hasReviewerSuggestions",
  "Does the entry this call appends carry suggestions from its reviewer?", .call⟩
def suggestionsUnderUnverifiedHeading : Atom := ⟨"suggestionsUnderUnverifiedHeading",
  "Does the entry list its reviewer's suggestions under the heading Reviewer's suggestions, unverified?", .call⟩
def eachSuggestionEndsRecord : Atom := ⟨"eachSuggestionEndsRecord",
  "Does each listed suggestion end with a Record. outcome naming claim IDs or the words searched?", .call⟩
def hasVerificationGate : Atom := ⟨"hasVerificationGate",
  "Does the entry this call appends have a short Verification gate. paragraph with the dependencies reread, the checks, the reviewer's verdict and the Process audit?", .call⟩
def developsNextResult : Atom := ⟨"developsNextResult",
  "Does this edit develop the next result, beyond the checkpoint in progress?", .edit⟩
def isResearchCheckpointCommit : Atom := ⟨"isResearchCheckpointCommit",
  "Is this commit a research turn's checkpoint commit?", .call⟩
def runsComputation : Atom := ⟨"runsComputation",
  "Does this call run a computation, a failed attempt or retry included?", .call⟩
def inResearchTurn : Atom := ⟨"inResearchTurn",
  "Is a research turn in progress at this point?", .any⟩
def discardsFullOutput : Atom := ⟨"discardsFullOutput",
  "Does this call discard a run's full output instead of keeping it on disk?", .call⟩
def displaysUnboundedOutput : Atom := ⟨"displaysUnboundedOutput",
  "Does this call display a long output unbounded, rather than a bounded excerpt?", .call⟩
def requestsPngPreview : Atom := ⟨"requestsPngPreview",
  "Does this message from the user ask to see a PNG preview?", .user⟩
def runsRenderingCheck : Atom := ⟨"runsRenderingCheck",
  "Does this call run a site or rendering check?", .call⟩
def hasLayoutChangeOrConcern : Atom := ⟨"hasLayoutChangeOrConcern",
  "At this point, has the session changed layout or a tool, or met a concrete rendering concern?", .any⟩

/-! Atoms: goal progress, reviews and the notebook (757 to 806). -/

def breaksReviewCadence : Atom := ⟨"breaksReviewCadence",
  "Is the entry this call appends a seventh research entry in a row on its route, or a review before six research entries?", .call⟩
def isExtraCadenceReviewer : Atom := ⟨"isExtraCadenceReviewer",
  "Does this call spawn a reviewer for a review the six-then-one cadence doesn't call for?", .call⟩
def isResearchOrReviewEntry : Atom := ⟨"isResearchOrReviewEntry",
  "Does this call append a research or review entry?", .call⟩
def hasObligationAndProgressAttrs : Atom := ⟨"hasObligationAndProgressAttrs",
  "Does the entry name its stable Open statements ID in data-obligation and set data-goal-progress?", .call⟩
def hasNewMathAndGoalProgress : Atom := ⟨"hasNewMathAndGoalProgress",
  "Does the entry give separate New mathematics. and Goal progress. paragraphs?", .call⟩
def reportsRouteUnchanged : Atom := ⟨"reportsRouteUnchanged",
  "Does the research entry this call appends report its route unchanged?", .call⟩
def endsWithBearing : Atom := ⟨"endsWithBearing",
  "Does the entry's Goal progress paragraph end with a Bearing. statement?", .call⟩
def bearingAttrMatches : Atom := ⟨"bearingAttrMatches",
  "Does the entry's data-bearing attribute match its Bearing. statement?", .call⟩
def bearingSome : Atom := ⟨"bearingSome",
  "Does the entry declare data-bearing some?", .call⟩
def hasNotCovered : Atom := ⟨"hasNotCovered",
  "Does the entry's Bearing. end with a Not covered. statement of the cases it doesn't reach?", .call⟩
def declaresBearingNone : Atom := ⟨"declaresBearingNone",
  "Does the entry this call appends declare data-bearing none?", .call⟩
def followUpContinuing : Atom := ⟨"followUpContinuing",
  "Is the entry's queue-item follow-up Continuing?", .call⟩
def statesRecordSearch : Atom := ⟨"statesRecordSearch",
  "Does the entry state a Record search. for the next attempt it names?", .call⟩
def isRouteReview : Atom := ⟨"isRouteReview",
  "Does this call append a scheduled route review?", .call⟩
def hasArchitectureReview : Atom := ⟨"hasArchitectureReview",
  "Does the review hold an Architecture review section with Necessary target (ending Downstream.), Extra requirements, Independent alternative, Rank normalization, Decision and Decisive test paragraphs?", .call⟩
def isIndependentAlternativeBrief : Atom := ⟨"isIndependentAlternativeBrief",
  "Does this call brief a reviewer for a review's Independent alternative?", .call⟩
def withholdsPreferredRoute : Atom := ⟨"withholdsPreferredRoute",
  "Does this brief give only the goal and bounded excerpts of results, withholding the preferred route?", .call⟩
def decisiveTestHasPowerAndRecordSearch : Atom := ⟨"decisiveTestHasPowerAndRecordSearch",
  "Does the review's Decisive test state Power. and end with Record search.?", .call⟩
def reportsArchitectureTest : Atom := ⟨"reportsArchitectureTest",
  "Does the entry report the review's test outcome in an Architecture test. paragraph linking the review's anchor?", .call⟩
def rewritesHistoricalEntry : Atom := ⟨"rewritesHistoricalEntry",
  "Does this edit change an earlier entry's assessment or mathematics, beyond a link repair or presentation-only change?", .edit⟩
def reviewsLivingSections : Atom := ⟨"reviewsLivingSections",
  "Does this call review or update the living sections (Where we stand, Open statements, The remaining route, Proposed next step, Working context)?", .call⟩
def editsOpenStatements : Atom := ⟨"editsOpenStatements",
  "Does this edit change the Open statements section?", .edit⟩
def openStatementsWellFormed : Atom := ⟨"openStatementsWellFormed",
  "After this edit, does Open statements hold at most about five self-contained statements, each with its status and the instances it must cover?", .edit⟩
def holdsFullMathematics : Atom := ⟨"holdsFullMathematics",
  "Does the entry this call appends hold the turn's question, outcome, remaining gap and new mathematics in full?", .call⟩
def raisesHardBudget : Atom := ⟨"raisesHardBudget",
  "Does this edit raise or waive a hard context-budget limit?", .edit⟩
def overridesBudget : Atom := ⟨"overridesBudget",
  "Does this message from the user explicitly override a hard context-budget limit?", .user⟩
def asksUserToConsolidate : Atom := ⟨"asksUserToConsolidate",
  "Does this reply leave consolidating the notebook to the user?", .reply⟩
def replacesMainWithSideGoal : Atom := ⟨"replacesMainWithSideGoal",
  "Does this edit replace the main notebook's living sections with a side goal?", .edit⟩
def editsNotebookCopy : Atom := ⟨"editsNotebookCopy",
  "Does this edit change a copy of the selected notebook instead of the notebook itself?", .edit⟩
def hasKindRouteClaimsTags : Atom := ⟨"hasKindRouteClaimsTags",
  "Does the entry carry data-kind, a data-route naming a top-level route item, and data-claims matching its claims or none with a data-claim-note?", .call⟩
def scopeMatchesOpenItemCount : Atom := ⟨"scopeMatchesOpenItemCount",
  "Is the review goal-level exactly when its line's open-item count has not dropped since the review ten or more entries back?", .call⟩
def reviewHasRequiredParts : Atom := ⟨"reviewHasRequiredParts",
  "Does the review state the line's general claim, what the goal needs, a falsification attempt, an assessment of that line, the next step and an Obstacle heading?", .call⟩
def queueDraining : Atom := ⟨"queueDraining",
  "Is the lead queue draining at this point (it reached 30 top-level items and hasn't fallen to 10)?", .any⟩
def hasLeadsAndBridges : Atom := ⟨"hasLeadsAndBridges",
  "Does the review give at least three Outside leads and two Absurd bridges, each ending Answers. and Test. with Passed, Falsified or Not run?", .call⟩
def cheapTestsRun : Atom := ⟨"cheapTestsRun",
  "Was every cheap test the review's sections name run within the review cycle?", .call⟩
def marksPicks : Atom := ⟨"marksPicks",
  "Does the review mark its three most promising passed leads and two bridges with data-pick?", .call⟩
def reviewHasPicks : Atom := ⟨"reviewHasPicks",
  "Does the review this call appends mark picked items?", .call⟩
def editsQueueByHand : Atom := ⟨"editsQueueByHand",
  "Does this edit change the Lead and bridge queue's items by hand instead of with lead_queue.py?", .edit⟩
def developsSeveralItems : Atom := ⟨"developsSeveralItems",
  "Does the entry develop more than one top-level queue item?", .call⟩
def developsNonHeadItem : Atom := ⟨"developsNonHeadItem",
  "Does the entry develop a queue item other than the head?", .call⟩
def hasChosenParagraph : Atom := ⟨"hasChosenParagraph",
  "Does the entry have a Chosen. paragraph saying which open statement the item bears on and why it comes first?", .call⟩
def continuesItemPastSpell : Atom := ⟨"continuesItemPastSpell",
  "Does the entry develop a queue item past the end of its spell?", .call⟩
def recordsSpellExtension : Atom := ⟨"recordsSpellExtension",
  "Does the entry record a spell extension in the queue tool's extension format?", .call⟩
def extensionEarnedByProgress : Atom := ⟨"extensionEarnedByProgress",
  "Did a proof, refutation or reduction of the spell materially advance a named open statement, with a next necessary implication using the same mechanism?", .call⟩
def refilesRefusedWork : Atom := ⟨"refilesRefusedWork",
  "Does the entry re-file work refused at a spell boundary under a related item?", .call⟩
def developsQueueItem : Atom := ⟨"developsQueueItem",
  "Does the entry this call appends develop a queue item?", .call⟩
def hasLeadTagAndFollowUp : Atom := ⟨"hasLeadTagAndFollowUp",
  "Is the entry tagged data-lead or data-bridge, stating Follow-up. Closed, Developed or Continuing?", .call⟩
def closesQueueItem : Atom := ⟨"closesQueueItem",
  "Does the entry close its queue item?", .call⟩
def closureHasStakesLinkSources : Atom := ⟨"closureHasStakesLinkSources",
  "Does the closure carry a Stakes. paragraph, a link to its record and a Sources read. statement?", .call⟩
def closureReasonFoundByAttempt : Atom := ⟨"closureReasonFoundByAttempt",
  "Does the closure rest on a reason the attempt found (a restatement, inapplicability, a falsification, supersession)?", .call⟩
def asksUserToCloseItem : Atom := ⟨"asksUserToCloseItem",
  "Does this reply ask the user whether to close a queue item?", .reply⟩
def leavesItemUnfinished : Atom := ⟨"leavesItemUnfinished",
  "Does the entry leave its queue item's reading, change, checks or follow-up unfinished?", .call⟩
def hasOwnLeadsSections : Atom := ⟨"hasOwnLeadsSections",
  "Does the entry carry Outside leads or Absurd bridges sections?", .call⟩
def reopensClosedItem : Atom := ⟨"reopensClosedItem",
  "Does this call reopen a queue item closed too early?", .call⟩
def hasReopenedFollowUp : Atom := ⟨"hasReopenedFollowUp",
  "Does the reopening carry a follow-up item ending Follow-up. Reopened: and its reason?", .call⟩
def listsUnfitSubIdea : Atom := ⟨"listsUnfitSubIdea",
  "Does the entry list under Sub-ideas an item that is filler, won't be done, or is small enough to do in the entry?", .call⟩
def queueTextReadableAlone : Atom := ⟨"queueTextReadableAlone",
  "Can someone taking up this queue item weeks later, without the conversation, act on its text?", .call⟩
def closesQueueItemOtherwise : Atom := ⟨"closesQueueItemOtherwise",
  "Does this call close or remove a queue item?", .call⟩
def closesDuplicate : Atom := ⟨"closesDuplicate",
  "Does this call close a queue item as a duplicate of another?", .call⟩
def marksCheckDeveloped : Atom := ⟨"marksCheckDeveloped",
  "Does this call mark a check item Developed?", .call⟩
def citesResolvingEvidence : Atom := ⟨"citesResolvingEvidence",
  "Does it cite evidence resolving the check?", .call⟩
def marksBuildDeveloped : Atom := ⟨"marksBuildDeveloped",
  "Does this call mark a build item Developed?", .call⟩
def citesTaskOrPath : Atom := ⟨"citesTaskOrPath",
  "Does it cite the build's opened task or its path?", .call⟩
def developsHeadOrFirstSubIdea : Atom := ⟨"developsHeadOrFirstSubIdea",
  "Does the entry develop the queue's head or its first sub-idea?", .call⟩
def editsProposedNextStep : Atom := ⟨"editsProposedNextStep",
  "Does this edit change Proposed next step?", .edit⟩
def namesRouteItemResearchStep : Atom := ⟨"namesRouteItemResearchStep",
  "Does the Proposed next step this edit writes name its route item and propose research, never a park or a wait?", .edit⟩
def saysRoutesClosed : Atom := ⟨"saysRoutesClosed",
  "Does this reply say every recorded route is closed?", .reply⟩
def spinActive : Atom := ⟨"spinActive",
  "Is an authorized Spin in progress at this point?", .any⟩
def endsTurn : Atom := ⟨"endsTurn",
  "Does this reply end the turn without starting the next cycle or review?", .reply⟩
def goalProved : Atom := ⟨"goalProved",
  "Is the notebook's goal proved at this point?", .any⟩
def lowYieldCorrectionOrHardStep : Atom := ⟨"lowYieldCorrectionOrHardStep",
  "Does the entry report a low-yield cycle, a correction or a hard next step?", .call⟩
def developsReviewLead : Atom := ⟨"developsReviewLead",
  "Does the entry develop an Outside lead or Absurd bridge of the latest review?", .call⟩
def registersClaim : Atom := ⟨"registersClaim",
  "Does this call register a claim in the registry?", .call⟩
def writesClaimMetadata : Atom := ⟨"writesClaimMetadata",
  "Does this call add or substantively revise a claim's metadata?", .call⟩
def claimMetadataComplete : Atom := ⟨"claimMetadataComplete",
  "Does the claim get evidence-backed status, topics, formalization scope and disposition, significance and relationship review?", .call⟩
def raisesSignificanceCandidate : Atom := ⟨"raisesSignificanceCandidate",
  "Does this call's output raise a new or reopened significance candidate?", .call⟩
def addsRefinesWithoutImplication : Atom := ⟨"addsRefinesWithoutImplication",
  "Does this call record a refines edge between versions neither of which implies the other?", .call⟩
def proposesPattern : Atom := ⟨"proposesPattern",
  "Does this reply propose, develop or name a working-style pattern?", .reply⟩
def writesPatternStatus : Atom := ⟨"writesPatternStatus",
  "Does this edit write a working-style pattern's status line?", .edit⟩
def notebookHasFormalizationGaps : Atom := ⟨"notebookHasFormalizationGaps",
  "Does the notebook this restoration selects have a Gaps identified by formalization section?", .call⟩
def isFormalizationWorker : Atom := ⟨"isFormalizationWorker",
  "Is the agent a worker of a coordinated parallel formalization at this point?", .any⟩
def editsLivingSection : Atom := ⟨"editsLivingSection",
  "Does this edit change one of the notebook's living sections?", .edit⟩
def rerunsFinisherChecks : Atom := ⟨"rerunsFinisherChecks",
  "Does this call rerun the finisher's checks?", .call⟩
def endsWithTimingTable : Atom := ⟨"endsWithTimingTable",
  "Does the entry end with the generated Measured category / Elapsed table and bold total, a one-sentence footnote and no backfilled time?", .call⟩
def commitsResearchEntry : Atom := ⟨"commitsResearchEntry",
  "Does this commit hold a research entry?", .call⟩
def commitHoldsEntryBundle : Atom := ⟨"commitHoldsEntryBundle",
  "Does this commit hold the entry with its timing fragment, archive and supporting results together?", .call⟩

/-! Atoms: worktrees, merges and requests (807 to 821). -/

def citesScratchOnlyResult : Atom := ⟨"citesScratchOnlyResult",
  "Does the entry cite a result whose only copy is in scratch, tmp, a runtime folder or ignored logs?", .call⟩
def deletesScratch : Atom := ⟨"deletesScratch",
  "Does this call delete the session's own scratch files?", .call⟩
def deletesUnpromotedResult : Atom := ⟨"deletesUnpromotedResult",
  "Does this deletion remove a result worth keeping that wasn't promoted to research/results or research/provenance?", .call⟩
def inSharedCheckoutInBackground : Atom := ⟨"inSharedCheckoutInBackground",
  "Is this edit a background session's, made in the shared checkout rather than its worktree?", .edit⟩
def inWorktree : Atom := ⟨"inWorktree",
  "Is this commit made in a worktree?", .call⟩
def ffBaseReportsConflict : Atom := ⟨"ffBaseReportsConflict",
  "Does this result of tools/ff-base.sh report a dry-run or rebase conflict?", .result⟩
def bringsSourceFramework : Atom := ⟨"bringsSourceFramework",
  "Does this call bring a source branch's framework into this branch?", .call⟩
def bringsLargeFrameworkChange : Atom := ⟨"bringsLargeFrameworkChange",
  "Does this merge bring a large framework change from its source?", .call⟩
def ffTargetPinned : Atom := ⟨"ffTargetPinned",
  "Does this fast-forward target an immutable commit fetched or received before?", .call⟩
def rebasesOntoMovedRemote : Atom := ⟨"rebasesOntoMovedRemote",
  "Does this rebase move a branch onto a remote that moved under it?", .call⟩
def inTemporaryWorktree : Atom := ⟨"inTemporaryWorktree",
  "Does this rebase run in a temporary worktree?", .call⟩
def continuesRebase : Atom := ⟨"continuesRebase",
  "Does this call continue a stopped rebase?", .call⟩
def resolvesConflictByScratchLoop : Atom := ⟨"resolvesConflictByScratchLoop",
  "Does this call resolve a recurring conflict shape with a scratch loop, rather than a guarded, tested resolver?", .call⟩
def asksUserSomething : Atom := ⟨"asksUserSomething",
  "Does this reply ask the user for something (a source, an install, a permission, a choice)?", .reply⟩
def requestHasNeedWhyTriedDefault : Atom := ⟨"requestHasNeedWhyTriedDefault",
  "Does the request this call files say what is needed, why, what was tried and the default followed?", .call⟩
def answersOpenRequest : Atom := ⟨"answersOpenRequest",
  "Does this message from the user answer an open request?", .user⟩
def reportsTaskProgress : Atom := ⟨"reportsTaskProgress",
  "Does this reply report a task's progress?", .reply⟩
def reportsAgainstArtifact : Atom := ⟨"reportsAgainstArtifact",
  "Does the report give progress against the requested artifact, its test evidence and the remaining blockers?", .reply⟩
def declaresMathClaimsInReport : Atom := ⟨"declaresMathClaimsInReport",
  "Does the task report carry mathematical claim declarations or a research-review cadence?", .reply⟩
def isRestartNotification : Atom := ⟨"isRestartNotification",
  "Is this message a notification after a session restart (instructions, stopped tasks, changed files) rather than the user's own?", .user⟩
def isAtMostOneSentence : Atom := ⟨"isAtMostOneSentence",
  "Is this reply at most one sentence?", .reply⟩
def asksToContinueActiveWork : Atom := ⟨"asksToContinueActiveWork",
  "Does this reply ask whether to go on with an active goal or authorized loop?", .reply⟩

/-! Atoms: mistakes, instruction files and tools (822 to 840). -/

def answersShownMistake : Atom := ⟨"answersShownMistake",
  "Does this reply answer a mistake of the agent's that the user or a reviewer showed?", .reply⟩
def hasPreventionAndMeta : Atom := ⟨"hasPreventionAndMeta",
  "Does this reply carry a Prevention paragraph naming the framework change made in the turn, and a Meta paragraph?", .reply⟩
def admitsMistakeOrReviewer : Atom := ⟨"admitsMistakeOrReviewer",
  "Does the entry admit a mistake, report a reviewer agent's findings or answer a right stand-in objection?", .call⟩
def hasMetaForEach : Atom := ⟨"hasMetaForEach",
  "Does the entry's Meta. paragraph answer each of them?", .call⟩
def addsGoalSpecificRule : Atom := ⟨"addsGoalSpecificRule",
  "Does this edit add to AGENTS.md a rule about one goal's mathematics rather than every notebook?", .edit⟩
def commitsInstructionChange : Atom := ⟨"commitsInstructionChange",
  "Does this commit change an instruction file?", .call⟩
def removesAsMuchAsAdds : Atom := ⟨"removesAsMuchAsAdds",
  "Does the instruction change remove as much as it adds?", .call⟩
def keepsEveryConstraint : Atom := ⟨"keepsEveryConstraint",
  "Does the instruction change keep every explicit constraint?", .call⟩
def restatesRuleElsewhere : Atom := ⟨"restatesRuleElsewhere",
  "Does this edit state a rule that another file owns?", .edit⟩
def restatesSkillRule : Atom := ⟨"restatesSkillRule",
  "Does this edit restate a rule of the published skill in a private file?", .edit⟩
def commitsAddedRule : Atom := ⟨"commitsAddedRule",
  "Does this commit add a rule to an instruction file?", .call⟩
def keepsOneCallPerJob : Atom := ⟨"keepsOneCallPerJob",
  "Does the tool this edit changes give its job one call, doing every step itself?", .edit⟩
def refusesWrongCallFirst : Atom := ⟨"refusesWrongCallFirst",
  "Does the tool this edit changes refuse a wrong call before doing anything?", .edit⟩
def refusalSaysWhatToDo : Atom := ⟨"refusalSaysWhatToDo",
  "Does each refusal of the tool say briefly what failed and what to do?", .edit⟩
def rebuildsRecurringHelper : Atom := ⟨"rebuildsRecurringHelper",
  "Does this scratch script rebuild a recurring helper instead of extending a committed tool?", .edit⟩
def commitsScratchOutput : Atom := ⟨"commitsScratchOutput",
  "Does this commit add output a scratch script produced to a tracked record?", .call⟩
def readsBodyToLearn : Atom := ⟨"readsBodyToLearn",
  "Does this read of a tool's body serve learning to use it, rather than changing it?", .read⟩
def saysToolFallsShort : Atom := ⟨"saysToolFallsShort",
  "Does this reply say a tool of ours falls short of a job?", .reply⟩
def proposesToolReplacement : Atom := ⟨"proposesToolReplacement",
  "Does this reply propose replacing a tool of ours with another, or giving up something ours does?", .reply⟩
def listsWhatEachDoes : Atom := ⟨"listsWhatEachDoes",
  "Does this reply list what each tool does that the other doesn't?", .reply⟩
def offersKeepingOurs : Atom := ⟨"offersKeepingOurs",
  "Does this reply offer keeping our tool beside the replacement?", .reply⟩
def suiteRunOverLimit : Atom := ⟨"suiteRunOverLimit",
  "Does this result report the framework suite exceeding the runner's LIMIT_S?", .result⟩
def storesCollectedDataElsewhere : Atom := ⟨"storesCollectedDataElsewhere",
  "Does this call store data a tool collected for training or evaluation (theory passes, refusals, verdicts) anywhere but a tracked, append-only, one-record-per-line file?", .call⟩
def changesFileThroughShell : Atom := ⟨"changesFileThroughShell",
  "Does this shell call write or change a file (by sed, a heredoc, a redirect or a script)?", .call⟩
def readsPreparedFile : Atom := ⟨"readsPreparedFile",
  "Does this command read a file written for it by an earlier step?", .call⟩
def heredocNotFinalInput : Atom := ⟨"heredocNotFinalInput",
  "Does this call use a heredoc for anything but feeding a program's input as its last step?", .call⟩
def waitsOnBlockedJob : Atom := ⟨"waitsOnBlockedJob",
  "Does this wakeup wait on a blocked job, such as a running reviewer or a background batch?", .call⟩
def delayAboutSixty : Atom := ⟨"delayAboutSixty",
  "Is this wakeup's delay about 60 seconds?", .call⟩
def idlesUntilWakeup : Atom := ⟨"idlesUntilWakeup",
  "Does the agent stop working until this wakeup, rather than continuing and keeping it as a fallback?", .call⟩
def delayIsLong : Atom := ⟨"delayIsLong",
  "Is this wakeup's delay long (many minutes)?", .call⟩

/-! Links. -/

def commitsCoverLetter : Link := ⟨"commitsCoverLetter",
  "Does this commit commit the cover letter of the branch the anchored reply offers?"⟩
def commitsArtifact : Link := ⟨"commitsArtifact",
  "Does this commit commit, somewhere durable, the artifact the anchored reply reports finished?"⟩
def writesPushedDocument : Link := ⟨"writesPushedDocument",
  "Does this edit write, in Markdown in this workspace, the document the anchored call pushes to Confluence?"⟩
def commitsBugDoc : Link := ⟨"commitsBugDoc",
  "Does this commit commit the bug write-up the anchored edit writes?"⟩
def referencesBugDoc : Link := ⟨"referencesBugDoc",
  "Does this edit of PLAN.md reference the bug write-up the anchored edit writes?"⟩
def removesBugDoc : Link := ⟨"removesBugDoc",
  "Does this git rm remove the bug write-up the anchored reply says is tracked elsewhere?"⟩
def weighsSlowTests : Link := ⟨"weighsSlowTests",
  "Does this reply weigh the runner's list of tests of a second or more, for the cycle the anchored checkpoint ends?"⟩
def measuresParallelSuiteTime : Link := ⟨"measuresParallelSuiteTime",
  "Does this result measure the parallel suite time the anchored edit's budget derives from?"⟩
def smallestTimingOfFix : Link := ⟨"smallestTimingOfFix",
  "Is this result the smallest timing showing the speed fix the anchored reply claims?"⟩
def fullSuiteRunOfFix : Link := ⟨"fullSuiteRunOfFix",
  "Is this result a full suite run made once, at the end of the speed fix the anchored reply claims?"⟩
def readsNamedPromptSection : Link := ⟨"readsNamedPromptSection",
  "Does this read cover the PROMPTS.md section of the prompt the anchored call acts on?"⟩
def statesCycleTest : Link := ⟨"statesCycleTest",
  "Does this reply state, for the cycle the anchored call opens, the missing implication, how the cycle tests it, and the evidence that ends the test?"⟩
def readsNextStepItems : Link := ⟨"readsNextStepItems",
  "Does this call read in full the parked or linked items Proposed next step names on the route of the anchored entry?"⟩
def searchesReopenedAnchor : Link := ⟨"searchesReopenedAnchor",
  "Does this search look for later links to the anchor of the question the anchored reply reopens?"⟩
def readsLaterEntries : Link := ⟨"readsLaterEntries",
  "Does this call read the later entries linking to the question the anchored reply reopens?"⟩
def sameRouteEntry : Link := ⟨"sameRouteEntry",
  "Is this entry on the same route as the anchored entry?"⟩
def comparesStepOptions : Link := ⟨"comparesStepOptions",
  "Does this reply compare lower-bound constructions, method repairs and structural restrictions by their effect on the missing implication, for the step the anchored reply chooses?"⟩
def decidesSeriesPrediction : Link := ⟨"decidesSeriesPrediction",
  "Does this result pass or fail the prediction of the series the anchored call extends, at the sizes that test it?"⟩
def combinesWitnessesForFit : Link := ⟨"combinesWitnessesForFit",
  "Does this call combine the computed witnesses by every recorded composition rule, for the formula the anchored reply fits?"⟩
def searchesForProposal : Link := ⟨"searchesForProposal",
  "Does this search look for the step or result the anchored reply proposes or names?"⟩
def searchesLemmaByTechnique : Link := ⟨"searchesLemmaByTechnique",
  "Does this search look for the anchored reply's lemma by its technique's name?"⟩
def searchesLemmaBySynonyms : Link := ⟨"searchesLemmaBySynonyms",
  "Does this search look for the anchored reply's lemma by the record's synonyms and structural names?"⟩
def searchesLemmaDual : Link := ⟨"searchesLemmaDual",
  "Does this search look for the dual or adjoint formulation of the anchored reply's lemma?"⟩
def searchesLemmaContentWords : Link := ⟨"searchesLemmaContentWords",
  "Does this search look for the anchored reply's lemma by its statement's content words?"⟩
def testsLemmaAgainstObstructions : Link := ⟨"testsLemmaAgainstObstructions",
  "Does this call test the anchored reply's lemma against the recorded counterexamples, refutations and obstructions?"⟩
def checksRecordImpliesLemma : Link := ⟨"checksRecordImpliesLemma",
  "Does this call check whether the record already implies the lemma the anchored edit proves?"⟩
def checksFewerHypothesisResult : Link := ⟨"checksFewerHypothesisResult",
  "Does this call look for an earlier result under fewer hypotheses than the corollary the anchored edit drafts?"⟩
def inspectsDirectionClaims : Link := ⟨"inspectsDirectionClaims",
  "Does this graph call inspect the dependencies and correction and refinement links of the claims the anchored reply's direction rests on?"⟩
def marksGateIncomplete : Link := ⟨"marksGateIncomplete",
  "Does this entry leave the verification gate incomplete for the reviewer the anchored reply says is unavailable?"⟩
def searchesForSuggestion : Link := ⟨"searchesForSuggestion",
  "Does this search look for the reviewer's suggestions the anchored entry lists?"⟩
def answersEarlierCheckpointStep : Link := ⟨"answersEarlierCheckpointStep",
  "Is this failed result the result of an earlier step of the checkpoint batch the anchored call continues?"⟩
def isWorkOfStartedTurn : Link := ⟨"isWorkOfStartedTurn",
  "Is this call work of the turn the anchored start instruments?"⟩
def disclosesUninstrumentedWork : Link := ⟨"disclosesUninstrumentedWork",
  "Does this entry disclose the work done before the anchored start?"⟩
def sameQueueItem : Link := ⟨"sameQueueItem",
  "Does this entry develop the same queue item as the anchored entry?"⟩
def sameReview : Link := ⟨"sameReview",
  "Is this brief for the same review as the anchored one?"⟩
def comparesQueueTextWithDiscussion : Link := ⟨"comparesQueueTextWithDiscussion",
  "Does this reply compare the anchored call's queue text with what was said, finding each decisive point in it?"⟩
def testsNewIdea : Link := ⟨"testsNewIdea",
  "Does this call test a new idea proposed after the anchored reply found every route closed?"⟩
def surfacesCandidate : Link := ⟨"surfacesCandidate",
  "Does this reply surface to the user the significance candidate the anchored call raised?"⟩
def passesPatternGate : Link := ⟨"passesPatternGate",
  "Does this call pass the pattern verification gate for the pattern whose status the anchored edit writes?"⟩
def readsFormalizationGaps : Link := ⟨"readsFormalizationGaps",
  "Does this call read the Gaps identified by formalization section of the notebook the anchored resume restores?"⟩
def sendsProposedOverviewChange : Link := ⟨"sendsProposedOverviewChange",
  "Does this call send the coordinator the proposed overview changes and discrepancies of the anchored entry?"⟩
def commitsTurnRecords : Link := ⟨"commitsTurnRecords",
  "Does this commit hold the anchored turn's living sections, record, sources, provenance, code, data and important outputs?"⟩
def resolvesReportedConflict : Link := ⟨"resolvesReportedConflict",
  "Does this call resolve the conflict the anchored result reports?"⟩
def readsSourceFrameworkDiff : Link := ⟨"readsSourceFrameworkDiff",
  "Does this call read the source's framework changes since the previous merge, for the merge the anchored commit concludes?"⟩
def rerunsKeyFrameworkTests : Link := ⟨"rerunsKeyFrameworkTests",
  "Does this call rerun the key tests of the source's framework changes the anchored commit merges?"⟩
def checksDestinationHeadAndTree : Link := ⟨"checksDestinationHeadAndTree",
  "Does this call check, immediately before it, the HEAD and worktree of the destination the anchored fast-forward moves?"⟩
def showsDestinationAdvanced : Link := ⟨"showsDestinationAdvanced",
  "Does this result show that the destination the anchored fast-forward moves has advanced?"⟩
def backsUpRebasedBranch : Link := ⟨"backsUpRebasedBranch",
  "Does this call create a backup branch of the branch the anchored call rebases?"⟩
def filesThisRequest : Link := ⟨"filesThisRequest",
  "Does this call file the request the anchored reply asks of the user?"⟩
def mentionsRequest : Link := ⟨"mentionsRequest",
  "Does this reply mention in one sentence the request the anchored call filed?"⟩
def marksRequestFulfilled : Link := ⟨"marksRequestFulfilled",
  "Does this call mark fulfilled the request the anchored user message answers?"⟩
def makesNamedPrevention : Link := ⟨"makesNamedPrevention",
  "Does this edit make the framework change the anchored reply's Prevention names?"⟩
def commitsFixForFrustration : Link := ⟨"commitsFixForFrustration",
  "Does this commit commit a fix, preferably a mechanical check, of the process the anchored user message is frustrated with?"⟩
def reviewsOldAgainstNew : Link := ⟨"reviewsOldAgainstNew",
  "Does this agent give a fresh-context review of the old against the new text of the anchored commit's instruction files?"⟩
def raisesCapForRule : Link := ⟨"raisesCapForRule",
  "Does this edit raise the file's cap by what the anchored commit's rule adds, with a raised entry naming the rule?"⟩
def turnsScriptIntoTool : Link := ⟨"turnsScriptIntoTool",
  "Does this edit make the scratch script whose output the anchored commit adds a tested framework tool?"⟩
def improvesThatTool : Link := ⟨"improvesThatTool",
  "Does this edit improve the tool the anchored reply says falls short?"⟩
def buildsSmallestGapChange : Link := ⟨"buildsSmallestGapChange",
  "Does this edit build the smallest change to our tool closing the gap the anchored reply weighs?"⟩
def measuresBothTools : Link := ⟨"measuresBothTools",
  "Does this result measure both tools the anchored reply compares?"⟩
def fixesSuiteSlowness : Link := ⟨"fixesSuiteSlowness",
  "Does this edit fix the cause of the slow suite run the anchored result reports?"⟩
def writesFileTheCallReads : Link := ⟨"writesFileTheCallReads",
  "Does this Write or Edit write the file the anchored command reads?"⟩

/-! Formulas shared by several rules. -/

/-- An entry appended on the anchor's route. -/
def entryOnRoute : Formula := ev entryAppend ∧ₗ link sameRouteEntry

/-- An entry appended on the anchor's queue item declaring no bearing. -/
def noBearingOnItem : Formula := ev entryAppend ∧ₗ atom declaresBearingNone ∧ₗ link sameQueueItem

/-- A notebook or claim edit made after the finisher and before the commit. -/
def editAfterFinisher : Formula := ev notebookOrClaimEdit ∧ₗ since (ev finishTurn) (ev gitCommit)

/-- A reviewer spawned for a research cycle. -/
def reviewerSpawn : Formula := ev agentRun ∧ₗ atom isReviewerSpawn

/-! Rules 701 to 716: artifacts, test speed, the queue's settings. -/

/-- Rule 701: clean, logically split commits; a committed cover letter in the skill's format for a
branch of several commits. -/
def r701 : Rule where
  number := 701
  keyword := .must
  domain := .tasks
  formula := (ev gitCommit ⟹ atom oneLogicalChange) ∧ₗ
    (ev reply ∧ₗ atom offersMultiCommitBranch ⟹
      once (ev coverLetterEdit ∧ₗ atom inCoverLetterFormat) ∧ₗ once (ev gitCommit ∧ₗ link commitsCoverLetter))

/-- Rule 702: the ledger before the letter is offered; a version note with ledger rows after a
rework. -/
def r702 : Rule where
  number := 702
  keyword := .must
  domain := .tasks
  formula := (ev reply ∧ₗ atom offersCoverLetter ⟹ once (ev ledgerEdit)) ∧ₗ
    (ev reply ∧ₗ atom offersReworkedBranch ⟹
      once (ev coverLetterEdit ∧ₗ atom addsVersionNote) ∧ₗ once (ev ledgerEdit ∧ₗ atom addsVersionNoteRows))

/-- Rule 703: another kind of artifact committed durably, honest about what was achieved. -/
def r703 : Rule where
  number := 703
  keyword := .must
  domain := .tasks
  formula := (ev reply ∧ₗ atom reportsOtherArtifactDone ⟹ once (ev gitCommit ∧ₗ link commitsArtifact)) ∧ₗ
    (ev editing ∧ₗ atom writesOtherArtifact ⟹ atom statesWhatWasNotAchieved)

/-- Rule 704: a Confluence page written in Markdown here and pushed with `confluence_page.py`. -/
def r704 : Rule where
  number := 704
  keyword := .must
  domain := .tasks
  formula := (atom writesConfluencePage ⟹ ev confluencePush) ∧ₗ
    (ev confluencePush ⟹ once (ev editing ∧ₗ link writesPushedDocument))

/-- Rule 705: a tangential bug written up, committed and referenced from PLAN.md, the task resumed,
the write-up removed once tracked elsewhere. -/
def r705 : Rule where
  number := 705
  keyword := .must
  domain := .discipline
  formula := (ev reply ∧ₗ atom findsTangentialBug ⟹ eventually (ev bugDocEdit)) ∧ₗ
    (ev bugDocEdit ⟹ eventually (ev gitCommit ∧ₗ link commitsBugDoc) ∧ₗ
      eventually (ev planEdit ∧ₗ link referencesBugDoc) ∧ₗ eventually (atom worksOnTask)) ∧ₗ
    (ev reply ∧ₗ atom saysBugTrackedElsewhere ⟹ eventually (ev gitRm ∧ₗ link removesBugDoc))

/-- Rule 707: a whole pytest suite through `pytest_queue.py`, another suite through its
ecosystem's parallel runner. -/
def r707 : Rule where
  number := 707
  keyword := .must
  domain := .tasks
  formula := never (ev pytestRun ∧ₗ atom runsWholeSuite) ∧ₗ never (atom runsSuiteSerially)

/-- Rule 708: tests using a service get one per worker with `--isolate`. -/
def r708 : Rule where
  number := 708
  keyword := .must
  domain := .tasks
  formula := ev pytestQueue ∧ₗ atom suiteUsesService ⟹ ev pytestQueueIsolated

/-- Rule 709: each test checks one thing. -/
def r709 : Rule where
  number := 709
  keyword := .must
  domain := .tasks
  formula := never (ev testEdit ∧ₗ atom testChecksSeveralThings)

/-- Rule 710: the list of slow tests read at each checkpoint. -/
def r710 : Rule where
  number := 710
  keyword := .should
  domain := .tasks
  formula := ev taskCheckpoint ⟹ once (ev reply ∧ₗ link weighsSlowTests) ∨ₗ atom justified

/-- Rule 711: a suite budget near one and a half times the measured parallel time. -/
def r711 : Rule where
  number := 711
  keyword := .must
  domain := .tasks
  formula := ev editing ∧ₗ atom setsSuiteBudget ⟹
    atom budgetNearOneAndHalf ∧ₗ once (ev passingResult ∧ₗ link measuresParallelSuiteTime)

/-- Rule 712: the suite's time recorded at each checkpoint, a reason given when it grew by more
than a fifth. -/
def r712 : Rule where
  number := 712
  keyword := .must
  domain := .tasks
  formula := ev taskCheckpoint ⟹
    ev checkpointWithSuite ∧ₗ (atom suiteGrewOverFifth ⟹ ev checkpointSlowReason)

/-- Rule 713: a speed fix shown by the smallest timing, the full suite run once at the end. -/
def r713 : Rule where
  number := 713
  keyword := .should
  domain := .tasks
  formula := ev reply ∧ₗ atom claimsSpeedFix ⟹
    once (ev passingResult ∧ₗ link smallestTimingOfFix) ∧ₗ once (ev passingResult ∧ₗ link fullSuiteRunOfFix) ∨ₗ
      atom justified

/-- Rule 714: only the touched test files during a cycle, the whole suite at the checkpoint. -/
def r714 : Rule where
  number := 714
  keyword := .should
  domain := .tasks
  formula := (atom runsUntouchedTests ⟹ atom justified) ∧ₗ
    (ev taskCheckpoint ⟹ once (atom runsWholeSuite) ∨ₗ atom justified)

/-- Rule 715: mutants in one `mutation_batch.py` call, its specs kept with the evidence. -/
def r715 : Rule where
  number := 715
  keyword := .must
  domain := .tasks
  formula := (atom runsMutants ⟹ ev mutationBatch) ∧ₗ (ev mutationBatch ⟹ atom specsWithEvidence)

/-- Rule 716: the queue counts task entries, with backpressure off. -/
def r716 : Rule where
  number := 716
  keyword := .must
  domain := .tasks
  formula := never (ev notebookEdit ∧ₗ atom changesQueueCounting)

/-! Rules 717 to 756: restoration and the research discipline. -/

/-- Rule 717: restoration through `resume.py`, its parts read. -/
def r717 : Rule where
  number := 717
  keyword := .must
  domain := .discipline
  formula := (ev user ∧ₗ atom asksToRestoreContext ⟹ eventually (ev resumeRun)) ∧ₗ
    (ev resumeRun ⟹ eventually (ev resumePartRead))

/-- Rule 718: the named prompt's PROMPTS.md section read before acting on it. -/
def r718 : Rule where
  number := 718
  keyword := .must
  domain := .discipline
  formula := atom actsOnNamedPrompt ⟹ once (ev promptsRead ∧ₗ link readsNamedPromptSection)

/-- Rule 719: no wholesale load of the record or the index. -/
def r719 : Rule where
  number := 719
  keyword := .mustNot
  domain := .discipline
  formula := never (ev wholeRecordRead ∨ₗ atom loadsRecordWholesale)

/-- Rule 720: the task protocol read before a task's work and after every resume. -/
def r720 : Rule where
  number := 720
  keyword := .must
  domain := .tasks
  formula := ev editing ∧ₗ atom taskInProgress ⟹ since (ev protocolRead) (ev resumeRun)

/-- Rule 721: AIFI.md read before an AiFi task's work. -/
def r721 : Rule where
  number := 721
  keyword := .must
  domain := .tasks
  formula := ev editing ∧ₗ atom aifiTaskInProgress ⟹ once (ev aifiRead)

/-- Rule 722: a research cycle opens by stating its missing implication and its test: the reply
stating them comes before the cycle's first edit. -/
def r722 : Rule where
  number := 722
  keyword := .must
  domain := .mathematics
  formula := ev cycleStart ∧ₗ atom startsResearchCycle ⟹
    eventually (ev reply ∧ₗ link statesCycleTest ∧ₗ since (ev cycleStart) (ev editing))

/-- Rule 723: Open statements read first in the cycle, before its first edit; the entry names what
it advances. -/
def r723 : Rule where
  number := 723
  keyword := .must
  domain := .mathematics
  formula :=
    (ev entryAppend ∧ₗ atom isResearchEntry ⟹
      since (atom readsOpenStatements) (ev cycleStart) ∧ₗ atom namesAdvancedStatement) ∧ₗ
    (ev editing ⟹ ¬ₗ since (ev cycleStart ∧ₗ atom startsResearchCycle) (atom readsOpenStatements))

/-- Rule 724: obligations first, then the review's highest risk. -/
def r724 : Rule where
  number := 724
  keyword := .should
  domain := .mathematics
  formula := ev reply ∧ₗ atom choosesNextStep ⟹ atom choosesByObligationThenRisk ∨ₗ atom justified

/-- Rule 725: the items Proposed next step names, read in full. -/
def r725 : Rule where
  number := 725
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ∧ₗ atom isResearchEntry ⟹ once (ev anyCall ∧ₗ link readsNextStepItems)

/-- Rule 726: later links to an older question searched and read before reopening it. -/
def r726 : Rule where
  number := 726
  keyword := .must
  domain := .mathematics
  formula := ev reply ∧ₗ atom reopensOlderQuestion ⟹
    once (ev backlinksSearch ∧ₗ link searchesReopenedAnchor) ∧ₗ once (ev anyCall ∧ₗ link readsLaterEntries)

/-- Rule 727: restricted examples test a named general hypothesis. -/
def r727 : Rule where
  number := 727
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ∧ₗ atom reportsRestrictedExamples ⟹ atom namesGeneralHypothesis

/-- Rule 728: a General statement paragraph citing the all-parameter claim. -/
def r728 : Rule where
  number := 728
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ∧ₗ atom isResearchEntry ⟹ atom hasGeneralStatement

/-- Rule 729: no two finite-check-only entries in a row on a route, nor finite checks in more than
three of five. -/
def r729 : Rule where
  number := 729
  keyword := .mustNot
  domain := .mathematics
  formula := never (ev entryAppend ∧ₗ atom finiteCheckOnly ∧ₗ
      since (entryOnRoute ∧ₗ atom finiteCheckOnly) entryOnRoute) ∧ₗ
    never (ev entryAppend ∧ₗ atom exceedsFiniteCheckShare)

/-- Rule 730: after two entries leaving the implication untouched, another mechanism, recorded for
the review. -/
def r730 : Rule where
  number := 730
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ∧ₗ atom leavesImplicationUntouched ∧ₗ
      since (entryOnRoute ∧ₗ atom leavesImplicationUntouched) entryOnRoute ⟹
    eventually (entryOnRoute ∧ₗ atom usesDifferentMechanism ∧ₗ atom recordsForScheduledReview)

/-- Rule 731: the standing hypotheses rechecked every cycle. -/
def r731 : Rule where
  number := 731
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ∧ₗ atom isResearchEntry ⟹ atom rechecksStandingHypotheses

/-- Rule 732: an excluding upper bound's structural reason, its reach and its lesson. -/
def r732 : Rule where
  number := 732
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ∧ₗ atom reportsUpperBoundExclusion ⟹
    atom extractsStructuralReason ∧ₗ atom checksOtherCandidates ∧ₗ atom recordsBoundLesson

/-- Rule 733: a specification refinement adopted with a non-vacuity witness, else provisional. -/
def r733 : Rule where
  number := 733
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ∧ₗ atom adoptsSpecRefinement ⟹
    atom provesNonVacuityWitness ∨ₗ atom marksRefinementProvisional

/-- Rule 734: the step options compared before choosing. -/
def r734 : Rule where
  number := 734
  keyword := .should
  domain := .mathematics
  formula := ev reply ∧ₗ atom choosesNextStep ⟹ once (ev reply ∧ₗ link comparesStepOptions) ∨ₗ atom justified

/-- Rule 735: no larger size once the series' prediction is decided, unless a new question needs
it. -/
def r735 : Rule where
  number := 735
  keyword := .must
  domain := .mathematics
  formula := atom runsLargerSize ⟹
    ¬ₗ once (ev anyResult ∧ₗ link decidesSeriesPrediction) ∨ₗ atom namesQuestionChangingImplication

/-- Rule 736: witnesses combined by the composition rules before a formula is fitted. -/
def r736 : Rule where
  number := 736
  keyword := .must
  domain := .mathematics
  formula := ev reply ∧ₗ atom fitsFormula ⟹ once (ev anyCall ∧ₗ link combinesWitnessesForFit)

/-- Rule 737: the claims searched before a next step is proposed or a result named. -/
def r737 : Rule where
  number := 737
  keyword := .must
  domain := .mathematics
  formula := ev reply ∧ₗ atom proposesStepOrNamesResult ⟹ once (ev searchClaims ∧ₗ link searchesForProposal)

/-- Rule 738: a new lemma searched four ways and tested against recorded obstructions. -/
def r738 : Rule where
  number := 738
  keyword := .must
  domain := .mathematics
  formula := ev reply ∧ₗ atom formulatesNewLemma ⟹
    once (ev searchClaims ∧ₗ link searchesLemmaByTechnique) ∧ₗ
    once (ev searchClaims ∧ₗ link searchesLemmaBySynonyms) ∧ₗ
    once (ev searchClaims ∧ₗ link searchesLemmaDual) ∧ₗ
    once (ev searchClaims ∧ₗ link searchesLemmaContentWords) ∧ₗ
    once (ev anyCall ∧ₗ link testsLemmaAgainstObstructions)

/-- Rule 739: the record checked for the lemma, and for a corollary's weaker-hypothesis original,
before drafting. -/
def r739 : Rule where
  number := 739
  keyword := .must
  domain := .mathematics
  formula := (ev editing ∧ₗ atom draftsLemmaProof ⟹ once (ev anyCall ∧ₗ link checksRecordImpliesLemma)) ∧ₗ
    (ev editing ∧ₗ atom draftsCorollary ⟹ once (ev anyCall ∧ₗ link checksFewerHypothesisResult))

/-- Rule 740: compositions as complete lemmas in one setting. -/
def r740 : Rule where
  number := 740
  keyword := .must
  domain := .mathematics
  formula := ev editing ∧ₗ atom writesComposition ⟹ atom compositionIsCompleteLemma

/-- Rule 741: the claim graph inspected before committing to a direction. -/
def r741 : Rule where
  number := 741
  keyword := .must
  domain := .mathematics
  formula := ev reply ∧ₗ atom commitsToDirection ⟹ once (ev claimGraph ∧ₗ link inspectsDirectionClaims)

/-- Rule 742: rediscoveries and refinements labelled and linked. -/
def r742 : Rule where
  number := 742
  keyword := .must
  domain := .mathematics
  formula := ev editing ∧ₗ atom recordsRediscoveryOrRefinement ⟹ atom labelsAndLinksOriginal

/-- Rule 743: at most one fresh reviewer a cycle, given only stable drafts and excerpts. -/
def r743 : Rule where
  number := 743
  keyword := .must
  domain := .mathematics
  formula := reviewerSpawn ⟹ ¬ₗ since reviewerSpawn (ev cycleStart) ∧ₗ atom givenOnlyStableDrafts

/-- Rule 744: reviewers at medium effort, the medium-reviewer type in Claude Code. -/
def r744 : Rule where
  number := 744
  keyword := .must
  domain := .mathematics
  formula := reviewerSpawn ⟹ ev reviewerRun ∨ₗ atom spawnsCodexMediumReviewer

/-- Rule 745: no higher-effort substitute; the gate left incomplete and a request filed. -/
def r745 : Rule where
  number := 745
  keyword := .mustNot
  domain := .mathematics
  formula := never (ev agentRun ∧ₗ atom isHigherEffortReviewer) ∧ₗ
    (ev reply ∧ₗ atom saysMediumUnavailable ⟹
      eventually (ev entryAppend ∧ₗ link marksGateIncomplete) ∧ₗ eventually (ev userRequestFiled))

/-- Rule 746: no root session for a review. -/
def r746 : Rule where
  number := 746
  keyword := .mustNot
  domain := .mathematics
  formula := never (atom startsRootSessionForReview)

/-- Rule 747: a narrow reviewer brief asking for a process audit. -/
def r747 : Rule where
  number := 747
  keyword := .must
  domain := .mathematics
  formula := reviewerSpawn ⟹ atom briefNamesExactAnchors ∧ₗ atom briefAtMostTwoSearches ∧ₗ
    atom briefExcerptsInScratchFile ∧ₗ atom briefChangesAsBullets ∧ₗ atom briefAsksProcessAudit

/-- Rule 748: no novelty reviewer, no reviewer beyond the cycle's one. -/
def r748 : Rule where
  number := 748
  keyword := .mustNot
  domain := .mathematics
  formula := never (ev agentRun ∧ₗ atom isNoveltyReviewer) ∧ₗ
    never (reviewerSpawn ∧ₗ since reviewerSpawn (ev cycleStart))

/-- Rule 749: reviewer suggestions under their heading, each ending in a prior search's outcome. -/
def r749 : Rule where
  number := 749
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ∧ₗ atom hasReviewerSuggestions ⟹
    atom suggestionsUnderUnverifiedHeading ∧ₗ atom eachSuggestionEndsRecord ∧ₗ
      once (ev searchClaims ∧ₗ link searchesForSuggestion)

/-- Rule 750: a Verification gate paragraph. -/
def r750 : Rule where
  number := 750
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ∧ₗ atom isResearchEntry ⟹ atom hasVerificationGate

/-- Rule 751: the checkpoint batch one step at a time, stopped at a failure, finished before the
next result. -/
def r751 : Rule where
  number := 751
  keyword := .must
  domain := .mathematics
  formula := never (sameMessage checkpointStepsTogether) ∧ₗ
    (ev checkpointStepCall ⟹ ¬ₗ since (ev failedResult ∧ₗ link answersEarlierCheckpointStep) (ev editing)) ∧ₗ
    (ev editing ∧ₗ atom developsNextResult ⟹
      ¬ₗ since (ev checkpointStepCall ∧ₗ ¬ₗ ev gitCommit) (ev gitCommit))

/-- Rule 752: `check_records.py --diff` before the research checkpoint's commit. -/
def r752 : Rule where
  number := 752
  keyword := .must
  domain := .mathematics
  formula := ev gitCommit ∧ₗ atom isResearchCheckpointCommit ⟹ since (ev checkRecordsDiff) (ev gitCommit)

/-- Rule 753: a research turn's computation measured from a `compute.sh start`. -/
def r753 : Rule where
  number := 753
  keyword := .must
  domain := .mathematics
  formula := atom runsComputation ∧ₗ atom inResearchTurn ⟹ once (ev cycleStart)

/-- Rule 754: work before the instrumentation disclosed. -/
def r754 : Rule where
  number := 754
  keyword := .must
  domain := .mathematics
  formula := ev cycleStart ∧ₗ once (ev anyCall ∧ₗ link isWorkOfStartedTurn) ⟹
    eventually (ev entryAppend ∧ₗ link disclosesUninstrumentedWork)

/-- Rule 755: full output kept on disk, bounded excerpts shown, no PNG preview unasked. -/
def r755 : Rule where
  number := 755
  keyword := .must
  domain := .mathematics
  formula := never (atom discardsFullOutput ∨ₗ atom displaysUnboundedOutput) ∧ₗ
    (ev pngRead ⟹ once (ev user ∧ₗ atom requestsPngPreview))

/-- Rule 756: site and rendering checks only for layout or tool changes or a rendering concern. -/
def r756 : Rule where
  number := 756
  keyword := .should
  domain := .mathematics
  formula := atom runsRenderingCheck ⟹ atom hasLayoutChangeOrConcern ∨ₗ atom justified

/-! Rules 757 to 806: goal progress, reviews, the notebook. -/

/-- Rule 757: six research entries, then one review; no extra reviews or reviewers. -/
def r757 : Rule where
  number := 757
  keyword := .must
  domain := .mathematics
  formula := never (ev entryAppend ∧ₗ atom breaksReviewCadence) ∧ₗ
    never (ev agentRun ∧ₗ atom isExtraCadenceReviewer)

/-- Rule 758: data-obligation and data-goal-progress on each research or review entry. -/
def r758 : Rule where
  number := 758
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ∧ₗ atom isResearchOrReviewEntry ⟹ atom hasObligationAndProgressAttrs

/-- Rule 759: separate New mathematics and Goal progress paragraphs. -/
def r759 : Rule where
  number := 759
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ∧ₗ atom isResearchOrReviewEntry ⟹ atom hasNewMathAndGoalProgress

/-- Rule 760: from the third unchanged entry in a row on a route, a Bearing with a matching
attribute, and Not covered for some bearing. -/
def r760 : Rule where
  number := 760
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ∧ₗ atom reportsRouteUnchanged ∧ₗ
      since (entryOnRoute ∧ₗ atom reportsRouteUnchanged ∧ₗ
        since (entryOnRoute ∧ₗ atom reportsRouteUnchanged) entryOnRoute) entryOnRoute ⟹
    atom endsWithBearing ∧ₗ atom bearingAttrMatches ∧ₗ (atom bearingSome ⟹ atom hasNotCovered)

/-- Rule 761: after two entries in a row on one item declaring no bearing, another item. -/
def r761 : Rule where
  number := 761
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ⟹ ¬ₗ since (noBearingOnItem ∧ₗ since noBearingOnItem (ev entryAppend))
    (ev entryAppend)

/-- Rule 762: a Continuing follow-up inside such a run states its Record search. -/
def r762 : Rule where
  number := 762
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ∧ₗ atom declaresBearingNone ∧ₗ atom followUpContinuing ∧ₗ
      since noBearingOnItem (ev entryAppend) ⟹ atom statesRecordSearch

/-- Rule 763: an Architecture review section in each scheduled review. -/
def r763 : Rule where
  number := 763
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ∧ₗ atom isRouteReview ⟹ atom hasArchitectureReview

/-- Rule 764: the Independent alternative's medium reviewer given only the goal and excerpts, and
no second reviewer for it. -/
def r764 : Rule where
  number := 764
  keyword := .must
  domain := .mathematics
  formula := ev agentRun ∧ₗ atom isIndependentAlternativeBrief ⟹
    ev reviewerRun ∧ₗ atom withholdsPreferredRoute ∧ₗ
      ¬ₗ once (ev agentRun ∧ₗ atom isIndependentAlternativeBrief ∧ₗ link sameReview)

/-- Rule 765: earlier reviews' tests read first; the Decisive test with Power and Record search. -/
def r765 : Rule where
  number := 765
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ∧ₗ atom isRouteReview ⟹
    once (ev reviewTestsRead) ∧ₗ atom decisiveTestHasPowerAndRecordSearch

/-- Rule 766: the next research entry on the route reports the Architecture test. -/
def r766 : Rule where
  number := 766
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ∧ₗ atom isResearchEntry ∧ₗ
      since (entryOnRoute ∧ₗ atom isRouteReview) entryOnRoute ⟹ atom reportsArchitectureTest

/-- Rule 767: historical assessments left as written. -/
def r767 : Rule where
  number := 767
  keyword := .mustNot
  domain := .mathematics
  formula := never (ev notebookEdit ∧ₗ atom rewritesHistoricalEntry)

/-- Rule 768: the living sections reviewed in every research turn, before its finisher. -/
def r768 : Rule where
  number := 768
  keyword := .must
  domain := .mathematics
  formula := ev finishTurn ⟹ since (atom reviewsLivingSections) (ev finishTurn)

/-- Rule 769: Open statements at most about five, each with status and instances. -/
def r769 : Rule where
  number := 769
  keyword := .must
  domain := .mathematics
  formula := ev notebookEdit ∧ₗ atom editsOpenStatements ⟹ atom openStatementsWellFormed

/-- Rule 770: an entry for every research turn, with its mathematics in full. -/
def r770 : Rule where
  number := 770
  keyword := .must
  domain := .mathematics
  formula := (ev finishTurn ⟹ since (ev entryAppend) (ev finishTurn)) ∧ₗ
    (ev entryAppend ⟹ atom holdsFullMathematics)

/-- Rule 771: `notebook_context.py` while drafting; consolidation by the agent; a hard limit
raised only on the user's override. -/
def r771 : Rule where
  number := 771
  keyword := .must
  domain := .mathematics
  formula := (ev entryAppend ⟹ since (ev notebookContext) (ev finishTurn)) ∧ₗ
    never (ev reply ∧ₗ atom asksUserToConsolidate) ∧ₗ
    (ev editing ∧ₗ atom raisesHardBudget ⟹ once (ev user ∧ₗ atom overridesBudget))

/-- Rule 772: the selected notebook edited itself, its main sections never replaced by a side
goal. -/
def r772 : Rule where
  number := 772
  keyword := .must
  domain := .mathematics
  formula := never (ev editing ∧ₗ (atom replacesMainWithSideGoal ∨ₗ atom editsNotebookCopy))

/-- Rule 773: data-kind, data-route and data-claims on each article. -/
def r773 : Rule where
  number := 773
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ⟹ atom hasKindRouteClaimsTags

/-- Rule 774: a review's scope set by its line's open-item count. -/
def r774 : Rule where
  number := 774
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ∧ₗ atom isRouteReview ⟹ atom scopeMatchesOpenItemCount

/-- Rule 775: a review's required parts and Obstacle heading. -/
def r775 : Rule where
  number := 775
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ∧ₗ atom isRouteReview ⟹ atom reviewHasRequiredParts

/-- Rule 776: a non-draining review's leads and bridges. -/
def r776 : Rule where
  number := 776
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ∧ₗ atom isRouteReview ∧ₗ ¬ₗ atom queueDraining ⟹ atom hasLeadsAndBridges

/-- Rule 777: the review's cheap tests run in its cycle. -/
def r777 : Rule where
  number := 777
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ∧ₗ atom isRouteReview ⟹ atom cheapTestsRun

/-- Rule 778: the picks marked. -/
def r778 : Rule where
  number := 778
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ∧ₗ atom isRouteReview ⟹ atom marksPicks

/-- Rule 779: picks queued with `lead_queue.py`, never by hand. -/
def r779 : Rule where
  number := 779
  keyword := .must
  domain := .mathematics
  formula := (ev entryAppend ∧ₗ atom reviewHasPicks ⟹ eventually (ev leadQueueAppend)) ∧ₗ
    never (ev notebookEdit ∧ₗ atom editsQueueByHand)

/-- Rule 780: one top-level item per entry, the head unless Chosen says why. -/
def r780 : Rule where
  number := 780
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ∧ₗ atom isResearchEntry ⟹
    ¬ₗ atom developsSeveralItems ∧ₗ (atom developsNonHeadItem ⟹ atom hasChosenParagraph)

/-- Rule 781: an item rotated at its spell boundary unless an earned extension is recorded; no
refused work re-filed. -/
def r781 : Rule where
  number := 781
  keyword := .must
  domain := .mathematics
  formula := never (ev entryAppend ∧ₗ
    ((atom continuesItemPastSpell ∧ₗ ¬ₗ (atom recordsSpellExtension ∧ₗ atom extensionEarnedByProgress)) ∨ₗ
      atom refilesRefusedWork))

/-- Rule 782: a lead entry's tag and follow-up. -/
def r782 : Rule where
  number := 782
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ∧ₗ atom developsQueueItem ⟹ atom hasLeadTagAndFollowUp

/-- Rule 783: a closure's Stakes, record link and Sources read. -/
def r783 : Rule where
  number := 783
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ∧ₗ atom closesQueueItem ⟹ atom closureHasStakesLinkSources

/-- Rule 784: a closure for a found reason, made without asking the user. -/
def r784 : Rule where
  number := 784
  keyword := .must
  domain := .mathematics
  formula := (ev entryAppend ∧ₗ atom closesQueueItem ⟹ atom closureReasonFoundByAttempt) ∧ₗ
    (ev reply ∧ₗ atom asksUserToCloseItem ⟹ atom justified)

/-- Rule 786: one item's development finished before the next item's starts. -/
def r786 : Rule where
  number := 786
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ∧ₗ atom developsQueueItem ⟹
    ¬ₗ since (ev entryAppend ∧ₗ atom leavesItemUnfinished ∧ₗ ¬ₗ link sameQueueItem) (ev entryAppend)

def leavesUndoneOutsideSubIdeas : Atom := ⟨"leavesUndoneOutsideSubIdeas",
  "Does the entry this call appends name undone work it means to carry out anywhere but under its Sub-ideas?", .call⟩

/-- Rule 787: no leads or bridges sections in a research entry; its undone work under Sub-ideas. -/
def r787 : Rule where
  number := 787
  keyword := .mustNot
  domain := .mathematics
  formula := never (ev entryAppend ∧ₗ atom isResearchEntry ∧ₗ atom hasOwnLeadsSections) ∧ₗ
    never (ev entryAppend ∧ₗ atom isResearchEntry ∧ₗ atom leavesUndoneOutsideSubIdeas)

/-- Rule 788: a reopened item with its Reopened follow-up, appended to the tail. -/
def r788 : Rule where
  number := 788
  keyword := .must
  domain := .mathematics
  formula := atom reopensClosedItem ⟹ atom hasReopenedFollowUp ∧ₗ eventually (ev leadQueueAppend)

/-- Rule 789: Sub-ideas only for undone work that will be done. -/
def r789 : Rule where
  number := 789
  keyword := .must
  domain := .mathematics
  formula := never (ev entryAppend ∧ₗ atom listsUnfitSubIdea)

/-- Rule 790: a check or build filed with Problem and Must parts, readable alone, compared with
what was said. -/
def r790 : Rule where
  number := 790
  keyword := .must
  domain := .mathematics
  formula := ev leadQueueAdd ⟹ ev queueTextHasProblemMust ∧ₗ atom queueTextReadableAlone ∧ₗ
    once (ev reply ∧ₗ link comparesQueueTextWithDiscussion)

/-- Rule 791: items closed with `lead_queue.py close`, duplicates as merged. -/
def r791 : Rule where
  number := 791
  keyword := .must
  domain := .mathematics
  formula := (atom closesQueueItemOtherwise ⟹ ev leadQueueClose) ∧ₗ
    (ev leadQueueClose ∧ₗ atom closesDuplicate ⟹ ev closeSaysMergedInto)

/-- Rule 792: Developed only on evidence, a build only with its task or path. -/
def r792 : Rule where
  number := 792
  keyword := .must
  domain := .mathematics
  formula := (atom marksCheckDeveloped ⟹ atom citesResolvingEvidence) ∧ₗ
    (atom marksBuildDeveloped ⟹ atom citesTaskOrPath)

/-- Rule 793: a draining queue's head developed, reviews without leads meanwhile. -/
def r793 : Rule where
  number := 793
  keyword := .must
  domain := .mathematics
  formula := (ev entryAppend ∧ₗ atom isResearchEntry ∧ₗ atom queueDraining ⟹ atom developsHeadOrFirstSubIdea) ∧ₗ
    never (ev entryAppend ∧ₗ atom isRouteReview ∧ₗ atom queueDraining ∧ₗ atom hasOwnLeadsSections)

/-- Rule 794: Proposed next step names a route item and stays research; closed routes call for a
new idea, tested. -/
def r794 : Rule where
  number := 794
  keyword := .must
  domain := .mathematics
  formula := (ev notebookEdit ∧ₗ atom editsProposedNextStep ⟹ atom namesRouteItemResearchStep) ∧ₗ
    (ev reply ∧ₗ atom saysRoutesClosed ⟹ eventually (ev anyCall ∧ₗ link testsNewIdea))

/-- Rule 795: an authorized Spin continues until the goal is proved. -/
def r795 : Rule where
  number := 795
  keyword := .must
  domain := .mathematics
  formula := ev reply ∧ₗ atom spinActive ∧ₗ atom endsTurn ⟹ atom goalProved

/-- Rule 796: after a low-yield cycle, a correction or a hard step, the latest review's leads. -/
def r796 : Rule where
  number := 796
  keyword := .should
  domain := .mathematics
  formula := ev entryAppend ∧ₗ since (ev entryAppend ∧ₗ atom lowYieldCorrectionOrHardStep) (ev entryAppend) ⟹
    atom developsReviewLead ∨ₗ atom justified

/-- Rule 797: claims registered with `author build`, the index owning metadata, views rendered. -/
def r797 : Rule where
  number := 797
  keyword := .must
  domain := .mathematics
  formula := (atom registersClaim ⟹ ev claimAuthorBuild) ∧ₗ never (ev claimViewEdit) ∧ₗ
    (ev claimIndexEdit ⟹ eventually (ev claimRender))

/-- Rule 798: a claim's metadata complete, new candidates surfaced. -/
def r798 : Rule where
  number := 798
  keyword := .must
  domain := .mathematics
  formula := (atom writesClaimMetadata ⟹ atom claimMetadataComplete) ∧ₗ
    (atom raisesSignificanceCandidate ⟹ eventually (ev reply ∧ₗ link surfacesCandidate))

/-- Rule 799: a refines edge only with an implication. -/
def r799 : Rule where
  number := 799
  keyword := .must
  domain := .mathematics
  formula := never (atom addsRefinesWithoutImplication)

/-- Rule 800: the pattern index searched before a pattern; the gate passed before its status. -/
def r800 : Rule where
  number := 800
  keyword := .must
  domain := .mathematics
  formula := (ev reply ∧ₗ atom proposesPattern ⟹ once (ev patternIndexRead)) ∧ₗ
    (ev editing ∧ₗ atom writesPatternStatus ⟹ once (ev anyCall ∧ₗ link passesPatternGate))

/-- Rule 801: the formalization gaps read on restoration. -/
def r801 : Rule where
  number := 801
  keyword := .must
  domain := .mathematics
  formula := ev resumeRun ∧ₗ atom notebookHasFormalizationGaps ⟹
    eventually (ev anyCall ∧ₗ link readsFormalizationGaps)

/-- Rule 802: in coordinated parallel formalization the coordinator alone edits living sections;
workers append records and send their proposals. -/
def r802 : Rule where
  number := 802
  keyword := .must
  domain := .mathematics
  formula := never (ev notebookEdit ∧ₗ atom isFormalizationWorker ∧ₗ atom editsLivingSection) ∧ₗ
    (ev entryAppend ∧ₗ atom isFormalizationWorker ⟹ eventually (ev anyCall ∧ₗ link sendsProposedOverviewChange))

/-- Rule 803: notebook and claim edits finished before the finisher, which runs directly. AGENTS.md
allows an edit after the finisher when its checks are rerun ("an edit after it needs the finisher's
checks rerun"), which rule 804 details, so an edit after the finisher breaks this rule only when a
commit follows it with the finisher's checks not rerun since. -/
def r803 : Rule where
  number := 803
  keyword := .must
  domain := .mathematics
  formula := never (ev finishTurnViaLauncher) ∧ₗ
    (ev gitCommit ⟹ ¬ₗ since editAfterFinisher (atom rerunsFinisherChecks))

/-- Rule 804: an edit after the finisher followed by its checks rerun. -/
def r804 : Rule where
  number := 804
  keyword := .must
  domain := .mathematics
  formula := ev gitCommit ⟹ ¬ₗ since editAfterFinisher (atom rerunsFinisherChecks) ∧ₗ
    ¬ₗ since editAfterFinisher (ev notebookContextAll) ∧ₗ ¬ₗ since editAfterFinisher (ev claimCheck)

/-- Rule 805: the generated timing table at the entry's end. -/
def r805 : Rule where
  number := 805
  keyword := .must
  domain := .mathematics
  formula := ev entryAppend ∧ₗ atom isResearchEntry ⟹ atom endsWithTimingTable

/-- Rule 806: the entry committed with its fragment, archive and results. -/
def r806 : Rule where
  number := 806
  keyword := .must
  domain := .mathematics
  formula := ev gitCommit ∧ₗ atom commitsResearchEntry ⟹ atom commitHoldsEntryBundle

/-! Rules 807 to 821: commits, worktrees, merges, requests. -/

/-- Rule 807: every research turn ends in a commit of its records. -/
def r807 : Rule where
  number := 807
  keyword := .must
  domain := .softwareEngineering
  formula := ev cycleStart ∧ₗ atom startsResearchCycle ⟹ eventually (ev gitCommit ∧ₗ link commitsTurnRecords)

/-- Rule 808: no result left only in scratch. -/
def r808 : Rule where
  number := 808
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev entryAppend ∧ₗ atom citesScratchOnlyResult)

/-- Rule 809: scratch deleted by the cycle's end, after promotion. -/
def r809 : Rule where
  number := 809
  keyword := .must
  domain := .softwareEngineering
  formula := (ev finishTurn ⟹ ¬ₗ since (ev scratchWrite) (atom deletesScratch)) ∧ₗ
    never (atom deletesScratch ∧ₗ atom deletesUnpromotedResult)

/-- Rule 810: one persistent, tracked worktree, never the shared checkout. -/
def r810 : Rule where
  number := 810
  keyword := .must
  domain := .softwareEngineering
  formula := (ev worktreeAdd ⟹ ev worktreeAddTracked ∧ₗ ¬ₗ once (ev worktreeAdd)) ∧ₗ
    never (ev editing ∧ₗ atom inSharedCheckoutInBackground)

/-- Rule 811: `ff-base.sh` after every worktree commit, before the next commit. -/
def r811 : Rule where
  number := 811
  keyword := .must
  domain := .softwareEngineering
  formula := (ev gitCommit ∧ₗ atom inWorktree ⟹ eventually (ev ffBase)) ∧ₗ
    (ev gitCommit ⟹ ¬ₗ since (ev gitCommit ∧ₗ atom inWorktree) (ev ffBase))

/-- Rule 812: a conflict `ff-base.sh` reports, resolved. -/
def r812 : Rule where
  number := 812
  keyword := .must
  domain := .softwareEngineering
  formula := atom ffBaseReportsConflict ⟹ eventually (ev anyCall ∧ₗ link resolvesReportedConflict)

/-- Rule 813: a source's framework through `merge_main.py`, its changes read and key tests rerun
before the commit. -/
def r813 : Rule where
  number := 813
  keyword := .must
  domain := .softwareEngineering
  formula := (atom bringsSourceFramework ⟹ ev mergeMain) ∧ₗ
    (ev gitCommitNoEdit ⟹ ¬ₗ since (ev mergeMain) (ev anyCall ∧ₗ link readsSourceFrameworkDiff) ∧ₗ
      ¬ₗ since (ev mergeMain) (ev anyCall ∧ₗ link rerunsKeyFrameworkTests))

/-- Rule 814: a large framework change reviewed fresh before the merge's commit. -/
def r814 : Rule where
  number := 814
  keyword := .should
  domain := .softwareEngineering
  formula := ev gitCommitNoEdit ⟹
    ¬ₗ since (ev mergeMain ∧ₗ atom bringsLargeFrameworkChange) (ev agentRun) ∨ₗ atom justified

/-- Rule 815: a fast-forward to a pinned commit, the destination checked immediately before (by the
call right before it), refreshed if it advanced. -/
def r815 : Rule where
  number := 815
  keyword := .must
  domain := .softwareEngineering
  formula := ev fastForward ⟹ atom ffTargetPinned ∧ₗ
    since (ev anyCall ∧ₗ link checksDestinationHeadAndTree) (ev anyCall) ∧ₗ
    ¬ₗ since (ev anyResult ∧ₗ link showsDestinationAdvanced) (ev gitRebase)

/-- Rule 816: a moved branch rebased in a temporary worktree with a backup, each stop continued
with `notebook_rebase.py`. -/
def r816 : Rule where
  number := 816
  keyword := .must
  domain := .softwareEngineering
  formula := (ev gitRebase ∧ₗ atom rebasesOntoMovedRemote ⟹
      atom inTemporaryWorktree ∧ₗ once (ev gitBranch ∧ₗ link backsUpRebasedBranch)) ∧ₗ
    (atom continuesRebase ⟹ ev notebookRebaseContinue)

/-- Rule 817: a recurring conflict shape gets a tested resolver, never a scratch loop. -/
def r817 : Rule where
  number := 817
  keyword := .must
  domain := .softwareEngineering
  formula := never (atom resolvesConflictByScratchLoop)

/-- Rule 818: every request to the user filed, with its need, reason, attempts and default. -/
def r818 : Rule where
  number := 818
  keyword := .must
  domain := .softwareEngineering
  formula := (ev reply ∧ₗ atom asksUserSomething ⟹ once (ev userRequestFiled ∧ₗ link filesThisRequest)) ∧ₗ
    (ev userRequestFiled ⟹ atom requestHasNeedWhyTriedDefault)

/-- Rule 819: a new request mentioned in the report; an answered one marked fulfilled. -/
def r819 : Rule where
  number := 819
  keyword := .must
  domain := .softwareEngineering
  formula := (ev userRequestFiled ⟹ before (ev reply ∧ₗ link mentionsRequest) (ev user)) ∧ₗ
    (ev user ∧ₗ atom answersOpenRequest ⟹
      before (ev anyCall ∧ₗ link marksRequestFulfilled) (ev user))

/-- Rule 820: a task's progress reported against its artifact, without mathematical claims or a
review cadence. -/
def r820 : Rule where
  number := 820
  keyword := .must
  domain := .tasks
  formula := ev reply ∧ₗ atom reportsTaskProgress ⟹
    atom reportsAgainstArtifact ∧ₗ ¬ₗ atom declaresMathClaimsInReport

/-- Rule 821: after a restart notification, no tool run and at most one sentence; after the user's
message, active work continues unasked. -/
def r821 : Rule where
  number := 821
  keyword := .mustNot
  domain := .discipline
  formula := never (ev anyCall ∧ₗ since (ev user ∧ₗ atom isRestartNotification) (ev user)) ∧ₗ
    (ev reply ∧ₗ since (ev user ∧ₗ atom isRestartNotification) (ev user) ⟹ atom isAtMostOneSentence) ∧ₗ
    never (ev reply ∧ₗ atom asksToContinueActiveWork)

/-! Rules 822 to 840: mistakes, instruction files, tools, Claude Code. -/

/-- Rule 822: a shown mistake answered with Prevention and Meta, the Prevention's change made in
the turn. -/
def r822 : Rule where
  number := 822
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom answersShownMistake ⟹
    atom hasPreventionAndMeta ∧ₗ since (ev editing ∧ₗ link makesNamedPrevention) (ev user)

/-- Rule 823: repeated question marks answered by a committed fix. -/
def r823 : Rule where
  number := 823
  keyword := .must
  domain := .discipline
  formula := ev frustratedUser ⟹ eventually (ev gitCommit ∧ₗ link commitsFixForFrustration)

/-- Rule 824: a Meta paragraph for each mistake, reviewer report and right objection. -/
def r824 : Rule where
  number := 824
  keyword := .must
  domain := .discipline
  formula := ev entryAppend ∧ₗ atom admitsMistakeOrReviewer ⟹ atom hasMetaForEach

/-- Rule 825: AGENTS.md holds rules for every notebook only. -/
def r825 : Rule where
  number := 825
  keyword := .must
  domain := .discipline
  formula := never (ev agentsMdEdit ∧ₗ atom addsGoalSpecificRule)

/-- Rule 826: an instruction change removes as much as it adds, keeps every constraint, and is
reviewed fresh old against new. -/
def r826 : Rule where
  number := 826
  keyword := .must
  domain := .discipline
  formula := ev gitCommit ∧ₗ atom commitsInstructionChange ⟹ atom removesAsMuchAsAdds ∧ₗ
    atom keepsEveryConstraint ∧ₗ once (ev agentRun ∧ₗ link reviewsOldAgainstNew)

/-- Rule 827: each rule once, in its owner, none of the published skill's restated. -/
def r827 : Rule where
  number := 827
  keyword := .must
  domain := .discipline
  formula := never (ev instructionEdit ∧ₗ (atom restatesRuleElsewhere ∨ₗ atom restatesSkillRule))

/-- Rule 828: an added rule raises its file's cap with a raised entry. -/
def r828 : Rule where
  number := 828
  keyword := .must
  domain := .discipline
  formula := ev gitCommit ∧ₗ atom commitsAddedRule ⟹ since (ev budgetsEdit ∧ₗ link raisesCapForRule) (ev gitCommit)

/-- Rule 829: one call per job, wrong calls refused first, refusals saying what to do. -/
def r829 : Rule where
  number := 829
  keyword := .must
  domain := .discipline
  formula := ev toolEdit ⟹ atom keepsOneCallPerJob ∧ₗ atom refusesWrongCallFirst ∧ₗ atom refusalSaysWhatToDo

/-- Rule 830: committed tools extended, no scratch rebuilds; a script whose output is committed
becomes a tested tool first. -/
def r830 : Rule where
  number := 830
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev scratchWrite ∧ₗ atom rebuildsRecurringHelper) ∧ₗ
    (ev gitCommit ∧ₗ atom commitsScratchOutput ⟹ once (ev toolEdit ∧ₗ link turnsScriptIntoTool))

/-- Rule 831: a tool that falls short improved; a tool learnt from its interface. -/
def r831 : Rule where
  number := 831
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev toolRead ∧ₗ atom readsBodyToLearn) ∧ₗ
    (ev reply ∧ₗ atom saysToolFallsShort ⟹ eventually (ev toolEdit ∧ₗ link improvesThatTool))

/-- Rule 832: a replacement proposed only after the comparison, keeping ours offered. -/
def r832 : Rule where
  number := 832
  keyword := .must
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom proposesToolReplacement ⟹ atom listsWhatEachDoes ∧ₗ
    once (ev toolEdit ∧ₗ link buildsSmallestGapChange) ∧ₗ once (ev anyResult ∧ₗ link measuresBothTools) ∧ₗ
    atom offersKeepingOurs

/-- Rule 833: framework tests under `tools/tests/` or `tests/`. -/
def r833 : Rule where
  number := 833
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev testBesideCode)

/-- Rule 834: a suite over its limit is a defect, fixed. -/
def r834 : Rule where
  number := 834
  keyword := .must
  domain := .softwareEngineering
  formula := atom suiteRunOverLimit ⟹ eventually (ev editing ∧ₗ link fixesSuiteSlowness)

/-- Rule 835: collected data in a tracked, append-only, one-record-per-line file. -/
def r835 : Rule where
  number := 835
  keyword := .must
  domain := .softwareEngineering
  formula := never (atom storesCollectedDataElsewhere)

/-- Rule 836: files written with Write and Edit, never through the shell. -/
def r836 : Rule where
  number := 836
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev shellFileWrite ∨ₗ atom changesFileThroughShell)

/-- Rule 837: a file a command needs written with Write before it; a heredoc only as a program's
input in the last step. -/
def r837 : Rule where
  number := 837
  keyword := .must
  domain := .softwareEngineering
  formula := (atom readsPreparedFile ⟹ once (ev editing ∧ₗ link writesFileTheCallReads)) ∧ₗ
    never (ev heredocCall ∧ₗ atom heredocNotFinalInput)

/-- Rule 839: a wakeup is a fallback, re-armed at about 60 seconds. -/
def r839 : Rule where
  number := 839
  keyword := .must
  domain := .softwareEngineering
  formula := (ev scheduleWakeup ∧ₗ ¬ₗ atom waitsOnBlockedJob ⟹ atom delayAboutSixty) ∧ₗ
    never (ev scheduleWakeup ∧ₗ atom idlesUntilWakeup)

/-- Rule 840: long wakeup delays only for blocked waits. -/
def r840 : Rule where
  number := 840
  keyword := .should
  domain := .softwareEngineering
  formula := ev scheduleWakeup ∧ₗ atom delayIsLong ⟹ atom waitsOnBlockedJob ∨ₗ atom justified

def rules : List Rule :=
  [r701, r702, r703, r704, r705, r707, r708, r709, r710, r711, r712, r713, r714, r715, r716,
   r717, r718, r719, r720, r721, r722, r723, r724, r725, r726, r727, r728, r729, r730, r731, r732,
   r733, r734, r735, r736, r737, r738, r739, r740, r741, r742, r743, r744, r745, r746, r747, r748,
   r749, r750, r751, r752, r753, r754, r755, r756, r757, r758, r759, r760, r761, r762, r763, r764,
   r765, r766, r767, r768, r769, r770, r771, r772, r773, r774, r775, r776, r777, r778, r779, r780,
   r781, r782, r783, r784, r786, r787, r788, r789, r790, r791, r792, r793, r794, r795, r796, r797,
   r798, r799, r800, r801, r802, r803, r804, r805, r806, r807, r808, r809, r810, r811, r812, r813,
   r814, r815, r816, r817, r818, r819, r820, r821, r822, r823, r824, r825, r826, r827, r828, r829,
   r830, r831, r832, r833, r834, r835, r836, r837, r839, r840]

/-! The MAY rules. -/

/-- Rule 706 (MAY): feedback on the task's own work deferred the way a tangential bug is, written
up, committed, referenced from PLAN.md and followed by the task's work, keeps rule 705. -/
theorem r706_deferredFeedbackKeepsWriteUpRule :
    run r705 (seq [.reply "deferring this feedback to a write-up", edit "tasks/x/FEEDBACK_BUG.md",
      bash "git commit -m write-up", edit "tasks/x/PLAN.md", bash "lake build"])
      [(Examples.atom findsTangentialBug 0, true), (Examples.atom saysBugTrackedElsewhere 0, false),
       (Examples.link commitsBugDoc 1 2, true), (Examples.link referencesBugDoc 1 3, true),
       (Examples.atom worksOnTask 4, true)] = .kept := by decide

/-- Rule 785 (MAY): an entry continuing its item past the spell, with an extension recorded and
earned by progress, keeps rule 781. -/
theorem r785_earnedExtensionKeepsRotationRule :
    run r781 (seq [bash "python3 tools/notebook-append.py notebook.html e.html"])
      [(Examples.atom continuesItemPastSpell 0, true), (Examples.atom recordsSpellExtension 0, true),
       (Examples.atom extensionEarnedByProgress 0, true), (Examples.atom refilesRefusedWork 0, false)] =
      .kept := by decide

/-- The extension rule 785 permits is the only one: an extension progress didn't earn breaks
rule 781. -/
theorem r785_unearnedExtensionBreaksRotationRule :
    run r781 (seq [bash "python3 tools/notebook-append.py notebook.html e.html"])
      [(Examples.atom continuesItemPastSpell 0, true), (Examples.atom recordsSpellExtension 0, true),
       (Examples.atom extensionEarnedByProgress 0, false), (Examples.atom refilesRefusedWork 0, false)] =
      .broken := by decide

def permissions : List Nat := [706, 785]

end Rails.Ruleset.Range6
