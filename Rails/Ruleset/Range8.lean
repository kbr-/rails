import Rails.Rules
import Rails.Examples
import Rails.Witness

/-!
Rules 981 to 1120 of `tasks/agents-on-rails/RULES.md`: the engineering discipline's code, change,
verification, process, intake, design and git rules, and the design skills' rules (software design
philosophy, flexibility, type-driven design). Rule 1072 is a MAY rule, stated as a theorem.
-/

namespace Rails.Ruleset.Range8
open Rails Formula Ruleset Rules Examples

/-! Event predicates. -/

private def word (s : String) (ws : List (List Char)) : Bool := ws.contains s.toList

private def anyWordEnds (ss : List String) (ws : List (List Char)) : Bool :=
  ws.any fun w => ss.any fun s => endsWith s.toList w

/-- A test run, a type check, a build or a check by a reviewer: the commands may run under a
launcher such as `compute.sh`, so every word of a command is read, not only its program. -/
def runsCheck (e : Event) : Bool :=
  isTool "Agent" e || (programs e).any fun (_, ws) =>
    anyWordEnds ["pytest", "tests/run.py", "pytest_queue.py", "mypy", "pyright", "tsc"] ws ||
    (anyWordEnds ["lake"] ws && (word "build" ws || word "test" ws || word "env" ws)) ||
    (anyWordEnds ["cargo"] ws && (word "test" ws || word "check" ws)) ||
    (anyWordEnds ["npm"] ws && word "test" ws)

def runsTypeCheck (e : Event) : Bool :=
  (programs e).any fun (_, ws) =>
    anyWordEnds ["mypy", "pyright", "tsc"] ws || (anyWordEnds ["lake"] ws && word "build" ws) ||
    (anyWordEnds ["cargo"] ws && word "check" ws)

def isSearch (e : Event) : Bool :=
  isTool "Grep" e || isTool "Glob" e || runs "grep" (fun _ => true) e || runs "rg" (fun _ => true) e ||
    runs "git" (word "grep") e

def editsMigration (e : Event) : Bool :=
  match writePath e with
  | some p => occursIn "migration".toList p.toList
  | none => false

def toolCall : Pred := ⟨"toolCall", isCall, [bash "ls"]⟩
def commitCall : Pred := ⟨"commitCall", runs "git" (word "commit"), [bash "git commit -m x"]⟩
def fixupCall : Pred := ⟨"fixupCall",
  runs "git" (fun ws => word "commit" ws && ws.any (hasPrefix "--fixup".toList)),
  [bash "git commit --fixup abc1234"]⟩
def cachedStatCall : Pred := ⟨"cachedStatCall",
  runs "git" (fun ws => word "diff" ws && (word "--cached" ws || word "--staged" ws) && word "--stat" ws),
  [bash "git diff --cached --stat"]⟩
def hunkStaging : Pred := ⟨"hunkStaging",
  fun e => runs "git" (fun ws => word "add" ws && (word "-p" ws || word "--patch" ws)) e ||
    runs "stage_hunks.py" (fun _ => true) e,
  [bash "git add -p f.py", bash "python3 tools/stage_hunks.py f.py --skip 1"]⟩
def historyRewrite : Pred := ⟨"historyRewrite",
  runs "git" (fun ws => word "rebase" ws || word "filter-branch" ws || (word "commit" ws && word "--amend" ws)),
  [bash "git rebase --autosquash main", bash "git commit --amend --no-edit"]⟩
def branchReset : Pred := ⟨"branchReset", runs "git" (word "reset"), [bash "git reset --hard origin/main"]⟩
def checkRun : Pred := ⟨"checkRun", runsCheck,
  [bash "./compute.sh python3 tools/tests/run.py test_x", bash "lake build", reviewer]⟩
def typeCheckRun : Pred := ⟨"typeCheckRun", runsTypeCheck, [bash "mypy --strict src"]⟩
def searching : Pred := ⟨"searching", isSearch,
  [.call "g" "Grep" [("pattern", "x")], bash "rg -n foo", bash "git grep -n foo"]⟩
def webLookup : Pred := ⟨"webLookup", fun e => isTool "WebSearch" e || isTool "WebFetch" e,
  [.call "s" "WebSearch" [("query", "x")], .call "f" "WebFetch" [("url", "https://x.org")]]⟩
def agentRun : Pred := ⟨"agentRun", isTool "Agent", [.call "a" "Agent" [("prompt", "x")]]⟩
def migrationEdit : Pred := ⟨"migrationEdit", editsMigration, [edit "app/migrations/0002_add.py"]⟩
def chartRender : Pred := ⟨"chartRender", runs "helm" (word "template"), [bash "helm template r chart"]⟩
def hookRefusal : Pred := ⟨"hookRefusal", isRefusalEvent, [.refusal "hook" "no"]⟩

def preds : List Pred :=
  [toolCall, commitCall, fixupCall, cachedStatCall, hunkStaging, historyRewrite, branchReset,
   checkRun, typeCheckRun, searching, webLookup, agentRun, migrationEdit, chartRender, hookRefusal]

theorem preds_wellFormed : preds.all Pred.wellFormed = true := by decide

/-- The predicates refuse what they mustn't read: a commit's mention inside quotes, a read-only
diff, a plain add, a read of a migration. -/
theorem preds_refuse :
    [commitCall.test (bash "grep -n 'git commit' f"), fixupCall.test (bash "git commit -m x"),
      cachedStatCall.test (bash "git diff --stat"), hunkStaging.test (bash "git add f.py"),
      historyRewrite.test (bash "git log"), checkRun.test (bash "ls tests"),
      typeCheckRun.test (bash "lake env lean f.lean"), searching.test (bash "ls"),
      migrationEdit.test (read "app/migrations/0002_add.py"), chartRender.test (bash "helm upgrade r c")
      ].all (· == false) = true := by decide

/-- A launcher before a check doesn't hide it. -/
theorem check_under_launcher : runsCheck (bash "./compute.sh --threads 1 python3 -m pytest -q") = true := by
  decide

/-- Around `φ`: at some other position of the trace, before or after, with this one its anchor. -/
def around (φ : Formula) : Formula := once φ ∨ₗ eventually φ

/-! Atoms: questions about one event. -/

def leavesTypesLoose : Atom := ⟨"leavesTypesLoose",
  "Does this edit leave code untyped or loosely typed where its language, or an external checker, allows strict types, or depart from the repository's typing conventions?", .edit⟩
def commitsCheckableCode : Atom := ⟨"commitsCheckableCode",
  "Does this commit hold code a type checker (the language's own or an external one such as mypy) can check?", .call⟩
def mixesEffectsWithDecisions : Atom := ⟨"mixesEffectsWithDecisions",
  "Does this edit put a decision inside code performing effects (network, file, process, prompt, clock, randomness), or an effect inside the pure core, where a pure core and a thin outer layer holding no decision would do?", .edit⟩
def readsConfigFromEnvironment : Atom := ⟨"readsConfigFromEnvironment",
  "Does this edit read configuration from the environment where the code uses it, rather than take it as an explicit parameter?", .edit⟩
def passingConfigCostly : Atom := ⟨"passingConfigCostly",
  "Would passing the configuration this edit reads as an explicit parameter be very costly here?", .edit⟩
def commitsOuterLayer : Atom := ⟨"commitsOuterLayer",
  "Does this commit add or change the outer layer of effects around a pure core?", .call⟩
def writesInlineProgram : Atom := ⟨"writesInlineProgram",
  "Does this edit write into code meant to be committed a program run inline (python3 -c, a heredoc fed to an interpreter) rather than a module run by its path?", .edit⟩
def needlessNewStructure : Atom := ⟨"needlessNewStructure",
  "Does this edit add a new directory, file or duplicated block, or a mechanism more complex than needed, where a smaller change to the existing artifact would do and reuse fits?", .edit⟩
def buildsCostlyMechanism : Atom := ⟨"buildsCostlyMechanism",
  "Does this edit build a mechanism costlier than the cheapest one that would meet its goal?", .edit⟩
def unearnedGenerality : Atom := ⟨"unearnedGenerality",
  "Does this edit add an interface more general than its current uses need, its generality removing no existing special case?", .edit⟩
def asksHowTo : Atom := ⟨"asksHowTo",
  "Does this message from the user ask how to do something?", .user⟩
def givesProvisionalAnswer : Atom := ⟨"givesProvisionalAnswer",
  "Does this message from the user give a provisional answer to a decision that can't be settled yet?", .user⟩
def adoptsPerInstanceDesign : Atom := ⟨"adoptsPerInstanceDesign",
  "Does this event adopt or propose a design needing a new entry per instance or service for every future deployment?", .any⟩
def verificationOffChange : Atom := ⟨"verificationOffChange",
  "Does this verification call check something other than the behaviour the change touched and what depends on it?", .call⟩
def escalatedVerification : Atom := ⟨"escalatedVerification",
  "Is this verification costlier than the least costly evidence settling the change's failure modes (a mechanical update needing only ordinary verification)?", .call⟩
def unresolvedRiskOrFailure : Atom := ⟨"unresolvedRiskOrFailure",
  "At this point, is there an unresolved risk or a failed check calling for stronger verification?", .any⟩
def checklistToolsAsGoals : Atom := ⟨"checklistToolsAsGoals",
  "Does this event make the tools of a default checklist separate goals to run, rather than means chosen for the change?", .any⟩
def verifiesBeyondAffectedArea : Atom := ⟨"verifiesBeyondAffectedArea",
  "Does this call verify a narrow change beyond the area it affects?", .call⟩
def broadBlastRadius : Atom := ⟨"broadBlastRadius",
  "At this point, is the change's blast radius broader than it looks?", .any⟩
def canStillFindNew : Atom := ⟨"canStillFindNew",
  "Is this check a review that can still find something new?", .call⟩
def plansRepeatedCheck : Atom := ⟨"plansRepeatedCheck",
  "Does this edit write into a plan, as a criterion, the repeat of a check whose evidence is already in hand?", .edit⟩
def changesSharedResource : Atom := ⟨"changesSharedResource",
  "Does this call change a resource other consumers share?", .call⟩
def notesDivergentMechanisms : Atom := ⟨"notesDivergentMechanisms",
  "Does this reply discuss two components converging on different mechanisms for one concern?", .reply⟩
def pushesOneMechanism : Atom := ⟨"pushesOneMechanism",
  "Does this reply push for one mechanism for that concern?", .reply⟩
def changesSharedSetting : Atom := ⟨"changesSharedSetting",
  "Does this call change a shared setting's live value?", .call⟩
def changesManualOperation : Atom := ⟨"changesManualOperation",
  "Does this edit change what a person operates by hand (a key binding, a gesture, an interactive prompt)?", .edit⟩
def testWhereProofFits : Atom := ⟨"testWhereProofFits",
  "Does this edit, in a Lean project, add a test of a property a kernel-checked proof could establish?", .edit⟩
def provesTestedProperty : Atom := ⟨"provesTestedProperty",
  "Does this edit prove, over its full input domain under the applicable assumptions, the property an existing test checks?", .edit⟩
def removesTestBeyondProof : Atom := ⟨"removesTestBeyondProof",
  "Does this edit remove a test of behaviour outside every proof's scope (external effects, integrations, agreement between specification and user requirements)?", .edit⟩
def writesCaseTableTest : Atom := ⟨"writesCaseTableTest",
  "Does this edit write a test as a table of the code's own cases with their answers, rather than a relation over generated inputs?", .edit⟩
def callsCaseTablePropertyTest : Atom := ⟨"callsCaseTablePropertyTest",
  "Does this reply count a table of named cases with expected answers, randomly drawn, as a property test?", .reply⟩
def writesTestHack : Atom := ⟨"writesTestHack",
  "Does this edit add a hack to reach a hard-to-reach state for manual testing?", .edit⟩
def hackClearlyMarked : Atom := ⟨"hackClearlyMarked",
  "Is the hack this edit adds explicit and clearly marked as never to be committed?", .edit⟩
def commitsTestHack : Atom := ⟨"commitsTestHack",
  "Does this commit hold a hack added for manual testing?", .call⟩
def callsAutomationDone : Atom := ⟨"callsAutomationDone",
  "Does this reply call a piece of automation done?", .reply⟩
def leavesMechanicalWorkToCaller : Atom := ⟨"leavesMechanicalWorkToCaller",
  "Does this edit leave repeatable mechanical work to a tool's caller rather than in the tool?", .edit⟩
def buildsTool : Atom := ⟨"buildsTool", "Does this edit build or change a tool others call?", .edit⟩
def statesCallerBoundary : Atom := ⟨"statesCallerBoundary",
  "Does this edit state which semantic judgements and project-specific decisions the tool leaves its caller?", .edit⟩
def shallowModule : Atom := ⟨"shallowModule",
  "Does this edit make a module whose interface costs callers more knowledge than the functionality it hides (short methods preferred to depth)?", .edit⟩
def presentsWorkedResult : Atom := ⟨"presentsWorkedResult",
  "Does this message from the user present something the user has worked out?", .user⟩
def offersArtifact : Atom := ⟨"offersArtifact",
  "Does this reply offer an artifact of the agent's as finished?", .reply⟩
def floatsProposal : Atom := ⟨"floatsProposal",
  "Does this message from the user float a proposal for the agent's opinion?", .user⟩
def briefLacksGoal : Atom := ⟨"briefLacksGoal",
  "Does this delegation's brief lack the goal, the spec, the decisions made or the checks the result must pass?", .call⟩
def keepsStaleContent : Atom := ⟨"keepsStaleContent",
  "Does this edit leave in place stale or superseded content it touches (resolved tracking items, stale notes)?", .edit⟩
def closesTask : Atom := ⟨"closesTask", "Does this reply declare a task done or close it?", .reply⟩
def leavesFinishedBranches : Atom := ⟨"leavesFinishedBranches",
  "Does this reply leave the finished task's branches in place, neither pruned nor listed for deletion?", .reply⟩
def costlyMethod : Atom := ⟨"costlyMethod",
  "Does this call start a method with a significant cost in context, disk, downloads or repeated work?", .call⟩
def costBuysNothing : Atom := ⟨"costBuysNothing",
  "Does this call spend cost (context, disk, downloads, repeated work) that buys no correctness or rigor?", .call⟩
def heavyComputation : Atom := ⟨"heavyComputation",
  "Does this call start a heavy computation?", .call⟩
def runsCompiledParallel : Atom := ⟨"runsCompiledParallel",
  "Does this computation run compiled code in parallel?", .call⟩
def processChangeAddsFriction : Atom := ⟨"processChangeAddsFriction",
  "Does this edit change a process or framework (a check, a review step, a table) so it adds friction or time, or loses quality?", .edit⟩
def reportsProcessFriction : Atom := ⟨"reportsProcessFriction",
  "Does this reply report that a process or framework step adds friction or time?", .reply⟩
def reportsProcessChangeUse : Atom := ⟨"reportsProcessChangeUse",
  "Does this reply report a process change's first real use?", .reply⟩
def comparesTimeAndDefects : Atom := ⟨"comparesTimeAndDefects",
  "Does this reply judge the change by time to finish against the same work without it and by defects found per hour?", .reply⟩
def processTimeMultiplied : Atom := ⟨"processTimeMultiplied",
  "Did the process change this reply reports multiply the time the work took?", .reply⟩
def reportsFailedExperiment : Atom := ⟨"reportsFailedExperiment",
  "Does this reply report the process change as a failed experiment, with the numbers?", .reply⟩
def growsStepPerFix : Atom := ⟨"growsStepPerFix",
  "Does this edit grow a step with another fix, or make it more thorough after a miss, where the step's design is what fails?", .edit⟩
def reportsCycle : Atom := ⟨"reportsCycle", "Does this reply report a cycle of the task's work?", .reply⟩
def weighsHoursAndTokens : Atom := ⟨"weighsHoursAndTokens",
  "Does this reply weigh the hours and tokens spent against the task's size?", .reply⟩
def designDecidesBehaviour : Atom := ⟨"designDecidesBehaviour",
  "Does this reply say the design now decides the behaviour?", .reply⟩
def reopensDesign : Atom := ⟨"reopensDesign", "Does this edit reopen a design already decided?", .edit⟩
def contradictionOrUndecided : Atom := ⟨"contradictionOrUndecided",
  "Is the design this edit reopens reopened for an observed contradiction or an undecided behaviour that changes the artifact?", .edit⟩
def incompleteEnumeration : Atom := ⟨"incompleteEnumeration",
  "Does this edit build a procedure that must be complete without enumerating its input mechanically, checking each unit was handled, applying its rules per unit, recording only findings, or finding interactions through an index on shared keys?", .edit⟩
def recordGrowsMultiplicatively : Atom := ⟨"recordGrowsMultiplicatively",
  "Does this edit design a record growing with units times rules, or rounds times everything?", .edit⟩
def addsRuleListOrField : Atom := ⟨"addsRuleListOrField",
  "Does this edit add a rule, a list or a required field to a record?", .edit⟩
def notesRepeatedBreach : Atom := ⟨"notesRepeatedBreach",
  "Does this reply note that an agent keeps breaking a rule?", .reply⟩
def checksJudgementCall : Atom := ⟨"checksJudgementCall",
  "Does this edit make a mechanical check decide a judgement call?", .edit⟩
def reportsStatus : Atom := ⟨"reportsStatus", "Does this reply report status?", .reply⟩
def statusAgainstGoal : Atom := ⟨"statusAgainstGoal",
  "Does this reply report status against the goal and the open items?", .reply⟩
def idlesWhileWorkRemains : Atom := ⟨"idlesWhileWorkRemains",
  "Does this reply end the turn or wait while unblocked work remains, or while a run goes on without its finished results read and the next piece started?", .reply⟩
def treatsReportAsEnd : Atom := ⟨"treatsReportAsEnd",
  "Does this reply treat a status report, or handing a task to another agent, as ending the work?", .reply⟩
def blamesFullMachine : Atom := ⟨"blamesFullMachine",
  "Does this reply treat a full machine as limiting the agent's own code, reading or analysis?", .reply⟩
def slowPolling : Atom := ⟨"slowPolling",
  "Does this call poll at a long interval or without exiting as soon as its condition holds, set a long timeout, or run serially checks that could run in parallel?", .call⟩
def startsBatch : Atom := ⟨"startsBatch", "Does this call start a batch of a long procedure?", .call⟩
def projectionExceedsAcceptable : Atom := ⟨"projectionExceedsAcceptable",
  "At this batch, does the projection of the procedure's rest exceed what the user would plausibly accept?", .call⟩
def thirdRoundSameClass : Atom := ⟨"thirdRoundSameClass",
  "Does this reply report a loop's third or later round finding the same defect class in one mechanism?", .reply⟩
def bringsCountsAndDesign : Atom := ⟨"bringsCountsAndDesign",
  "Does this reply bring the per-round counts and recommend a design removing the class, with its measured limits?", .reply⟩
def ordersWithoutDependency : Atom := ⟨"ordersWithoutDependency",
  "Does this reply impose an order on steps without naming the output the later step consumes?", .reply⟩
def serializesIndependentWork : Atom := ⟨"serializesIndependentWork",
  "Does this call run alone work independent of other pending work that could run together with it within the resource budget?", .call⟩
def declaresTaskBlocked : Atom := ⟨"declaresTaskBlocked", "Does this reply declare a task blocked?", .reply⟩
def blocksIndependentOnGate : Atom := ⟨"blocksIndependentOnGate",
  "Does this reply hold back work that doesn't depend on a failed test, approval or commit gate?", .reply⟩
def reviewerSeesBeyondInput : Atom := ⟨"reviewerSeesBeyondInput",
  "Does this reviewer run have access to inputs beyond those its review should see?", .call⟩
def writesDesign : Atom := ⟨"writesDesign", "Does this edit write or change a design or plan for the task?", .edit⟩
def assignsTask : Atom := ⟨"assignsTask", "Does this message from the user assign a task?", .user⟩
def needsProductionVerification : Atom := ⟨"needsProductionVerification",
  "Does the task this message assigns need anything verified against production?", .user⟩
def implementsChange : Atom := ⟨"implementsChange",
  "Does this edit implement the task's change (code or configuration in the target)?", .edit⟩
def choosesTool : Atom := ⟨"choosesTool", "Does this reply choose a tool for the task's build or tests?", .reply⟩
def namesEnvVariable : Atom := ⟨"namesEnvVariable",
  "Does this edit name an environment variable the code reads?", .edit⟩
def judgesToolExistence : Atom := ⟨"judgesToolExistence",
  "Does this reply say whether a tool for a job exists?", .reply⟩
def addsField : Atom := ⟨"addsField", "Does this edit add a field to a record, schema or metadata?", .edit⟩
def citesConvention : Atom := ⟨"citesConvention",
  "Does this reply cite a file as the convention to follow?", .reply⟩
def fixesDesignChoice : Atom := ⟨"fixesDesignChoice",
  "Does this edit fix a choice of a search space or design (a budget split, a value)?", .edit⟩
def namesDecider : Atom := ⟨"namesDecider",
  "Does this edit name who decides that choice: evidence, the user or the search?", .edit⟩
def offersUserMechanism : Atom := ⟨"offersUserMechanism",
  "Does this reply offer a design for a mechanism the user proposed?", .reply⟩
def checksPartsAgainstPurpose : Atom := ⟨"checksPartsAgainstPurpose",
  "Does this reply check each part of the design against the purpose the user stated for the mechanism?", .reply⟩
def recommends : Atom := ⟨"recommends", "Does this reply make a recommendation?", .reply⟩
def recommendationAnswersCause : Atom := ⟨"recommendationAnswersCause",
  "Does this reply's recommendation remove the cause its diagnosis named?", .reply⟩
def syncMissesOperation : Atom := ⟨"syncMissesOperation",
  "Does this edit design a sync missing create, update or delete in either direction?", .edit⟩
def ignoresReplicasOrWriters : Atom := ⟨"ignoresReplicasOrWriters",
  "Does this edit design without regard to the deployment's replica counts or every concurrent writer?", .edit⟩
def decisionInputsUnlisted : Atom := ⟨"decisionInputsUnlisted",
  "Does this edit write a decision function without listing its unknown or malformed inputs?", .edit⟩
def unmappedMechanism : Atom := ⟨"unmappedMechanism",
  "Does this edit leave a mechanism a decision names neither mapped to a step nor marked out of scope?", .edit⟩
def incrementHoldsSeveralArtifacts : Atom := ⟨"incrementHoldsSeveralArtifacts",
  "Does this edit define an implementation increment that delivers several artifacts, or one not independently verifiable or without its acceptance evidence?", .edit⟩
def splitDropsObligations : Atom := ⟨"splitDropsObligations",
  "Does this edit split a workstream while dropping unfinished integration or acceptance obligations?", .edit⟩
def reportsIncrements : Atom := ⟨"reportsIncrements",
  "Does this reply report completed implementation increments?", .reply⟩
def fromArtifactList : Atom := ⟨"fromArtifactList",
  "Does this reply report the increments from the split's artifact list?", .reply⟩
def redesigns : Atom := ⟨"redesigns", "Does this edit redesign the task's change?", .edit⟩
def proposesDesignOnLibrary : Atom := ⟨"proposesDesignOnLibrary",
  "Does this reply propose a design relying on a library's semantics (time zones and DST, connection pools, transactions)?", .reply⟩
def designsAroundToolLimit : Atom := ⟨"designsAroundToolLimit",
  "Does this reply design around a tool's limit?", .reply⟩
def toolReportsUnverifiedOutcome : Atom := ⟨"toolReportsUnverifiedOutcome",
  "Does this edit make a tool report an outcome it didn't read back from where that state lives?", .edit⟩
def confirmsToolByHand : Atom := ⟨"confirmsToolByHand",
  "Does this call confirm by hand the outcome of a tool just run?", .call⟩
def proposesPerTurnMechanism : Atom := ⟨"proposesPerTurnMechanism",
  "Does this reply propose something that runs on every turn or request (a hook, a per-commit check, a call in a loop)?", .reply⟩
def statesLatency : Atom := ⟨"statesLatency", "Does this reply state the proposal's measured latency?", .reply⟩
def addsOption : Atom := ⟨"addsOption", "Does this edit add an option to a tool or interface?", .edit⟩
def everyCallerWantsIt : Atom := ⟨"everyCallerWantsIt",
  "Does every caller want the behaviour this edit's new option gives?", .edit⟩
def stopsRepeatingAsyncTask : Atom := ⟨"stopsRepeatingAsyncTask",
  "Does this edit write code stopping a repeating async task (polling, a debounced search, a cancelled fetch)?", .edit⟩
def dropsInFlightResults : Atom := ⟨"dropsInFlightResults",
  "Does that code drop the results of calls still in flight at the stop?", .edit⟩
def buildsModelJudge : Atom := ⟨"buildsModelJudge", "Does this edit build or change a model judge?", .edit⟩
def judgeIsHybrid : Atom := ⟨"judgeIsHybrid",
  "Does the judge get the facts a tool can know before its call, and is its verdict checked against its input after?", .edit⟩
def judgeErrsTowardRefusing : Atom := ⟨"judgeErrsTowardRefusing",
  "Does this edit make a refusing judge err toward refusing rather than passing?", .edit⟩
def dropsRefusingInputs : Atom := ⟨"dropsRefusingInputs",
  "Does this edit let a judge's refusing verdicts go without keeping their inputs?", .edit⟩
def changesJudge : Atom := ⟨"changesJudge", "Does this edit change a judge's prompt or decision?", .edit⟩
def commitsBeforeItsLayer : Atom := ⟨"commitsBeforeItsLayer",
  "Does this commit add code depending on a layer no earlier commit added?", .call⟩
def waitsOnGateForIndependentWork : Atom := ⟨"waitsOnGateForIndependentWork",
  "Does this reply let a pending verification or gate hold back work independent of it?", .reply⟩
def landsArtifact : Atom := ⟨"landsArtifact", "Does this call land an artifact (merge, fast-forward, final commit)?", .call⟩
def carriesUnusedCode : Atom := ⟨"carriesUnusedCode",
  "Does this commit carry code over from an old branch that its own code and tests don't call?", .call⟩
def fileServesSeveralCommits : Atom := ⟨"fileServesSeveralCommits",
  "Does this commit take part of a file whose changes serve more than one commit?", .call⟩
def commitsUnusedSymbol : Atom := ⟨"commitsUnusedSymbol",
  "Does this commit add a symbol with no user in the same commit?", .call⟩
def fixupMisaimed : Atom := ⟨"fixupMisaimed",
  "Is this fixup aimed at a commit other than the one whose change it belongs to?", .call⟩
def changesEarlierCommitsCode : Atom := ⟨"changesEarlierCommitsCode",
  "Does this edit change code an earlier commit of the branch added?", .edit⟩
def foldsEarlierFixIntoStep : Atom := ⟨"foldsEarlierFixIntoStep",
  "Does this commit mix a change to an earlier commit's code into the current step's files?", .call⟩
def realignsWithFixupPairsAtTip : Atom := ⟨"realignsWithFixupPairsAtTip",
  "Does this call realign committed changes by writing fixup pairs at the tip, rather than splitting each overfull commit in place and folding the leftovers in a second rebase?", .call⟩
def changesDecision : Atom := ⟨"changesDecision", "Does this edit change a decision?", .edit⟩
def changesCode : Atom := ⟨"changesCode", "Does this edit change code?", .edit⟩
def testsShapedByExisting : Atom := ⟨"testsShapedByExisting",
  "Does this edit design tests after the repository's existing tests rather than from what the checking rules require?", .edit⟩
def writesCheckWithoutAnswerKey : Atom := ⟨"writesCheckWithoutAnswerKey",
  "Does this edit write a check of code with no answer key?", .edit⟩
def checksByRelations : Atom := ⟨"checksByRelations",
  "Does that check use relations (independent views agree, an inverse returns the start, a repeat changes nothing, a simpler model agrees) on inputs generated from their definition?", .edit⟩
def standInRefusal : Atom := ⟨"standInRefusal",
  "Was this refusal caused by a check keyed on a stand-in for its property (a reader reused from another tool for another purpose included)?", .refusal⟩
def assertsUnworkedTime : Atom := ⟨"assertsUnworkedTime",
  "Does this reply assert a time, weekday or cursor expectation not worked out by hand?", .reply⟩
def worstCaseMissesSteps : Atom := ⟨"worstCaseMissesSteps",
  "Does this reply give a worst case leaving out a step still blocking after a deadline's last check?", .reply⟩
def testsScheduledCodeDirectly : Atom := ⟨"testsScheduledCodeDirectly",
  "Does this edit test scheduled or framework-invoked code other than through the real scheduler or framework entry point?", .edit⟩
def rerunsHungRun : Atom := ⟨"rerunsHungRun", "Does this call rerun a run that hung?", .call⟩
def buildsCheckForUncaughtMistake : Atom := ⟨"buildsCheckForUncaughtMistake",
  "Does this edit build a custom check for a mistake class nothing existing catches?", .edit⟩
def settlesCheckableQuestion : Atom := ⟨"settlesCheckableQuestion",
  "Does this reply settle a question a check of a few minutes would answer?", .reply⟩
def wrongToolForJob : Atom := ⟨"wrongToolForJob",
  "Does this call do its job with a general tool where one made for the job and its input's form exists?", .call⟩
def resetRemovesMigrations : Atom := ⟨"resetRemovesMigrations",
  "Does this branch reset remove migrations?", .call⟩
def editsChartValue : Atom := ⟨"editsChartValue", "Does this edit change a deployment chart's value?", .edit⟩
def apiRecipeSucceeds : Atom := ⟨"apiRecipeSucceeds",
  "Is this result the first success of an external-API recipe (URL, identity, parameters)?", .result⟩
def listsLeftoverBranches : Atom := ⟨"listsLeftoverBranches",
  "Does this reply list leftover branches and worktrees for deletion?", .reply⟩
def analysesDesign : Atom := ⟨"analysesDesign",
  "Does this reply analyse a software design (its complexity, boundaries or modules)?", .reply⟩
def startsFromCallerJourney : Atom := ⟨"startsFromCallerJourney",
  "Does the analysis start from a concrete change or caller journey and locate its friction?", .reply⟩
def tracesSymptomDependency : Atom := ⟨"tracesSymptomDependency",
  "Does the analysis trace the dependency behind each symptom and say which remaining relationships types or explicit contracts could hold?", .reply⟩
def namesOwnedKnowledge : Atom := ⟨"namesOwnedKnowledge",
  "Does the analysis name the knowledge each module owns and where callers, intermediate data and tests duplicate it?", .reply⟩
def findsKnowledgeLeak : Atom := ⟨"findsKnowledgeLeak",
  "Does this reply find knowledge leaking across a module boundary?", .reply⟩
def comparesLeakOptions : Atom := ⟨"comparesLeakOptions",
  "Does this reply compare, for each leak, keeping the boundary, moving ownership to an existing module and extracting a shared owner?", .reply⟩
def proposesRemovingLayer : Atom := ⟨"proposesRemovingLayer",
  "Does this reply propose removing a forwarding layer?", .reply⟩
def namesLayerContribution : Atom := ⟨"namesLayerContribution",
  "Does this reply identify what the layer contributes (routing, adaptation, access control, a framework need, a domain name)?", .reply⟩
def hidesPublicSemantics : Atom := ⟨"hidesPublicSemantics",
  "Does this edit hide from a contract a necessary public semantic (whether an external effect may repeat, a durability guarantee)?", .edit⟩
def interfaceHardToExplain : Atom := ⟨"interfaceHardToExplain",
  "Does this reply show difficulty explaining an interface (a parameter's meaning, units, ownership, empty results, failures, lifecycle)?", .reply⟩
def keepsSpecialization : Atom := ⟨"keepsSpecialization", "Does this reply keep a specialization?", .reply⟩
def statesCallerBenefit : Atom := ⟨"statesCallerBenefit",
  "Does this reply state the specialization's benefit for the actual caller?", .reply⟩
def needlessOption : Atom := ⟨"needlessOption",
  "Does this edit expose an option whose value doesn't vary between callers or deployments and whose wrong default would cause no harm?", .edit⟩
def policyAsInternalDefault : Atom := ⟨"policyAsInternalDefault",
  "Does this edit treat authorization, business policy or externally observable failure behaviour as an internal default rather than a contract choice?", .edit⟩
def reportsDesignFinding : Atom := ⟨"reportsDesignFinding", "Does this reply report a design finding?", .reply⟩
def findingNamesAll : Atom := ⟨"findingNamesAll",
  "Does the finding name the symptom, the leaking decision, its proposed owner and the consequence for callers?", .reply⟩
def combinationLosesContract : Atom := ⟨"combinationLosesContract",
  "Does this edit combine interchangeable parts so the combination isn't usable wherever a primitive is, losing shape, constraints, identity, failure behaviour or evaluation semantics?", .edit⟩
def buildsCombination : Atom := ⟨"buildsCombination",
  "Does this edit build a combination of interchangeable parts?", .edit⟩
def lawBreakingSubstitution : Atom := ⟨"lawBreakingSubstitution",
  "Does this edit parameterize an algorithm without the operations and laws it needs, or substitute a representation breaking those laws?", .edit⟩
def buildsExtensibleOperation : Atom := ⟨"buildsExtensibleOperation",
  "Does this edit build an extensible operation that new cases join?", .edit⟩
def definesDispatchRules : Atom := ⟨"definesDispatchRules",
  "Does the operation define applicability, overlap resolution, fallback and the scope of registrations?", .edit⟩
def addsHandler : Atom := ⟨"addsHandler", "Does this edit add a handler to an extensible operation?", .edit⟩
def fusesSelectionAndRun : Atom := ⟨"fusesSelectionAndRun",
  "Does this edit fuse selecting a handler with running it?", .edit⟩
def fusesReusedStages : Atom := ⟨"fusesReusedStages",
  "Does this edit fuse the description, preparation and execution of a reused description, or prepare what depends on current inputs?", .edit⟩
def defersComputation : Atom := ⟨"defersComputation", "Does this edit defer a computation?", .edit⟩
def definesDeferralSemantics : Atom := ⟨"definesDeferralSemantics",
  "Does the edit define when the deferred computation runs, what environment it observes, whether it may rerun and when its state is released?", .edit⟩
def reusesGeneratedIdentity : Atom := ⟨"reusesGeneratedIdentity",
  "Does this edit let generated identities or bindings go stale across nested or repeated deferred computations?", .edit⟩
def addsAnnotation : Atom := ⟨"addsAnnotation",
  "Does this edit add an annotation layer accompanying values?", .edit⟩
def definesAnnotationRules : Atom := ⟨"definesAnnotationRules",
  "Does the annotation get its own combination rules and a defined meaning for missing metadata?", .edit⟩
def recordsProvenance : Atom := ⟨"recordsProvenance", "Does this edit record provenance?", .edit⟩
def statesProvenanceScope : Atom := ⟨"statesProvenanceScope",
  "Does the edit choose whether provenance records inputs, sufficient premises or a full derivation, and state what the summary omits?", .edit⟩
def implementsPropagation : Atom := ⟨"implementsPropagation",
  "Does this edit implement propagation of partial information between sources?", .edit⟩
def statesMergeLawsAndTermination : Atom := ⟨"statesMergeLawsAndTermination",
  "Does the propagation have merge laws for order independence and repeated delivery, and say how cyclic computation terminates or reports incomplete work?", .edit⟩
def mixesAssertionsAndDerived : Atom := ⟨"mixesAssertionsAndDerived",
  "Does this edit mix source assertions and their assumptions with derived consequences, or let a retraction drop independently supported conclusions or keep dependent ones?", .edit⟩
def fusesSearchParts : Atom := ⟨"fusesSearchParts",
  "Does this edit fix what makes a candidate usable inside the producer, or fuse candidate generation, acceptance and scheduling?", .edit⟩
def reexploresFailedCombinations : Atom := ⟨"reexploresFailedCombinations",
  "Does this edit drop the incompatible assumption combinations of failed candidates, so the search explores them again?", .edit⟩
def conflatesExhaustionAndLimit : Atom := ⟨"conflatesExhaustionAndLimit",
  "Does this edit report search exhaustion and a resource limit alike?", .edit⟩
def votesWithoutReconciliation : Atom := ⟨"votesWithoutReconciliation",
  "Does this edit reconcile several methods by voting alone, with no acceptance or reconciliation rule?", .edit⟩
def mismatchedStateShape : Atom := ⟨"mismatchedStateShape",
  "Does this edit model exclusive alternatives as other than a sum, coexisting facts as other than a product, or use an optional value where absence means nothing?", .edit⟩
def excludesInvalidStates : Atom := ⟨"excludesInvalidStates",
  "Does this edit show that a representation excludes invalid combinations?", .edit⟩
def showsValidConstructible : Atom := ⟨"showsValidConstructible",
  "Does this edit also show that the needed valid states remain constructible?", .edit⟩
def mapsByCardinality : Atom := ⟨"mapsByCardinality",
  "Does this edit change a representation relying on equal cardinality rather than an explicit mapping?", .edit⟩
def ignoresPartiality : Atom := ⟨"ignoresPartiality",
  "Does this reply apply a types-as-propositions or parametricity argument in a partial language without accounting for failure and nontermination?", .reply⟩
def conflatesSharedRepresentation : Atom := ⟨"conflatesSharedRepresentation",
  "Does this edit leave identifiers, units or states sharing a raw representation undistinguished where they permit different operations?", .edit⟩
def constructorLeavesInvariant : Atom := ⟨"constructorLeavesInvariant",
  "Does this edit add a constructor that doesn't establish the relationship its consumers rely on?", .edit⟩
def splitsTagFromPayload : Atom := ⟨"splitsTagFromPayload",
  "Does this edit keep a runtime tag apart from its dependent payload?", .edit⟩
def actsOnStaleObservation : Atom := ⟨"actsOnStaleObservation",
  "Does this edit act on changing external state relying on an invariant about a past observation without revalidating it?", .edit⟩

/-! Links: questions about an event and its anchor. -/

def strictestOwnChecker : Link := ⟨"strictestOwnChecker",
  "Does this type-check run check the anchored commit's code at its strictest setting, with the repository's own checker?"⟩
def testsOuterLayerLive : Link := ⟨"testsOuterLayerLive",
  "Does this edit write integration tests of the anchored commit's outer layer against the real system?"⟩
def namesCheapestMechanism : Link := ⟨"namesCheapestMechanism",
  "Does this reply name the cheapest mechanism meeting the anchored edit's goal and say why it fails, weighing each by its cost to whoever runs it and how often?"⟩
def givesRunnableCommand : Link := ⟨"givesRunnableCommand",
  "Does this reply give the literal, runnable command for what the anchored message asks how to do?"⟩
def actsOnProvisionalAnswer : Link := ⟨"actsOnProvisionalAnswer",
  "Does this call proceed on the provisional answer the anchored message gives?"⟩
def closesProvisionalQuestion : Link := ⟨"closesProvisionalQuestion",
  "Does this reply treat as settled the question the anchored message answered provisionally?"⟩
def testsRewrittenTip : Link := ⟨"testsRewrittenTip",
  "Does this check test the tip of the branch the anchored rewrite produced?"⟩
def settlesSameQuestion : Link := ⟨"settlesSameQuestion",
  "Does this earlier check settle the same question, on the same code, as the anchored one?"⟩
def checksResourceConsumers : Link := ⟨"checksResourceConsumers",
  "Does this call check the other consumers of the resource the anchored call changes?"⟩
def keepsLiveValue : Link := ⟨"keepsLiveValue",
  "Does this call keep the live value of the setting the anchored call changes, so an undo can restore it?"⟩
def statesWholeBehaviour : Link := ⟨"statesWholeBehaviour",
  "Does this reply state the whole expected behaviour of what the anchored edit changes and compare the options by it?"⟩
def listsExistingBehaviour : Link := ⟨"listsExistingBehaviour",
  "Does this reply list what the existing behaviour the anchored edit changes already does?"⟩
def measuresManualChange : Link := ⟨"measuresManualChange",
  "Does this check measure the anchored change in the test (how far, how often, at what cost), beyond that it did something?"⟩
def removesSupersededTest : Link := ⟨"removesSupersededTest",
  "Does this edit remove the test whose property the anchored edit proves?"⟩
def revertsHack : Link := ⟨"revertsHack", "Does this edit revert the hack the anchored edit added?"⟩
def walksCallerWorkflow : Link := ⟨"walksCallerWorkflow",
  "Does this reply walk the caller's remaining setup, execution, retries and interpretation for the automation the anchored reply calls done?"⟩
def checksUsersResult : Link := ⟨"checksUsersResult",
  "Does this call check what the anchored message from the user worked out?"⟩
def rederivesUsersResult : Link := ⟨"rederivesUsersResult",
  "Does this reply re-derive what the anchored message from the user worked out?"⟩
def freshReviewOfArtifact : Link := ⟨"freshReviewOfArtifact",
  "Is this a fresh-context reviewer given only the artifact the anchored reply offers?"⟩
def judgesProposalIndependently : Link := ⟨"judgesProposalIndependently",
  "Does this reply give independent judgement of the proposal the anchored message floats?"⟩
def weighsMethodCost : Link := ⟨"weighsMethodCost",
  "Does this reply weigh the anchored method's cost beside its correctness?"⟩
def estimatesRunTime : Link := ⟨"estimatesRunTime",
  "Does this reply estimate the anchored computation's time?"⟩
def changesFrictionalProcess : Link := ⟨"changesFrictionalProcess",
  "Does this edit change the process the anchored reply reports as adding friction?"⟩
def buildsNextArtifact : Link := ⟨"buildsNextArtifact",
  "Does this edit build the next small artifact of the design the anchored reply says is decided?"⟩
def asksRecordGrowth : Link := ⟨"asksRecordGrowth",
  "Does this reply ask what the record the anchored edit extends grows with?"⟩
def addsMinimalCheck : Link := ⟨"addsMinimalCheck",
  "Does this edit add a minimal check (a hook, a warning before rejection, unskippable output) of the rule the anchored reply says keeps being broken, whose firing leads to a useful response?"⟩
def projectsFromRate : Link := ⟨"projectsFromRate",
  "Does this reply project the rest of the procedure from the measured rate, before the anchored batch?"⟩
def reassessesBuildable : Link := ⟨"reassessesBuildable",
  "Does this reply reassess what can still be built before the anchored reply declares the task blocked?"⟩
def readsTrackerIssue : Link := ⟨"readsTrackerIssue",
  "Does this call read the tracker issue of the task the anchored edit designs for?"⟩
def readsIssueLinks : Link := ⟨"readsIssueLinks",
  "Does this call read what that tracker issue links?"⟩
def confirmsAccess : Link := ⟨"confirmsAccess",
  "Does this call confirm access to the data sources and write scope the anchored task needs?"⟩
def asksProductionCredentials : Link := ⟨"asksProductionCredentials",
  "Does this reply ask for a service account or credentials to verify the anchored task against production?"⟩
def settlesSourceOfTruth : Link := ⟨"settlesSourceOfTruth",
  "Does this reply settle the source of truth and ownership of the anchored change with the stakeholders?"⟩
def readsBuildConfig : Link := ⟨"readsBuildConfig",
  "Does this read open how CI and the Makefile install and test, the lockfile or packageManager, for the anchored choice of tool?"⟩
def readsSettingsLoader : Link := ⟨"readsSettingsLoader",
  "Does this read open the settings loader reading the variable the anchored edit names?"⟩
def searchesForTool : Link := ⟨"searchesForTool",
  "Does this lookup search the package index, tool documentation or the web for a tool doing the anchored reply's job?"⟩
def searchesExistingFields : Link := ⟨"searchesExistingFields",
  "Does this search look for existing fields (JSON metadata included) serving the field the anchored edit adds?"⟩
def confirmsLiveRoute : Link := ⟨"confirmsLiveRoute",
  "Does this call confirm a live route reaches the file the anchored reply cites as the convention?"⟩
def rechecksTicketRequirements : Link := ⟨"rechecksTicketRequirements",
  "Does this reply recheck every requirement in the ticket against the anchored redesign?"⟩
def checksLibrarySemantics : Link := ⟨"checksLibrarySemantics",
  "Does this call check the library semantics the anchored reply's design relies on?"⟩
def checksToolPrimitives : Link := ⟨"checksToolPrimitives",
  "Does this call check whether the tool, its primitives included, already does the job the anchored reply designs around its limit?"⟩
def sameHandConfirmation : Link := ⟨"sameHandConfirmation",
  "Does this call confirm by hand the same tool's outcome as the anchored call?"⟩
def movesConfirmationIntoTool : Link := ⟨"movesConfirmationIntoTool",
  "Does this edit move the confirmation the anchored call does by hand into the tool?"⟩
def timesOnRealInput : Link := ⟨"timesOnRealInput",
  "Does this call time the anchored reply's proposal on a real input?"⟩
def asksCallersWant : Link := ⟨"asksCallersWant",
  "Does this reply ask whether every caller wants the behaviour of the option the anchored edit adds?"⟩
def testsResolveAfterStop : Link := ⟨"testsResolveAfterStop",
  "Does this edit test the anchored stop by resolving an in-flight call after it?"⟩
def replaysKeptInputs : Link := ⟨"replaysKeptInputs",
  "Does this check replay the judge's kept inputs, showing the anchored change turns the wrong verdicts and keeps the right ones?"⟩
def verifiesLandedArtifact : Link := ⟨"verifiesLandedArtifact",
  "Does this check verify the artifact the anchored call lands?"⟩
def checksSymbolUse : Link := ⟨"checksSymbolUse",
  "Does this call check that every symbol the anchored commit adds has a user in it?"⟩
def fixupOfThatChange : Link := ⟨"fixupOfThatChange",
  "Is this fixup commit the anchored edit's change, aimed at the earlier commit it changes?"⟩
def searchesDependentText : Link := ⟨"searchesDependentText",
  "Does this search look through the branch's docs, runbooks, comments, commit messages and plan for text depending on the anchored edit's decision?"⟩
def searchesQuotedLines : Link := ⟨"searchesQuotedLines",
  "Does this search look for the anchored edit's changed lines in the evidence quoting code (mutation specs, ledgers, saved replays) and the prose?"⟩
def treatsAsStandInSign : Link := ⟨"treatsAsStandInSign",
  "Does this reply take the anchored refusal as the sign that its check is keyed on a stand-in?"⟩
def inspectsHungRun : Link := ⟨"inspectsHungRun",
  "Does this call read where the run the anchored call reruns stood (its thread stacks, its log)?"⟩
def considersStandardToolConvention : Link := ⟨"considersStandardToolConvention",
  "Does this reply look for a convention letting a standard tool see the class the anchored edit's check is for?"⟩
def runsSettlingCheck : Link := ⟨"runsSettlingCheck",
  "Does this call run the check answering the question the anchored reply settles?"⟩
def resetsLocalDatabase : Link := ⟨"resetsLocalDatabase",
  "Does this call reset the local database after the anchored reset removed migrations?"⟩
def searchesHeadPins : Link := ⟨"searchesHeadPins",
  "Does this search look for tests pinning the migration head the anchored edit moves?"⟩
def tracesChartValue : Link := ⟨"tracesChartValue",
  "Does this call trace the chart value the anchored edit changes to its template and to the name the code reads?"⟩
def recordsApiRecipe : Link := ⟨"recordsApiRecipe",
  "Does this edit record in the plan the API recipe the anchored result shows working?"⟩
def checksRecordsAgainstFinal : Link := ⟨"checksRecordsAgainstFinal",
  "Does this call check the plan's and records' counts and status against the final state of the task the anchored reply closes?"⟩
def simplifiesAbstraction : Link := ⟨"simplifiesAbstraction",
  "Does this edit simplify the abstraction the anchored reply had difficulty explaining?"⟩
def checksNestedCombination : Link := ⟨"checksNestedCombination",
  "Does this check try nested combinations of the anchored edit's parts for lost information?"⟩
def checksHandlerInteractions : Link := ⟨"checksHandlerInteractions",
  "Does this check try old inputs, mixed old and new inputs and competing handlers for the handler the anchored edit adds?"⟩
def definesKnowledgeStates : Link := ⟨"definesKnowledgeStates",
  "Does this edit distinguish unknown, incompatible and known information and define refinement, equivalence and merge for the anchored propagation?"⟩
def showsValidStatesConstructible : Link := ⟨"showsValidStatesConstructible",
  "Does this edit show that the needed valid states of the anchored edit's representation remain constructible?"⟩

/-! The rules. -/

/-- Rule 981: strict types, checked at their strictest with the repository's own checker. -/
def strictTyping : Rule where
  number := 981
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom leavesTypesLoose) ∧ₗ
    (ev commitCall ∧ₗ atom commitsCheckableCode ⟹ once (ev typeCheckRun ∧ₗ link strictestOwnChecker))

/-- Rule 982: decisions in a pure core, effects in a thin outer layer. -/
def pureCore : Rule where
  number := 982
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom mixesEffectsWithDecisions)

/-- Rule 983: config as an explicit parameter, the environment only where passing is very costly. -/
def explicitConfig : Rule where
  number := 983
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom readsConfigFromEnvironment ⟹ atom passingConfigCostly

/-- Rule 984: the outer layer gets integration tests against the real system. -/
def outerLayerIntegrationTests : Rule where
  number := 984
  keyword := .should
  domain := .discipline
  formula := ev commitCall ∧ₗ atom commitsOuterLayer ⟹
    around (ev editing ∧ₗ link testsOuterLayerLive) ∨ₗ atom justified

/-- Rule 985: no program run inline in committed code. -/
def noInlineProgram : Rule where
  number := 985
  keyword := .mustNot
  domain := .discipline
  formula := never (ev editing ∧ₗ atom writesInlineProgram)

/-- Rule 986: the smallest surgical diff and the simplest mechanism. -/
def smallestDiff : Rule where
  number := 986
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom needlessNewStructure)

/-- Rule 987: the cheapest mechanism named, and why it fails, before a costlier one. -/
def cheapestMechanismFirst : Rule where
  number := 987
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom buildsCostlyMechanism ⟹ once (ev reply ∧ₗ link namesCheapestMechanism)

/-- Rule 988: the simplest coherent interface; generality removes special cases. -/
def earnedGenerality : Rule where
  number := 988
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom unearnedGenerality)

/-- Rule 989: asked how, give the literal command. -/
def literalCommand : Rule where
  number := 989
  keyword := .must
  domain := .discipline
  formula := ev user ∧ₗ atom asksHowTo ⟹ eventually (ev reply ∧ₗ link givesRunnableCommand)

/-- Rule 990: proceed on a provisional answer and keep its question open. -/
def provisionalAnswer : Rule where
  number := 990
  keyword := .must
  domain := .discipline
  formula := ev user ∧ₗ atom givesProvisionalAnswer ⟹
    eventually (ev toolCall ∧ₗ link actsOnProvisionalAnswer) ∧ₗ
      ¬ₗ eventually (ev reply ∧ₗ link closesProvisionalQuestion)

/-- Rule 991: no design needing an entry per instance. -/
def noPerInstanceDesign : Rule where
  number := 991
  keyword := .must
  domain := .discipline
  formula := never (atom adoptsPerInstanceDesign)

/-- Rule 992: verification chosen by the change, the least costly, escalated only for a risk. -/
def verificationByChange : Rule where
  number := 992
  keyword := .must
  domain := .discipline
  formula := never (ev toolCall ∧ₗ atom verificationOffChange) ∧ₗ
    (ev toolCall ∧ₗ atom escalatedVerification ⟹ atom unresolvedRiskOrFailure)

/-- Rule 993: a checklist's tools are no separate goals. -/
def checklistToolsNoGoals : Rule where
  number := 993
  keyword := .mustNot
  domain := .discipline
  formula := never (atom checklistToolsAsGoals)

/-- Rule 994: a narrow change's verification stays in its area. -/
def narrowVerification : Rule where
  number := 994
  keyword := .must
  domain := .discipline
  formula := ev toolCall ∧ₗ atom verifiesBeyondAffectedArea ⟹ atom broadBlastRadius

/-- Rule 995: test the tip after a rewrite. -/
def testTipAfterRewrite : Rule where
  number := 995
  keyword := .must
  domain := .discipline
  formula := ev historyRewrite ⟹ eventually (ev checkRun ∧ₗ link testsRewrittenTip)

/-- Rule 996: no repeat of a check whose evidence is in hand, run or planned. -/
def noRepeatedCheck : Rule where
  number := 996
  keyword := .mustNot
  domain := .discipline
  formula := never (ev checkRun ∧ₗ once (ev checkRun ∧ₗ link settlesSameQuestion) ∧ₗ
      ¬ₗ atom canStillFindNew) ∧ₗ
    never (ev editing ∧ₗ atom plansRepeatedCheck)

/-- Rule 997: a shared resource's other consumers checked before it changes. -/
def checkConsumersFirst : Rule where
  number := 997
  keyword := .should
  domain := .discipline
  formula := ev toolCall ∧ₗ atom changesSharedResource ⟹
    once (ev toolCall ∧ₗ link checksResourceConsumers) ∨ₗ atom justified

/-- Rule 998: one mechanism for one concern. -/
def oneMechanism : Rule where
  number := 998
  keyword := .should
  domain := .discipline
  formula := ev reply ∧ₗ atom notesDivergentMechanisms ⟹ atom pushesOneMechanism ∨ₗ atom justified

/-- Rule 999: a shared setting's live value kept before it changes. -/
def keepLiveValue : Rule where
  number := 999
  keyword := .should
  domain := .discipline
  formula := ev toolCall ∧ₗ atom changesSharedSetting ⟹
    once (ev toolCall ∧ₗ link keepsLiveValue) ∨ₗ atom justified

/-- Rule 1000: a change to what a person operates by hand: the whole behaviour stated, the existing
listed, the change measured. -/
def manualOperationChange : Rule where
  number := 1000
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom changesManualOperation ⟹
    once (ev reply ∧ₗ link statesWholeBehaviour) ∧ₗ once (ev reply ∧ₗ link listsExistingBehaviour) ∧ₗ
      eventually (ev checkRun ∧ₗ link measuresManualChange)

/-- Rule 1001: in Lean, proofs over tests. -/
def proofsOverTests : Rule where
  number := 1001
  keyword := .should
  domain := .discipline
  formula := never (ev editing ∧ₗ atom testWhereProofFits) ∨ₗ atom justified

/-- Rule 1002: a test goes once a proof establishes its property. -/
def removeProvedTest : Rule where
  number := 1002
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom provesTestedProperty ⟹ eventually (ev editing ∧ₗ link removesSupersededTest)

/-- Rule 1003: tests of behaviour outside a proof's scope stay. -/
def keepTestsBeyondProof : Rule where
  number := 1003
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom removesTestBeyondProof)

/-- Rule 1004: a relation over generated inputs, never a case table called a property test. -/
def relationNotTable : Rule where
  number := 1004
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom writesCaseTableTest) ∧ₗ
    never (ev reply ∧ₗ atom callsCaseTablePropertyTest)

/-- Rule 1005: a manual-testing hack is marked, never committed, and reverted. -/
def markedTestHack : Rule where
  number := 1005
  keyword := .must
  domain := .discipline
  formula := (ev editing ∧ₗ atom writesTestHack ⟹
      atom hackClearlyMarked ∧ₗ eventually (ev editing ∧ₗ link revertsHack)) ∧ₗ
    never (ev commitCall ∧ₗ atom commitsTestHack)

/-- Rule 1006: automation judged from the caller's whole workflow before it is called done. -/
def automationFromWorkflow : Rule where
  number := 1006
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom callsAutomationDone ⟹ once (ev reply ∧ₗ link walksCallerWorkflow)

/-- Rule 1007: mechanical work in the tool, the caller's judgement stated as its boundary. -/
def mechanicalWorkInTool : Rule where
  number := 1007
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom leavesMechanicalWorkToCaller) ∧ₗ
    (ev editing ∧ₗ atom buildsTool ⟹ atom statesCallerBoundary)

/-- Rule 1008: deep modules over short methods. -/
def deepModules : Rule where
  number := 1008
  keyword := .should
  domain := .discipline
  formula := never (ev editing ∧ₗ atom shallowModule) ∨ₗ atom justified

/-- Rule 1009: check what the user worked out, without re-deriving it. -/
def checkUsersWork : Rule where
  number := 1009
  keyword := .must
  domain := .discipline
  formula := ev user ∧ₗ atom presentsWorkedResult ⟹
    eventually (ev toolCall ∧ₗ link checksUsersResult) ∧ₗ
      ¬ₗ eventually (ev reply ∧ₗ link rederivesUsersResult)

/-- Rule 1010: one's own artifact reviewed by a fresh-context reviewer given only it. -/
def freshReviewOfOwnWork : Rule where
  number := 1010
  keyword := .should
  domain := .discipline
  formula := ev reply ∧ₗ atom offersArtifact ⟹
    once (ev agentRun ∧ₗ link freshReviewOfArtifact) ∨ₗ atom justified

/-- Rule 1011: independent judgement of a floated proposal. -/
def independentJudgement : Rule where
  number := 1011
  keyword := .must
  domain := .discipline
  formula := ev user ∧ₗ atom floatsProposal ⟹ eventually (ev reply ∧ₗ link judgesProposalIndependently)

/-- Rule 1012: a delegation carries the goal, the spec, the decisions and the checks. -/
def delegateWithGoal : Rule where
  number := 1012
  keyword := .must
  domain := .discipline
  formula := never (ev agentRun ∧ₗ atom briefLacksGoal)

/-- Rule 1013: stale content pruned, a finished task's branches included. -/
def pruneStale : Rule where
  number := 1013
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom keepsStaleContent) ∧ₗ
    (ev reply ∧ₗ atom closesTask ⟹ ¬ₗ atom leavesFinishedBranches)

/-- Rule 1014: a method's cost weighed beside its correctness, cost buying nothing cut. -/
def weighMethodCost : Rule where
  number := 1014
  keyword := .must
  domain := .discipline
  formula := (ev toolCall ∧ₗ atom costlyMethod ⟹ once (ev reply ∧ₗ link weighsMethodCost)) ∧ₗ
    never (ev toolCall ∧ₗ atom costBuysNothing)

/-- Rule 1015: heavy computation: its time estimated first, compiled and parallel. -/
def heavyComputationPrepared : Rule where
  number := 1015
  keyword := .must
  domain := .discipline
  formula := ev toolCall ∧ₗ atom heavyComputation ⟹
    once (ev reply ∧ₗ link estimatesRunTime) ∧ₗ atom runsCompiledParallel

/-- Rule 1016: a process change removes friction, and one adding friction is changed. -/
def processChangeRemovesFriction : Rule where
  number := 1016
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom processChangeAddsFriction) ∧ₗ
    (ev reply ∧ₗ atom reportsProcessFriction ⟹ eventually (ev editing ∧ₗ link changesFrictionalProcess))

/-- Rule 1017: a process change judged on its first use, a multiplied time reported as failed. -/
def judgeProcessChange : Rule where
  number := 1017
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom reportsProcessChangeUse ⟹
    atom comparesTimeAndDefects ∧ₗ (atom processTimeMultiplied ⟹ atom reportsFailedExperiment)

/-- Rule 1018: no step growing with every fix; hours and tokens reviewed against the task. -/
def watchGrowingSteps : Rule where
  number := 1018
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom growsStepPerFix) ∧ₗ
    (ev reply ∧ₗ atom reportsCycle ⟹ atom weighsHoursAndTokens)

/-- Rule 1019: once the design decides, build; reopen it only for a contradiction or a gap. -/
def buildOnceDecided : Rule where
  number := 1019
  keyword := .must
  domain := .discipline
  formula := (ev reply ∧ₗ atom designDecidesBehaviour ⟹ eventually (ev editing ∧ₗ link buildsNextArtifact)) ∧ₗ
    (ev editing ∧ₗ atom reopensDesign ⟹ atom contradictionOrUndecided)

/-- Rule 1020: a complete procedure enumerates its input mechanically. -/
def mechanicalEnumeration : Rule where
  number := 1020
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom incompleteEnumeration)

/-- Rule 1021: no record growing multiplicatively; ask what it grows with first. -/
def recordGrowth : Rule where
  number := 1021
  keyword := .mustNot
  domain := .discipline
  formula := never (ev editing ∧ₗ atom recordGrowsMultiplicatively) ∧ₗ
    (ev editing ∧ₗ atom addsRuleListOrField ⟹ once (ev reply ∧ₗ link asksRecordGrowth))

/-- Rule 1022: a rule kept being broken gets a minimal check. -/
def enforceBrokenRule : Rule where
  number := 1022
  keyword := .should
  domain := .discipline
  formula := ev reply ∧ₗ atom notesRepeatedBreach ⟹
    eventually (ev editing ∧ₗ link addsMinimalCheck) ∨ₗ atom justified

/-- Rule 1023: judgement calls stay with judgement. -/
def judgementNotChecks : Rule where
  number := 1023
  keyword := .should
  domain := .discipline
  formula := never (ev editing ∧ₗ atom checksJudgementCall) ∨ₗ atom justified

/-- Rule 1024: status against the goal and the open items. -/
def statusAgainstGoalRule : Rule where
  number := 1024
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom reportsStatus ⟹ atom statusAgainstGoal

/-- Rule 1025: no wasted wall-clock time. -/
def noWastedTime : Rule where
  number := 1025
  keyword := .mustNot
  domain := .discipline
  formula := never (ev reply ∧ₗ atom idlesWhileWorkRemains)

/-- Rule 1026: a report or a hand-over ends nothing; a full machine limits no own work. -/
def reportEndsNothing : Rule where
  number := 1026
  keyword := .mustNot
  domain := .discipline
  formula := never (ev reply ∧ₗ atom treatsReportAsEnd) ∧ₗ never (ev reply ∧ₗ atom blamesFullMachine)

/-- Rule 1027: short polls and timeouts, independent checks in parallel. -/
def shortPolls : Rule where
  number := 1027
  keyword := .should
  domain := .discipline
  formula := never (ev toolCall ∧ₗ atom slowPolling) ∨ₗ atom justified

/-- Rule 1028: a batch projected from the measured rate, stopped when it exceeds what is acceptable. -/
def projectBeforeBatch : Rule where
  number := 1028
  keyword := .must
  domain := .discipline
  formula := ev toolCall ∧ₗ atom startsBatch ⟹
    once (ev reply ∧ₗ link projectsFromRate) ∧ₗ ¬ₗ atom projectionExceedsAcceptable

/-- Rule 1029: a third round finding one class brings counts and a design removing it. -/
def thirdRoundRedesign : Rule where
  number := 1029
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom thirdRoundSameClass ⟹ atom bringsCountsAndDesign

/-- Rule 1030: an order names its dependency; independent work runs together. -/
def orderIsDependency : Rule where
  number := 1030
  keyword := .must
  domain := .discipline
  formula := never (ev reply ∧ₗ atom ordersWithoutDependency) ∧ₗ
    never (ev toolCall ∧ₗ atom serializesIndependentWork)

/-- Rule 1031: a failed gate blocks only its dependent artifact. -/
def gateBlocksDependentOnly : Rule where
  number := 1031
  keyword := .must
  domain := .discipline
  formula := never (ev reply ∧ₗ atom blocksIndependentOnGate) ∧ₗ
    (ev reply ∧ₗ atom declaresTaskBlocked ⟹ once (ev reply ∧ₗ link reassessesBuildable))

/-- Rule 1032: review inputs isolated by access. -/
def isolateReviewInputs : Rule where
  number := 1032
  keyword := .must
  domain := .discipline
  formula := never (ev agentRun ∧ₗ atom reviewerSeesBeyondInput)

/-- Rule 1033: the tracker issue and its links read before designing. -/
def readIssueFirst : Rule where
  number := 1033
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom writesDesign ⟹
    once (ev toolCall ∧ₗ link readsTrackerIssue) ∧ₗ once (ev toolCall ∧ₗ link readsIssueLinks)

/-- Rule 1034: access confirmed at the start, production credentials asked for. -/
def confirmAccessAtStart : Rule where
  number := 1034
  keyword := .must
  domain := .discipline
  formula := ev user ∧ₗ atom assignsTask ⟹
    eventually (ev toolCall ∧ₗ link confirmsAccess) ∧ₗ
      (atom needsProductionVerification ⟹ eventually (ev reply ∧ₗ link asksProductionCredentials))

/-- Rule 1035: the source of truth and ownership settled before implementing. -/
def settleSourceOfTruth : Rule where
  number := 1035
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom implementsChange ⟹ once (ev reply ∧ₗ link settlesSourceOfTruth)

/-- Rule 1036: CI, the Makefile and the lockfile read before choosing a tool. -/
def readBuildConfigFirst : Rule where
  number := 1036
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom choosesTool ⟹ once (ev reading ∧ₗ link readsBuildConfig)

/-- Rule 1037: the settings loader read before naming an environment variable. -/
def readSettingsLoaderFirst : Rule where
  number := 1037
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom namesEnvVariable ⟹ once (ev reading ∧ₗ link readsSettingsLoader)

/-- Rule 1038: whether a tool exists is searched for in the ecosystem. -/
def searchEcosystem : Rule where
  number := 1038
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom judgesToolExistence ⟹ once (ev webLookup ∧ₗ link searchesForTool)

/-- Rule 1039: existing fields searched before adding one. -/
def searchFieldsFirst : Rule where
  number := 1039
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom addsField ⟹ once (ev searching ∧ₗ link searchesExistingFields)

/-- Rule 1040: a live route confirmed before citing a file as the convention. -/
def confirmConventionRoute : Rule where
  number := 1040
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom citesConvention ⟹ once (ev toolCall ∧ₗ link confirmsLiveRoute)

/-- Rule 1041: each fixed choice names who decides it. -/
def nameTheDecider : Rule where
  number := 1041
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom fixesDesignChoice ⟹ atom namesDecider

/-- Rule 1042: a mechanism the user proposes settled by its stated purpose. -/
def mechanismByPurpose : Rule where
  number := 1042
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom offersUserMechanism ⟹ atom checksPartsAgainstPurpose

/-- Rule 1043: a recommendation read beside the cause it answers. -/
def recommendationAgainstCause : Rule where
  number := 1043
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom recommends ⟹ atom recommendationAnswersCause

/-- Rule 1044: a sync designs create, update and delete each way. -/
def syncBothWays : Rule where
  number := 1044
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom syncMissesOperation)

/-- Rule 1045: design against replicas and concurrent writers. -/
def designForReplicas : Rule where
  number := 1045
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom ignoresReplicasOrWriters)

/-- Rule 1046: a decision function's bad inputs listed. -/
def listBadInputs : Rule where
  number := 1046
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom decisionInputsUnlisted)

/-- Rule 1047: every mechanism a decision names mapped to a step or out of scope. -/
def mapMechanisms : Rule where
  number := 1047
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom unmappedMechanism)

/-- Rule 1048: one verifiable artifact per increment; splits keep obligations and report from the
artifact list. -/
def oneArtifactPerIncrement : Rule where
  number := 1048
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom incrementHoldsSeveralArtifacts) ∧ₗ
    never (ev editing ∧ₗ atom splitDropsObligations) ∧ₗ
    (ev reply ∧ₗ atom reportsIncrements ⟹ atom fromArtifactList)

/-- Rule 1049: the ticket's requirements rechecked after a redesign. -/
def recheckAfterRedesign : Rule where
  number := 1049
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom redesigns ⟹ eventually (ev reply ∧ₗ link rechecksTicketRequirements)

/-- Rule 1050: a library's semantics checked before a design relies on them. -/
def checkLibrarySemantics : Rule where
  number := 1050
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom proposesDesignOnLibrary ⟹ once (ev toolCall ∧ₗ link checksLibrarySemantics)

/-- Rule 1051: whether a tool already does the job checked before designing around its limit. -/
def checkToolFirst : Rule where
  number := 1051
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom designsAroundToolLimit ⟹ once (ev toolCall ∧ₗ link checksToolPrimitives)

/-- Rule 1052: a tool reports its verified outcome; a repeated hand confirmation moves into it. -/
def toolVerifiesOutcome : Rule where
  number := 1052
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom toolReportsUnverifiedOutcome) ∧ₗ
    (ev toolCall ∧ₗ atom confirmsToolByHand ∧ₗ once (ev toolCall ∧ₗ link sameHandConfirmation) ⟹
      eventually (ev editing ∧ₗ link movesConfirmationIntoTool) ∨ₗ atom justified)

/-- Rule 1053: what runs every turn is timed on a real input, its latency stated. -/
def timePerTurnProposal : Rule where
  number := 1053
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom proposesPerTurnMechanism ⟹
    once (ev toolCall ∧ₗ link timesOnRealInput) ∧ₗ atom statesLatency

/-- Rule 1054: an option every caller wants is the default behaviour instead. -/
def optionOrDefault : Rule where
  number := 1054
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom addsOption ⟹
    once (ev reply ∧ₗ link asksCallersWant) ∧ₗ ¬ₗ atom everyCallerWantsIt

/-- Rule 1055: a stopped async task drops in-flight results, tested by a late resolution. -/
def dropInFlightResults : Rule where
  number := 1055
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom stopsRepeatingAsyncTask ⟹
    atom dropsInFlightResults ∧ₗ around (ev editing ∧ₗ link testsResolveAfterStop)

/-- Rule 1056: a model judge built as a hybrid. -/
def hybridJudge : Rule where
  number := 1056
  keyword := .should
  domain := .discipline
  formula := ev editing ∧ₗ atom buildsModelJudge ⟹ atom judgeIsHybrid ∨ₗ atom justified

/-- Rule 1057: a refusing judge errs toward passing. -/
def judgeErrsToPass : Rule where
  number := 1057
  keyword := .should
  domain := .discipline
  formula := never (ev editing ∧ₗ atom judgeErrsTowardRefusing) ∨ₗ atom justified

/-- Rule 1058: refusing verdicts' inputs kept; a judge changed only on a replay of them. -/
def judgeChangedByReplay : Rule where
  number := 1058
  keyword := .should
  domain := .discipline
  formula := (never (ev editing ∧ₗ atom dropsRefusingInputs) ∧ₗ
      (ev editing ∧ₗ atom changesJudge ⟹ around (ev checkRun ∧ₗ link replaysKeptInputs))) ∨ₗ
    atom justified

/-- Rule 1059: dependent layers in commit order. -/
def layersInCommitOrder : Rule where
  number := 1059
  keyword := .must
  domain := .discipline
  formula := never (ev commitCall ∧ₗ atom commitsBeforeItsLayer)

/-- Rule 1060: no gate serializing independent work; each artifact verified before it lands. -/
def gateSerializesNothing : Rule where
  number := 1060
  keyword := .mustNot
  domain := .discipline
  formula := never (ev reply ∧ₗ atom waitsOnGateForIndependentWork) ∧ₗ
    (ev toolCall ∧ₗ atom landsArtifact ⟹ once (ev checkRun ∧ₗ link verifiesLandedArtifact))

/-- Rule 1061: code carried from an old branch by first use. -/
def carryByFirstUse : Rule where
  number := 1061
  keyword := .must
  domain := .discipline
  formula := never (ev commitCall ∧ₗ atom carriesUnusedCode)

/-- Rule 1062: stage by content a file serving several commits, since the previous commit. -/
def stageByContent : Rule where
  number := 1062
  keyword := .must
  domain := .discipline
  formula := ev commitCall ∧ₗ atom fileServesSeveralCommits ⟹ since (ev hunkStaging) (ev commitCall)

/-- Rule 1063: each commit's symbols checked for a user since the previous commit; no unused one. -/
def symbolsHaveUsers : Rule where
  number := 1063
  keyword := .must
  domain := .discipline
  formula := ev commitCall ⟹
    since (ev toolCall ∧ₗ link checksSymbolUse) (ev commitCall) ∧ₗ ¬ₗ atom commitsUnusedSymbol

/-- Rule 1064: a fixup aimed at its commit, the staged stat checked since the previous commit. -/
def aimedFixup : Rule where
  number := 1064
  keyword := .must
  domain := .discipline
  formula := ev fixupCall ⟹ since (ev cachedStatCall) (ev commitCall) ∧ₗ ¬ₗ atom fixupMisaimed

/-- Rule 1065: a change to an earlier commit's code committed as its fixup, apart from the step. -/
def fixupAtOnce : Rule where
  number := 1065
  keyword := .must
  domain := .discipline
  formula := (ev editing ∧ₗ atom changesEarlierCommitsCode ⟹ eventually (ev fixupCall ∧ₗ link fixupOfThatChange)) ∧ₗ
    never (ev commitCall ∧ₗ atom foldsEarlierFixIntoStep)

/-- Rule 1066: realign by splitting in place and folding, not fixup pairs at the tip. -/
def realignBySplitting : Rule where
  number := 1066
  keyword := .must
  domain := .discipline
  formula := never (ev toolCall ∧ₗ atom realignsWithFixupPairsAtTip)

/-- Rule 1067: a changed decision's dependent text searched for. -/
def grepAfterDecision : Rule where
  number := 1067
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom changesDecision ⟹ around (ev searching ∧ₗ link searchesDependentText)

/-- Rule 1068: changed code's lines searched for in the evidence and prose quoting them. -/
def grepAfterCodeChange : Rule where
  number := 1068
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom changesCode ⟹ around (ev searching ∧ₗ link searchesQuotedLines)

/-- Rule 1069: tests designed from the checking rules. -/
def testsFromRules : Rule where
  number := 1069
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom testsShapedByExisting)

/-- Rule 1070: without an answer key, check by relations. -/
def checkByRelations : Rule where
  number := 1070
  keyword := .should
  domain := .discipline
  formula := ev editing ∧ₗ atom writesCheckWithoutAnswerKey ⟹ atom checksByRelations ∨ₗ atom justified

/-- Rule 1071: the first refusal a stand-in costs is the sign. -/
def standInSign : Rule where
  number := 1071
  keyword := .should
  domain := .discipline
  formula := ev hookRefusal ∧ₗ atom standInRefusal ⟹
    eventually (ev reply ∧ₗ link treatsAsStandInSign) ∨ₗ atom justified

/-- Rule 1073: times worked out by hand; a worst case adds every blocking step. -/
def timesByHand : Rule where
  number := 1073
  keyword := .must
  domain := .discipline
  formula := never (ev reply ∧ₗ atom assertsUnworkedTime) ∧ₗ never (ev reply ∧ₗ atom worstCaseMissesSteps)

/-- Rule 1074: scheduled code tested through the real scheduler. -/
def testThroughScheduler : Rule where
  number := 1074
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom testsScheduledCodeDirectly)

/-- Rule 1075: where a hung run stands read before rerunning it. -/
def inspectHungRun : Rule where
  number := 1075
  keyword := .must
  domain := .discipline
  formula := ev toolCall ∧ₗ atom rerunsHungRun ⟹ once (ev toolCall ∧ₗ link inspectsHungRun)

/-- Rule 1076: a convention for a standard tool looked for before a custom check. -/
def standardToolConvention : Rule where
  number := 1076
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom buildsCheckForUncaughtMistake ⟹
    once (ev reply ∧ₗ link considersStandardToolConvention)

/-- Rule 1077: a question a short check answers is settled by running it. -/
def runShortCheck : Rule where
  number := 1077
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom settlesCheckableQuestion ⟹ once (ev toolCall ∧ₗ link runsSettlingCheck)

/-- Rule 1078: each job with the tool made for it. -/
def toolMadeForJob : Rule where
  number := 1078
  keyword := .must
  domain := .discipline
  formula := never (ev toolCall ∧ₗ atom wrongToolForJob)

/-- Rule 1079: a reset removing migrations resets the local database. -/
def resetDatabaseToo : Rule where
  number := 1079
  keyword := .must
  domain := .discipline
  formula := ev branchReset ∧ₗ atom resetRemovesMigrations ⟹ eventually (ev toolCall ∧ₗ link resetsLocalDatabase)

/-- Rule 1080: tests pinning the head searched for when adding a migration. -/
def grepHeadPins : Rule where
  number := 1080
  keyword := .must
  domain := .discipline
  formula := ev migrationEdit ⟹ around (ev searching ∧ₗ link searchesHeadPins)

/-- Rule 1081: a chart value traced to its template and code, and the chart rendered. -/
def traceAndRenderChart : Rule where
  number := 1081
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom editsChartValue ⟹
    around (ev toolCall ∧ₗ link tracesChartValue) ∧ₗ around (ev chartRender)

/-- Rule 1082: a working API recipe recorded the moment it succeeds. -/
def recordApiRecipe : Rule where
  number := 1082
  keyword := .must
  domain := .discipline
  formula := ev passingResult ∧ₗ atom apiRecipeSucceeds ⟹ eventually (ev editing ∧ₗ link recordsApiRecipe)

/-- Rule 1083: leftover branches and worktrees listed for deletion. -/
def listLeftovers : Rule where
  number := 1083
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom closesTask ⟹ atom listsLeftoverBranches

/-- Rule 1084: the records' counts and status checked against the final state. -/
def checkRecordsAtClose : Rule where
  number := 1084
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom closesTask ⟹ once (ev toolCall ∧ₗ link checksRecordsAgainstFinal)

/-- Rule 1085: design analysis starts from a concrete change or caller journey. -/
def analysisFromJourney : Rule where
  number := 1085
  keyword := .should
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom analysesDesign ⟹ atom startsFromCallerJourney ∨ₗ atom justified

/-- Rule 1086: the dependency behind each symptom traced. -/
def traceSymptomDependency : Rule where
  number := 1086
  keyword := .should
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom analysesDesign ⟹ atom tracesSymptomDependency ∨ₗ atom justified

/-- Rule 1087: each module's knowledge and its duplicates named. -/
def nameOwnedKnowledge : Rule where
  number := 1087
  keyword := .should
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom analysesDesign ⟹ atom namesOwnedKnowledge ∨ₗ atom justified

/-- Rule 1088: each leak's three options compared. -/
def compareLeakOptions : Rule where
  number := 1088
  keyword := .should
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom findsKnowledgeLeak ⟹ atom comparesLeakOptions ∨ₗ atom justified

/-- Rule 1089: a forwarding layer's contribution named before its removal is proposed. -/
def layerContributionFirst : Rule where
  number := 1089
  keyword := .should
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom proposesRemovingLayer ⟹ atom namesLayerContribution ∨ₗ atom justified

/-- Rule 1090: necessary public semantics stay in the contract. -/
def publicSemanticsInContract : Rule where
  number := 1090
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom hidesPublicSemantics) ∨ₗ atom justified

/-- Rule 1091: an interface hard to explain is simplified. -/
def explanationAsProbe : Rule where
  number := 1091
  keyword := .should
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom interfaceHardToExplain ⟹
    eventually (ev editing ∧ₗ link simplifiesAbstraction) ∨ₗ atom justified

/-- Rule 1092: a kept specialization states its benefit for the caller. -/
def specializationBenefit : Rule where
  number := 1092
  keyword := .should
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom keepsSpecialization ⟹ atom statesCallerBenefit ∨ₗ atom justified

/-- Rule 1093: an option only where its value varies or a wrong default harms. -/
def justifiedOption : Rule where
  number := 1093
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom needlessOption) ∨ₗ atom justified

/-- Rule 1094: authorization, policy and failure behaviour are contract choices. -/
def policyInContract : Rule where
  number := 1094
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom policyAsInternalDefault)

/-- Rule 1095: a design finding names symptom, decision, owner and consequence. -/
def completeDesignFinding : Rule where
  number := 1095
  keyword := .should
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom reportsDesignFinding ⟹ atom findingNamesAll ∨ₗ atom justified

/-- Rule 1096: combinations usable wherever a primitive is. -/
def closedCombinations : Rule where
  number := 1096
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom combinationLosesContract) ∨ₗ atom justified

/-- Rule 1097: nested combinations checked for lost information. -/
def checkNestedCombinations : Rule where
  number := 1097
  keyword := .should
  domain := .softwareEngineering
  formula := ev editing ∧ₗ atom buildsCombination ⟹
    around (ev checkRun ∧ₗ link checksNestedCombination) ∨ₗ atom justified

/-- Rule 1098: an algorithm parameterized by its operations and laws. -/
def lawfulParameters : Rule where
  number := 1098
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom lawBreakingSubstitution) ∨ₗ atom justified

/-- Rule 1099: an extensible operation defines its dispatch. -/
def defineDispatch : Rule where
  number := 1099
  keyword := .should
  domain := .softwareEngineering
  formula := ev editing ∧ₗ atom buildsExtensibleOperation ⟹ atom definesDispatchRules ∨ₗ atom justified

/-- Rule 1100: a new handler checked against old, mixed and competing inputs. -/
def checkNewHandler : Rule where
  number := 1100
  keyword := .should
  domain := .softwareEngineering
  formula := ev editing ∧ₗ atom addsHandler ⟹
    around (ev checkRun ∧ₗ link checksHandlerInteractions) ∨ₗ atom justified

/-- Rule 1101: selecting a handler apart from running it. -/
def separateSelection : Rule where
  number := 1101
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom fusesSelectionAndRun) ∨ₗ atom justified

/-- Rule 1102: description, preparation and execution apart. -/
def separateStages : Rule where
  number := 1102
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom fusesReusedStages) ∨ₗ atom justified

/-- Rule 1103: a deferred computation's run, environment, rerun and release defined. -/
def defineDeferral : Rule where
  number := 1103
  keyword := .should
  domain := .softwareEngineering
  formula := ev editing ∧ₗ atom defersComputation ⟹ atom definesDeferralSemantics ∨ₗ atom justified

/-- Rule 1104: generated identities fresh across deferred computations. -/
def freshIdentities : Rule where
  number := 1104
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom reusesGeneratedIdentity) ∨ₗ atom justified

/-- Rule 1105: each annotation its own rules and a meaning for missing metadata. -/
def annotationRules : Rule where
  number := 1105
  keyword := .should
  domain := .softwareEngineering
  formula := ev editing ∧ₗ atom addsAnnotation ⟹ atom definesAnnotationRules ∨ₗ atom justified

/-- Rule 1106: provenance's kind chosen and its omissions stated. -/
def provenanceScope : Rule where
  number := 1106
  keyword := .should
  domain := .softwareEngineering
  formula := ev editing ∧ₗ atom recordsProvenance ⟹ atom statesProvenanceScope ∨ₗ atom justified

/-- Rule 1107: knowledge states and merge defined before propagation. -/
def knowledgeStatesFirst : Rule where
  number := 1107
  keyword := .should
  domain := .softwareEngineering
  formula := ev editing ∧ₗ atom implementsPropagation ⟹
    once (ev editing ∧ₗ link definesKnowledgeStates) ∨ₗ atom justified

/-- Rule 1108: merge laws and cyclic termination established. -/
def mergeLaws : Rule where
  number := 1108
  keyword := .should
  domain := .softwareEngineering
  formula := ev editing ∧ₗ atom implementsPropagation ⟹ atom statesMergeLawsAndTermination ∨ₗ
    atom justified

/-- Rule 1109: assertions apart from derived consequences; retraction precise. -/
def assertionsApart : Rule where
  number := 1109
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom mixesAssertionsAndDerived) ∨ₗ atom justified

/-- Rule 1110: generation, acceptance and scheduling replaceable apart. -/
def separableSearch : Rule where
  number := 1110
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom fusesSearchParts) ∨ₗ atom justified

/-- Rule 1111: failed combinations retained, not re-explored. -/
def retainFailedCombinations : Rule where
  number := 1111
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom reexploresFailedCombinations) ∨ₗ atom justified

/-- Rule 1112: exhaustion apart from a limit; methods reconciled by a rule. -/
def exhaustionAndReconciliation : Rule where
  number := 1112
  keyword := .should
  domain := .softwareEngineering
  formula := (never (ev editing ∧ₗ atom conflatesExhaustionAndLimit) ∧ₗ
      never (ev editing ∧ₗ atom votesWithoutReconciliation)) ∨ₗ atom justified

/-- Rule 1113: sums, products and meaningful options. -/
def stateShape : Rule where
  number := 1113
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom mismatchedStateShape) ∨ₗ atom justified

/-- Rule 1114: valid states shown constructible beside invalid ones excluded. -/
def validStatesConstructible : Rule where
  number := 1114
  keyword := .should
  domain := .softwareEngineering
  formula := ev editing ∧ₗ atom excludesInvalidStates ⟹
    atom showsValidConstructible ∨ₗ around (ev editing ∧ₗ link showsValidStatesConstructible) ∨ₗ
      atom justified

/-- Rule 1115: an explicit mapping, not equal cardinality. -/
def explicitMapping : Rule where
  number := 1115
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom mapsByCardinality) ∨ₗ atom justified

/-- Rule 1116: partiality accounted for before types-as-propositions. -/
def accountForPartiality : Rule where
  number := 1116
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev reply ∧ₗ atom ignoresPartiality) ∨ₗ atom justified

/-- Rule 1117: identifiers, units and states told apart. -/
def distinguishSharedRepresentation : Rule where
  number := 1117
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom conflatesSharedRepresentation) ∨ₗ atom justified

/-- Rule 1118: a constructor establishes what its consumers rely on. -/
def constructorEvidence : Rule where
  number := 1118
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom constructorLeavesInvariant) ∨ₗ atom justified

/-- Rule 1119: a tag and its payload in one package. -/
def tagWithPayload : Rule where
  number := 1119
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom splitsTagFromPayload) ∨ₗ atom justified

/-- Rule 1120: an invariant about a past observation revalidated before acting. -/
def revalidateObservation : Rule where
  number := 1120
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom actsOnStaleObservation) ∨ₗ atom justified

def rules : List Rule :=
  [strictTyping, pureCore, explicitConfig, outerLayerIntegrationTests, noInlineProgram, smallestDiff,
   cheapestMechanismFirst, earnedGenerality, literalCommand, provisionalAnswer, noPerInstanceDesign,
   verificationByChange, checklistToolsNoGoals, narrowVerification, testTipAfterRewrite,
   noRepeatedCheck, checkConsumersFirst, oneMechanism, keepLiveValue, manualOperationChange,
   proofsOverTests, removeProvedTest, keepTestsBeyondProof, relationNotTable, markedTestHack,
   automationFromWorkflow, mechanicalWorkInTool, deepModules, checkUsersWork, freshReviewOfOwnWork,
   independentJudgement, delegateWithGoal, pruneStale, weighMethodCost, heavyComputationPrepared,
   processChangeRemovesFriction, judgeProcessChange, watchGrowingSteps, buildOnceDecided,
   mechanicalEnumeration, recordGrowth, enforceBrokenRule, judgementNotChecks, statusAgainstGoalRule,
   noWastedTime, reportEndsNothing, shortPolls, projectBeforeBatch, thirdRoundRedesign,
   orderIsDependency, gateBlocksDependentOnly, isolateReviewInputs, readIssueFirst,
   confirmAccessAtStart, settleSourceOfTruth, readBuildConfigFirst, readSettingsLoaderFirst,
   searchEcosystem, searchFieldsFirst, confirmConventionRoute, nameTheDecider, mechanismByPurpose,
   recommendationAgainstCause, syncBothWays, designForReplicas, listBadInputs, mapMechanisms,
   oneArtifactPerIncrement, recheckAfterRedesign, checkLibrarySemantics, checkToolFirst,
   toolVerifiesOutcome, timePerTurnProposal, optionOrDefault, dropInFlightResults, hybridJudge,
   judgeErrsToPass, judgeChangedByReplay, layersInCommitOrder, gateSerializesNothing,
   carryByFirstUse, stageByContent, symbolsHaveUsers, aimedFixup, fixupAtOnce, realignBySplitting,
   grepAfterDecision, grepAfterCodeChange, testsFromRules, checkByRelations, standInSign,
   timesByHand, testThroughScheduler, inspectHungRun, standardToolConvention, runShortCheck,
   toolMadeForJob, resetDatabaseToo, grepHeadPins, traceAndRenderChart, recordApiRecipe,
   listLeftovers, checkRecordsAtClose, analysisFromJourney, traceSymptomDependency,
   nameOwnedKnowledge, compareLeakOptions, layerContributionFirst, publicSemanticsInContract,
   explanationAsProbe, specializationBenefit, justifiedOption, policyInContract,
   completeDesignFinding, closedCombinations, checkNestedCombinations, lawfulParameters,
   defineDispatch, checkNewHandler, separateSelection, separateStages, defineDeferral,
   freshIdentities, annotationRules, provenanceScope, knowledgeStatesFirst, mergeLaws,
   assertionsApart, separableSearch, retainFailedCombinations, exhaustionAndReconciliation,
   stateShape, validStatesConstructible, explicitMapping, accountForPartiality,
   distinguishSharedRepresentation, constructorEvidence, tagWithPayload, revalidateObservation]

/-- The MAY rule 1072, stated as `combinedReadOnlyChecksAllowed`. -/
def permissions : List Nat := [1072]

/-- Rule 1072 (MAY): read-only checks combined in one command keep this range's rules and the
sample's rules on running state (23, 53), every question a model is asked about the command answered
no (it changes nothing, wastes nothing, uses the tools made for its jobs). Rule 72, which the
permission qualifies, is in another range's module. -/
theorem combinedReadOnlyChecksAllowed :
    (rules ++ [runningStateNeedsAsk, questionIsNoGoAhead]).all (fun r =>
      run r (seq [bash "git status && git log --oneline -3 && ls"])
        ((r.formula.atoms.map fun a => (Examples.atom a 0, false)) ++
          (r.formula.links.map fun l => (Examples.link l 0 0, false))) == .kept) = true := by
  decide

/-- The rules' numbers are this range's, in order, each once. -/
theorem numbers : (rules.map (·.number)) ++ permissions =
    (List.range' 981 140).filter (· != 1072) ++ [1072] := by decide

end Rails.Ruleset.Range8
