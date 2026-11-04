import Rails.Rules
import Rails.Examples
import Rails.Witness
import Rails.WellFormed

/-!
Rules 141 to 280 of `tasks/agents-on-rails/RULES.md`, rule 170 (the sample's) left out: the
evidence, verification, testing, checking and theory-checklist rules, and the review loop's briefs.
Rule 154 is a MAY rule, stated as a theorem; the others are formulas.
-/

namespace Rails.Ruleset.Range2
open Rails Formula Ruleset Rules Examples

/-! Event tests this range needs beyond the shared ones. -/

private def word (s : String) (ws : List (List Char)) : Bool := ws.contains s.toList

/-- A path's last component. -/
def baseName (w : List Char) : List Char := (w.reverse.takeWhile (· != '/')).reverse

/-- Some command runs one of the programs named (by its last path component), directly or through
`compute.sh`. -/
def runsAny (names : List String) (e : Event) : Bool :=
  let named (w : List Char) := names.any fun n => baseName w == n.toList
  (programs e).any fun (w, ws) => named w || (baseName w == "compute.sh".toList && ws.any named)

private def commandMentions (s : String) (e : Event) : Bool :=
  match command e with
  | some c => occursIn s.toList c.toList
  | none => false

private def writesPathWith (p : List Char → Bool) (e : Event) : Bool :=
  match writePath e with
  | some f => p f.toList
  | none => false

/-- A `|` that is not part of `||`. -/
def hasSinglePipe : List Char → Bool
  | [] => false
  | c :: rest =>
    if c == '|' then
      match rest with
      | d :: r => if d == '|' then hasSinglePipe r else true
      | [] => true
    else hasSinglePipe rest

def isCommit (e : Event) : Bool := runs "git" (word "commit") e

/-- A test run: pytest or our parallel runners, `lake test`, `cargo test`, `go test`, `npm test`. -/
def isTestRun (e : Event) : Bool :=
  runsAny ["pytest", "pytest_queue.py", "run.py"] e || runs "lake" (word "test") e ||
    runs "cargo" (word "test") e || runs "go" (word "test") e || runs "npm" (word "test") e

def isMutationRun (e : Event) : Bool := runsAny ["mutation_batch.py"] e
def isRealRun (e : Event) : Bool := runsAny ["real_run.py"] e
def isEntryAppend (e : Event) : Bool := runsAny ["notebook-append.py", "task_checkpoint.py"] e
/-- A task checkpoint, which ends a cycle (TASK_PROTOCOL.md: "A checkpoint ends a cycle"). -/
def isCheckpoint (e : Event) : Bool := runsAny ["task_checkpoint.py"] e
def isBrowserRender (e : Event) : Bool := commandMentions "playwright" e || commandMentions "chromium" e
def isPlanEdit (e : Event) : Bool := writesPathWith (endsWith "PLAN.md".toList) e
def isNotebookEdit (e : Event) : Bool := writesPathWith (endsWith "notebook.html".toList) e
def isPrivateEdit (e : Event) : Bool := writesPathWith (occursIn "/private/".toList) e
def isTestEdit (e : Event) : Bool := writesPathWith (occursIn "test".toList) e

/-- A shell pipeline whose command doesn't set `pipefail`. -/
def isPipelineNoPipefail (e : Event) : Bool :=
  match command e with
  | some c => hasSinglePipe c.toList && !occursIn "pipefail".toList c.toList
  | none => false

theorem real_run_is_no_test_run : isTestRun (bash "python3 tools/real_run.py out -- make") = false := by
  decide +kernel
theorem compute_test_run : isTestRun (bash "./compute.sh python3 tools/tests/run.py test_x") = true := by
  decide +kernel
theorem or_is_no_pipeline : isPipelineNoPipefail (bash "make || true") = false := by decide +kernel
theorem pipefail_pipeline : isPipelineNoPipefail (bash "set -o pipefail; make | tee log") = false := by
  decide +kernel
theorem private_edit_is_edit : isPrivateEdit (edit "tasks/x/README.md") = false := by decide +kernel

def commit : Pred := ⟨"commit", isCommit, [bash "git commit -m fix"]⟩
def testRun : Pred := ⟨"testRun", isTestRun,
  [bash "pytest -q", bash "./compute.sh python3 tools/tests/run.py test_x", bash "lake test"]⟩
def mutationRun : Pred := ⟨"mutationRun", isMutationRun,
  [bash "./compute.sh python3 tools/mutation_batch.py . spec.json"]⟩
def realRun : Pred := ⟨"realRun", isRealRun, [bash "python3 tools/real_run.py out -- make"]⟩
def entryAppend : Pred := ⟨"entryAppend", isEntryAppend,
  [bash "python3 tools/notebook-append.py notebook.html e.html",
   bash "python3 tools/task_checkpoint.py --entry e.html"]⟩
def checkpoint : Pred := ⟨"checkpoint", isCheckpoint,
  [bash "python3 tools/task_checkpoint.py --entry e.html"]⟩
def browserRender : Pred := ⟨"browserRender", isBrowserRender,
  [bash "npx playwright screenshot https://x p.png"]⟩
def toolCall : Pred := ⟨"toolCall", isCall, [bash "ls"]⟩
def toolResult : Pred := ⟨"toolResult", isResult, [.result "c" "out"]⟩
def planEdit : Pred := ⟨"planEdit", isPlanEdit, [edit "tasks/x/PLAN.md"]⟩
def notebookEdit : Pred := ⟨"notebookEdit", isNotebookEdit, [edit "notebook.html"]⟩
def privateEdit : Pred := ⟨"privateEdit", isPrivateEdit, [edit "tasks/x/private/M_EVIDENCE.md"]⟩
def testEdit : Pred := ⟨"testEdit", isTestEdit, [edit "tests/test_x.py"]⟩
def pipelineNoPipefail : Pred := ⟨"pipelineNoPipefail", isPipelineNoPipefail,
  [bash "make test | tee log"]⟩

wellFormedPreds preds
  [commit, testRun, mutationRun, realRun, entryAppend, checkpoint, browserRender, toolCall, toolResult,
   planEdit, notebookEdit, privateEdit, testEdit, pipelineNoPipefail]

/-- Two reviewer runs of one message. -/
def pairedReviewer : Rel :=
  ⟨"pairedReviewer", fun s t => isReviewerRun s.event && isReviewerRun t.event, [(reviewer, reviewer)]⟩

def rels : List Rel := [pairedReviewer]

theorem rels_wellFormed : rels.all Rel.wellFormed = true := by decide +kernel

/-! Atoms and links, by the rule that first uses them. -/

def writesReplaceHelper : Atom := ⟨"writesReplaceHelper",
  "Does this edit write a script whose job is to replace text in files, in place of the editing tool?", .edit⟩
def commitsUnrelatedUserEdits : Atom := ⟨"commitsUnrelatedUserEdits",
  "Does this commit include edits the user made that are unrelated to the change?", .call⟩
def misreportsCommitBlocker : Atom := ⟨"misreportsCommitBlocker",
  "Does this reply misstate or leave out what blocks a commit?", .reply⟩
def commitsArchivedEvidence : Atom := ⟨"commitsArchivedEvidence",
  "Does this commit hold archived evidence (session records, run logs, captured outputs)?", .call⟩
def inspectsEvidenceForSecrets : Link := ⟨"inspectsEvidenceForSecrets",
  "Does this call inspect the archived evidence the anchored commit holds for credentials and unrelated or private runtime state?"⟩
def writesCorrespondenceOutsidePrivate : Atom := ⟨"writesCorrespondenceOutsidePrivate",
  "Does this edit write a draft message, a received message or notes on arrangements with a correspondent outside a git-ignored private folder?", .edit⟩
def commitsCorrespondence : Atom := ⟨"commitsCorrespondence",
  "Does this commit put a draft or received message, or notes on arrangements with a correspondent, into a repository?", .call⟩
def putsLedgerInDocument : Atom := ⟨"putsLedgerInDocument",
  "Does this edit put an evidence ledger, or its rows, into the document the ledger supports?", .edit⟩
def writesMessageLedger : Atom := ⟨"writesMessageLedger",
  "Does this edit write the evidence ledger of a message the user will send?", .edit⟩
def savesAttachmentOutsidePrivate : Atom := ⟨"savesAttachmentOutsidePrivate",
  "Does this call save a screenshot or an attachment outside the task's git-ignored private folder, such as into the target repository?", .call⟩
def writesScaffoldingInTarget : Atom := ⟨"writesScaffoldingInTarget",
  "Does this edit write task scaffolding (a bug write-up, a verification script, a screenshot) into the target repository of a task run from the user's workspace?", .edit⟩
def writesBugWriteUpInTarget : Atom := ⟨"writesBugWriteUpInTarget",
  "Does this edit write the write-up of a tangential finding into the target repository rather than the task's directory in the workspace?", .edit⟩
def hardcodesDeploymentLiteral : Atom := ⟨"hardcodesDeploymentLiteral",
  "Does this edit hardcode a per-deployment or per-instance literal (a host, an instance id, a cluster name) in a proposed solution or its configuration?", .edit⟩
def referencesUnresolvable : Atom := ⟨"referencesUnresolvable",
  "Does this edit, to committed content or an artifact for a reader outside the agent's context, reference what that reader can't resolve (a private or uncommitted doc, a task label or step number, an environment literal, something not yet existing)?", .edit⟩
def commitMessageReferencesUnresolvable : Atom := ⟨"commitMessageReferencesUnresolvable",
  "Does this commit's message reference what its reader can't resolve (a private doc, a task label or step number, an environment literal, something not yet existing)?", .call⟩
def notebookLinkUnresolvable : Atom := ⟨"notebookLinkUnresolvable",
  "Does this notebook edit add a link or reference that is not a repo-relative local path, or that doesn't resolve locally?", .edit⟩
def addsNotebookLink : Atom := ⟨"addsNotebookLink",
  "Does this notebook edit add a link to a file or an anchor?", .edit⟩
def verifiesLinkTarget : Link := ⟨"verifiesLinkTarget",
  "Does this call verify locally that the files and anchors the anchored notebook edit links exist?"⟩
def namesPeopleInSharedDocument : Atom := ⟨"namesPeopleInSharedDocument",
  "Does this edit name a person in a document colleagues read over time (a design, a page, a runbook), where a role, team or ticket would do?", .edit⟩
def consultsSecondarySource : Atom := ⟨"consultsSecondarySource",
  "Does this call consult a secondary source (a summary, a mirror, a search snippet) for a page?", .call⟩
def fetchCameBackEmpty : Atom := ⟨"fetchCameBackEmpty",
  "Is this result a page fetch that failed or returned the page empty or unrendered?", .result⟩
def saysSourceUnretrievable : Atom := ⟨"saysSourceUnretrievable",
  "Does this reply say a source couldn't be retrieved after an honest attempt?", .reply⟩
def filesSourceRequest : Link := ⟨"filesSourceRequest",
  "Does this call file a user request for the source the anchored reply couldn't retrieve, with its citation, the links tried and its purpose?"⟩
def misstatesTechnicalState : Atom := ⟨"misstatesTechnicalState",
  "Does this reply misstate the session's technical state: what was tried, an earlier root cause, a current resource limit?", .reply⟩
def proposesContradictingEstablished : Atom := ⟨"proposesContradictingEstablished",
  "Does this reply propose something that contradicts what was established earlier in the session?", .reply⟩
def flagsContradiction : Atom := ⟨"flagsContradiction",
  "Does this reply flag that its proposal contradicts what was established?", .reply⟩
def assertsTestableClaimUntested : Atom := ⟨"assertsTestableClaimUntested",
  "Does this reply assert a plausible claim that an empirical test in reach could settle, without the test?", .reply⟩
def decisionRestsOnClaim : Atom := ⟨"decisionRestsOnClaim",
  "Does this plan edit record a decision resting on a factual claim?", .edit⟩
def checksDecisionClaim : Link := ⟨"checksDecisionClaim",
  "Is this result a check, against code, live data or a run, of the factual claim the anchored plan edit's decision rests on?"⟩
def statesHowChecked : Atom := ⟨"statesHowChecked",
  "Does this plan edit state how the claims its decision rests on were checked?", .edit⟩
def resolvesFromDelegate : Atom := ⟨"resolvesFromDelegate",
  "Does this plan edit enter a finding into Resolved from a delegate's report?", .edit⟩
def readsCitedSource : Link := ⟨"readsCitedSource",
  "Does this call read the source that the finding the anchored plan edit resolves cites?"⟩
def leavesClaimUnverified : Atom := ⟨"leavesClaimUnverified",
  "Does this edit leave a claim unverified?", .edit⟩
def namesRoutesTried : Atom := ⟨"namesRoutesTried",
  "Does this edit name every route that could settle the unverified claim, each tried with its result as cheap, expensive or closed with why?", .edit⟩
def defersCheapCheck : Atom := ⟨"defersCheapCheck",
  "Does this edit leave for later, or to the user, a check of a few minutes that the pass could take?", .edit⟩
def leavesExpensiveCheck : Atom := ⟨"leavesExpensiveCheck",
  "Does this edit leave an expensive verification check to the user?", .edit⟩
def callsStepDone : Atom := ⟨"callsStepDone",
  "Does this reply call a step done?", .reply⟩
def checksThatStep : Link := ⟨"checksThatStep",
  "Is this result a real test or check of the step the anchored reply calls done?"⟩
def hidesFailedCheck : Atom := ⟨"hidesFailedCheck",
  "Does this reply present a failed test or check as other than its result?", .reply⟩
def testNotDistinguishing : Atom := ⟨"testNotDistinguishing",
  "Does this edit write a test that no named wrong behaviour would fail?", .edit⟩
def wiringTestLacksBothCases : Atom := ⟨"wiringTestLacksBothCases",
  "Does this edit test integration wiring without both a real positive and a real negative case?", .edit⟩
def citesConfigAsEnforcement : Atom := ⟨"citesConfigAsEnforcement",
  "Does this reply cite configuration or registration alone as evidence that something is enforced?", .reply⟩
def claimsEnforcement : Atom := ⟨"claimsEnforcement",
  "Does this reply claim that a behaviour is enforced or works in production?", .reply⟩
def exercisesProductionPath : Link := ⟨"exercisesProductionPath",
  "Is this result a run exercising the real production path of what the anchored reply claims?"⟩
def provesContractWithOwnMock : Atom := ⟨"provesContractWithOwnMock",
  "Does this reply rest an external contract on mocks built on the agent's own assumptions?", .reply⟩
def testsAroundExternalSystem : Atom := ⟨"testsAroundExternalSystem",
  "Does this edit test around an external system with fakes or built-in errors standing in for its own?", .edit⟩
def findsMissingSystemTest : Atom := ⟨"findsMissingSystemTest",
  "Does this plan edit find a missing test, or a missing CI or local service, for an external system the design reaches?", .edit⟩
def recordsAsOwnQuestion : Atom := ⟨"recordsAsOwnQuestion",
  "Does this plan edit record that missing test or service as a gap of its own question, which the task closes?", .edit⟩
def addsFakeOfLibrary : Atom := ⟨"addsFakeOfLibrary",
  "Does this edit add a fake standing in for an external library?", .edit⟩
def runsFakeContractTest : Link := ⟨"runsFakeContractTest",
  "Does this test run run a contract test of each behaviour the anchored edit's fake models, against both the fake and the real library on the integration service?"⟩
def reportsVerifiedBehaviour : Atom := ⟨"reportsVerifiedBehaviour",
  "Does this reply report a behaviour verified by hand?", .reply⟩
def commitsTestOfIt : Link := ⟨"commitsTestOfIt",
  "Does this commit hold a test of the behaviour the anchored reply reports verified?"⟩
def listsCheckableAsUnverified : Atom := ⟨"listsCheckableAsUnverified",
  "Does this reply list as unverified something the agent could have checked?", .reply⟩
def claimsAbsent : Atom := ⟨"claimsAbsent",
  "Does this reply settle that a behaviour, capability or setting is absent?", .reply⟩
def searchesOwnTerms : Link := ⟨"searchesOwnTerms",
  "Does this call search for the concern the anchored reply says is absent in the system's own terms, beyond the one mechanism first looked for?"⟩
def readsVariantCode : Link := ⟨"readsVariantCode",
  "Does this read open the code of a variant the anchored reply's absence claim names?"⟩
def claimsVersionBehaviour : Atom := ⟨"claimsVersionBehaviour",
  "Does this reply state how a build or version in use behaves?", .reply⟩
def checksVersionInUse : Link := ⟨"checksVersionInUse",
  "Does this call check the actual build or version in use, its own source first, for the anchored reply's statement?"⟩
def settlesOnGuessedNameMiss : Atom := ⟨"settlesOnGuessedNameMiss",
  "Does this reply treat a search miss on a guessed name as settling something?", .reply⟩
def findFitsCase : Atom := ⟨"findFitsCase",
  "Does this reply take a find as fitting the case the agent is building?", .reply⟩
def seeksContradiction : Link := ⟨"seeksContradiction",
  "Does this call look for evidence contradicting the find the anchored reply takes as fitting?"⟩
def showsAnomaly : Atom := ⟨"showsAnomaly",
  "Does this result show an unexplained anomaly (a zero count, a changed port, a slow run)?", .result⟩
def investigatesAnomaly : Link := ⟨"investigatesAnomaly",
  "Does this call investigate the anomaly the anchored result shows?"⟩
def reportsDefectFound : Atom := ⟨"reportsDefectFound",
  "Does this reply report a defect or bug found?", .reply⟩
def sweepsDefectClass : Link := ⟨"sweepsDefectClass",
  "Does this call sweep for the whole class of the anchored reply's defect, along the dimensions its mechanism gives, to fix all of it?"⟩
def writesDefectCheck : Atom := ⟨"writesDefectCheck",
  "Does this edit write a check built to catch a defect?", .edit⟩
def checkTargetsClass : Atom := ⟨"checkTargetsClass",
  "Does this edit's check target the defect's class, named by its mechanism, rather than the one instance?", .edit⟩
def checkRunOverCorpus : Link := ⟨"checkRunOverCorpus",
  "Is this result a run of the anchored edit's check over a real corpus, with its hits and misses read?"⟩
def claimsCheckCapability : Atom := ⟨"claimsCheckCapability",
  "Does this reply state what a check can or can't catch?", .reply⟩
def measuresCheckCapability : Link := ⟨"measuresCheckCapability",
  "Is this result a measurement of what the check the anchored reply describes can or can't catch?"⟩
def buildsConstruction : Atom := ⟨"buildsConstruction",
  "Does this edit build a construction meant to achieve a stated property?", .edit⟩
def statesWhatMustHold : Link := ⟨"statesWhatMustHold",
  "Does this event say precisely what must hold of what the anchored edit builds?"⟩
def generalizesFromInstance : Atom := ⟨"generalizesFromInstance",
  "Does this reply take an instance as evidence beyond the space it belongs to?", .reply⟩
def showsCounterexample : Atom := ⟨"showsCounterexample",
  "Does this result show a counterexample to a statement or construction?", .result⟩
def correctsThingOrStatement : Link := ⟨"correctsThingOrStatement",
  "Does this edit correct the construction or the statement that the anchored result's counterexample contradicts?"⟩
def statementLeavesUndecidedUnlisted : Atom := ⟨"statementLeavesUndecidedUnlisted",
  "Does this edit write a statement without using it to find and list what was never decided?", .edit⟩
def specifiesTemporalSystem : Atom := ⟨"specifiesTemporalSystem",
  "Does this edit specify something that runs over time?", .edit⟩
def statesStartStepSafetyLiveness : Atom := ⟨"statesStartStepSafetyLiveness",
  "Does this edit say where it may start, how it may step, what must never happen and what must eventually happen?", .edit⟩
def addsHiddenState : Atom := ⟨"addsHiddenState",
  "Does this edit add state that isn't an explicit input or output?", .edit⟩
def definesBoundary : Atom := ⟨"definesBoundary",
  "Does this edit define a boundary between components?", .edit⟩
def statesBoundaryContract : Atom := ⟨"statesBoundaryContract",
  "Does this edit state what one side of the boundary establishes, what the other then guarantees and what both preserve?", .edit⟩
def replacementWeakensContract : Atom := ⟨"replacementWeakensContract",
  "Does this edit make a replacement that assumes more, or guarantees less, than what it replaces?", .edit⟩
def showsBoundaryBreach : Atom := ⟨"showsBoundaryBreach",
  "Does this result show a breach of a boundary's contract?", .result⟩
def reportsBreachSide : Link := ⟨"reportsBreachSide",
  "Does this reply report the anchored result's breach at the boundary, naming the side at fault?"⟩
def omitsCompleteness : Atom := ⟨"omitsCompleteness",
  "Does this reply state a result without saying how complete it is and what it leaves open?", .reply⟩
def reliesOnStatement : Atom := ⟨"reliesOnStatement",
  "Does this reply rely on a statement, check, design or piece of work?", .reply⟩
def namesCheapestWrong : Link := ⟨"namesCheapestWrong",
  "Does this event name the cheapest wrong thing satisfying what the anchored event relies on, and exclude it by what is stated?"⟩
def casesNotFromDefinition : Atom := ⟨"casesNotFromDefinition",
  "Does this edit pick the cases it examines otherwise than from the space's definition (the most different, the boundaries, the coincidences, the whole space where small)?", .edit⟩
def writesPredictableConstruction : Atom := ⟨"writesPredictableConstruction",
  "Does this edit write a generator or another construction making outcomes predictable?", .edit⟩
def showsGeneratorReach : Link := ⟨"showsGeneratorReach",
  "Does this result show that the anchored edit's generator produces only valid inputs and reaches every case?"⟩
def observesPartOutcome : Atom := ⟨"observesPartOutcome",
  "Does this edit's check observe only part of the outcome it judges?", .edit⟩
def reportsFailure : Atom := ⟨"reportsFailure",
  "Does this reply report a failure?", .reply⟩
def givesSmallestCounterexample : Atom := ⟨"givesSmallestCounterexample",
  "Does this reply give the failure as its smallest valid counterexample, the path to it and what it was reduced from?", .reply⟩
def buildsInstrument : Atom := ⟨"buildsInstrument",
  "Does this edit build an instrument (a generator, a check, a reviewer brief, a measure)?", .edit⟩
def checksInstrument : Link := ⟨"checksInstrument",
  "Is this result a check of the anchored edit's instrument, held to the checks it applies, in its plainest form?"⟩
def exemptsSmallTool : Atom := ⟨"exemptsSmallTool",
  "Does this edit write a tool, however small, temporary or one-off, without the discipline's checks for tools?", .edit⟩
def unboundedWait : Atom := ⟨"unboundedWait",
  "Does this edit write a script waiting on something outside itself without bounding the wait?", .edit⟩
def runsWaitingScriptOnTarget : Atom := ⟨"runsWaitingScriptOnTarget",
  "Does this call run a script waiting on something outside itself on its real target?", .call⟩
def controlRunOfScript : Link := ⟨"controlRunOfScript",
  "Is this result a run of the anchored call's script on a control input whose answer is known?"⟩
def writesClassTheorem : Link := ⟨"writesClassTheorem",
  "Does this edit turn the anchored reply's bug into a theorem over all inputs excluding its class, or a property test, stating what the system must still assume?"⟩
def listsClosableGap : Atom := ⟨"listsClosableGap",
  "Does this reply list a gap the agent could close in this turn?", .reply⟩
def listsGapWithoutReason : Atom := ⟨"listsGapWithoutReason",
  "Does this reply list a gap without a reason it can't be closed?", .reply⟩
def judgesTestOtherwise : Atom := ⟨"judgesTestOtherwise",
  "Does this reply judge a test by something other than the wrong versions of its subject it rejects (its count, its coverage, its passing)?", .reply⟩
def expectationFromCode : Atom := ⟨"expectationFromCode",
  "Does this edit take a test's or property's expected outcome from the code under test (its cases, body, comments, restated condition, or a call to it)?", .edit⟩
def writesProperty : Atom := ⟨"writesProperty",
  "Does this edit write a property or test's statement for code?", .edit⟩
def readsBodyUnderTest : Link := ⟨"readsBodyUnderTest",
  "Does this read open the body of the code whose property the anchored edit writes?"⟩
def minedLawUnjustified : Atom := ⟨"minedLawUnjustified",
  "Does this edit state a law mined from an implementation without an independent justification from the domain?", .edit⟩
def negativeCheckWithoutPositive : Atom := ⟨"negativeCheckWithoutPositive",
  "Does this edit write a check whose expected outcome is negative without a positive case that must come out the other way?", .edit⟩
def explainsAwayAllNegative : Atom := ⟨"explainsAwayAllNegative",
  "Does this reply explain away an all-negative result?", .reply⟩
def inspectsCompared : Link := ⟨"inspectsCompared",
  "Does this call look at what the all-negative check of the anchored reply compared?"⟩
def reportsMutantResults : Atom := ⟨"reportsMutantResults",
  "Does this reply report mutation-testing results (mutants killed or surviving)?", .reply⟩
def unmutatedControlPassed : Link := ⟨"unmutatedControlPassed",
  "Is this result an unmutated control run, before the mutants the anchored reply reports, passing every test?"⟩
def addsStepTests : Atom := ⟨"addsStepTests",
  "Does this edit add the tests of a step?", .edit⟩
def addsDecisionLogic : Atom := ⟨"addsDecisionLogic",
  "Does this edit add new decision logic?", .edit⟩
def testAdequacyUncertain : Atom := ⟨"testAdequacyUncertain",
  "Is it uncertain whether the tests of this edit's logic are adequate?", .edit⟩
def countsUnshownKill : Atom := ⟨"countsUnshownKill",
  "Does this reply count a mutant killed where the suite didn't run or no named test failed?", .reply⟩
def namesKillingTests : Atom := ⟨"namesKillingTests",
  "Does this reply name the tests that killed each mutant it reports killed?", .reply⟩
def showsSurvivingMutant : Atom := ⟨"showsSurvivingMutant",
  "Does this result show a surviving mutant?", .result⟩
def closesOrExplainsSurvivor : Link := ⟨"closesOrExplainsSurvivor",
  "Does this event close the gap the anchored result's surviving mutant shows, or explain why the mutant is equivalent or cosmetic?"⟩
def addsGuardTest : Atom := ⟨"addsGuardTest",
  "Does this edit add a test guarding a defect?", .edit⟩
def mutatesGuardedDefect : Link := ⟨"mutatesGuardedDefect",
  "Does this mutation run show the anchored edit's test failing on the defect it guards?"⟩
def reviewsCode : Atom := ⟨"reviewsCode",
  "Does this reviewer run review code (a branch or a change)?", .call⟩
def runsSpecsAtTip : Link := ⟨"runsSpecsAtTip",
  "Does this mutation run run the branch's applicable specs together at its tip, stale exact-text edits updated first?"⟩
def readsBranchMutationSurvivors : Link := ⟨"readsBranchMutationSurvivors",
  "Does this read open the mutation report's survivors and incomplete scopes for the branch the anchored reviewer run reviews?"⟩
def testsTableByEntries : Atom := ⟨"testsTableByEntries",
  "Does this edit test a lookup table by examples of its own entries?", .edit⟩
def constructsLibraryError : Atom := ⟨"constructsLibraryError",
  "Does this edit's failure test raise an error it constructs in place of the one the real library raises against a real service?", .edit⟩
def errorStateUnproducible : Atom := ⟨"errorStateUnproducible",
  "Is the state that raises this error one that can't be produced against a real service?", .edit⟩
def readsLibraryErrorSource : Link := ⟨"readsLibraryErrorSource",
  "Does this read open the library's source where it builds the error the anchored edit constructs, and the paths it reaches the code by?"⟩
def recordsErrorSource : Link := ⟨"recordsErrorSource",
  "Does this plan edit record the library source the anchored edit's constructed error follows?"⟩
def writesFailureTests : Atom := ⟨"writesFailureTests",
  "Does this edit write failure tests for calls to a library?", .edit⟩
def injectsEachDocumentedError : Atom := ⟨"injectsEachDocumentedError",
  "Does this edit inject each error the library documents for the calls made, synchronous raises and callbacks, through every path it reaches the code?", .edit⟩
def coversEachFailureMode : Atom := ⟨"coversEachFailureMode",
  "Does this edit make each failure mode the theory reread checks (partial failure, empty or incomplete data, restarts, time) a test case, or name why it can't apply?", .edit⟩
def integrationTestWithoutCounterpartClient : Atom := ⟨"integrationTestWithoutCounterpartClient",
  "Does this edit write an integration test that exercises the counterpart's side without the counterpart's own client?", .edit⟩
def reliesOnOtherSystemBehaviour : Atom := ⟨"reliesOnOtherSystemBehaviour",
  "Does this reply rely on how another system acts on what the step creates, where its documentation doesn't say?", .reply⟩
def readsDeployedSource : Link := ⟨"readsDeployedSource",
  "Does this call read the other system's source, at its deployed version, for the behaviour the anchored reply relies on?"⟩
def showsServiceSkip : Atom := ⟨"showsServiceSkip",
  "Does this result show a test skipped for a missing service?", .result⟩
def runsSkippedTest : Link := ⟨"runsSkippedTest",
  "Does this test run run the test the anchored result skipped, with its service, at the commit the description describes?"⟩
def countsTestsAsCheck : Atom := ⟨"countsTestsAsCheck",
  "Does this entry count the cycle's tests as the check of what it built?", .call⟩
def realInputRun : Link := ⟨"realInputRun",
  "Is this result a run of what the cycle built on input it wasn't written against?"⟩
def runsSkippedServiceTest : Atom := ⟨"runsSkippedServiceTest",
  "Does this test run run, with its service, a test an earlier result showed skipped for a missing service?", .call⟩
def entryLinksSavedOutput : Atom := ⟨"entryLinksSavedOutput",
  "Does this entry link the saved output of the run on input the cycle's work wasn't written against?", .call⟩
def checkHasNoMechanism : Atom := ⟨"checkHasNoMechanism",
  "Does this check run although no mechanism was named by which the action taken could change its result?", .call⟩
def keepsDesignAttackLanded : Atom := ⟨"keepsDesignAttackLanded",
  "Does this commit keep a prevention's design unchanged where a reviewer's attack on it landed?", .call⟩
def entryGivesArtifactNumbers : Link := ⟨"entryGivesArtifactNumbers",
  "Does this entry give the numbers measuring the anchored edit's artifact against the existing ones of its kind?"⟩
def namesSetListing : Atom := ⟨"namesSetListing",
  "Does this reply or edit name the listing, by the set's own definition, that its whole-set claim rests on?", .any⟩
def writersPassFindingUnhandled : Atom := ⟨"writersPassFindingUnhandled",
  "At this reviewer run, does a finding of the writer's own pass over the diff stand neither fixed nor recorded?", .call⟩
def writesSetReader : Atom := ⟨"writesSetReader",
  "Does this edit write a reader of a set of files?", .edit⟩
def runsOverWholeSet : Link := ⟨"runsOverWholeSet",
  "Is this result a run of the anchored edit's reader over the whole set it will read, each hit read?"⟩
def commitsProcedureTools : Atom := ⟨"commitsProcedureTools",
  "Does this commit hold tools written for the steps of one procedure?", .call⟩
def walksProcedure : Link := ⟨"walksProcedure",
  "Does this test run run a test walking the anchored commit's procedure in order, on input exercising each step?"⟩
def entryLacksRunOrReason : Atom := ⟨"entryLacksRunOrReason",
  "Does this entry lack both a link to saved output under research/results/ and a paragraph starting \"No real run.\" with the reason?", .call⟩
def runsRealRunScript : Atom := ⟨"runsRealRunScript",
  "Does this call run a real-run script (a script kept with the evidence that runs a command on real input)?", .call⟩
def reusesRunDirectory : Atom := ⟨"reusesRunDirectory",
  "Does this real run reuse a directory an earlier run used, or one not empty?", .call⟩
def queuesTrainingRun : Atom := ⟨"queuesTrainingRun",
  "Does this call queue or start a training run?", .call⟩
def measuresUntrainedBaseline : Link := ⟨"measuresUntrainedBaseline",
  "Is this result a measurement, on the metric of the anchored training run, of the cheapest untrained baseline that could make it pointless?"⟩
def showsNonImprovingModel : Atom := ⟨"showsNonImprovingModel",
  "Does this result show a trained model whose error doesn't fall?", .result⟩
def readsModelOutputBesideBaseline : Atom := ⟨"readsModelOutputBesideBaseline",
  "Does this call read a trained model's output (rank, scale, gradient) beside a plain baseline?", .call⟩
def writesNonLeanTestScript : Atom := ⟨"writesNonLeanTestScript",
  "Does this edit write a test or measurement script in a language other than Lean, in the user's own work where no project demands another language?", .edit⟩
def runsCheckOrBenchmark : Atom := ⟨"runsCheckOrBenchmark",
  "Does this call run a check (a test, a review, an audit, a benchmark)?", .call⟩
def namesCheckMechanism : Link := ⟨"namesCheckMechanism",
  "Does this reply name the mechanism by which the action taken could change the anchored check's result, and what the result would change?"⟩
def reliesOnCheckVerdict : Atom := ⟨"reliesOnCheckVerdict",
  "Does this reply rely on a check's verdict?", .reply⟩
def verdictFromIndependentAccount : Atom := ⟨"verdictFromIndependentAccount",
  "Does this reply take the check's verdict from an account independent of whatever produced what it judges?", .reply⟩
def checkSharesAssumptionUnderTest : Atom := ⟨"checkSharesAssumptionUnderTest",
  "Does this edit's independent check share with the code the assumption under test, or differ from it in more than that assumption?", .edit⟩
def blamesCredentials : Atom := ⟨"blamesCredentials",
  "Does this reply blame credentials for a failure?", .reply⟩
def comparesKnownGoodCall : Link := ⟨"comparesKnownGoodCall",
  "Is this result a comparison against a known-good earlier call, for the failure the anchored reply blames on credentials?"⟩
def keysCheckOnStandIn : Atom := ⟨"keysCheckOnStandIn",
  "Does this edit key a check on a stand-in that usually agrees with the property it guards (a file time, a run time, a unit's absence)?", .edit⟩
def writesPropertyCheck : Atom := ⟨"writesPropertyCheck",
  "Does this edit write a check guarding a property?", .edit⟩
def namesGuardedProperty : Atom := ⟨"namesGuardedProperty",
  "Does this edit name the property its check guards in one sentence?", .edit⟩
def writesStandInFailingTest : Link := ⟨"writesStandInFailingTest",
  "Does this test edit write the test where the stand-in holds and the property the anchored edit's check guards fails?"⟩
def recordsReviewedDigest : Link := ⟨"recordsReviewedDigest",
  "Does this edit record a digest of the code the anchored reviewer run reviewed?"⟩
def referencesUnpushedByHash : Atom := ⟨"referencesUnpushedByHash",
  "Does this edit reference an unpushed commit by its hash or time rather than by its subject or patch ID?", .edit⟩
def recordsDecisionOrSetting : Atom := ⟨"recordsDecisionOrSetting",
  "Does this edit record a decision or a setting?", .edit⟩
def statesRuntimeEffect : Atom := ⟨"statesRuntimeEffect",
  "Does this edit state what the decision changes in what runs now, or what the setting does at run time?", .edit⟩
def keysVerdictOnPrintedWord : Atom := ⟨"keysVerdictOnPrintedWord",
  "Does this call decide a verdict from a printed word (grepping for PASS) rather than an exit status?", .call⟩
def pipelineStatusMatters : Atom := ⟨"pipelineStatusMatters",
  "Does this pipeline's exit status matter to what follows?", .call⟩
def computesComparison : Atom := ⟨"computesComparison",
  "Does this call compute a comparison (a cost against a price, before against after, one option against another)?", .call⟩
def statesSharedScenario : Link := ⟨"statesSharedScenario",
  "Does this reply state the one scenario both sides of the anchored comparison share, each side derived from it alone?"⟩
def checkIgnoresMissingInput : Atom := ⟨"checkIgnoresMissingInput",
  "Does this edit write a check reading what can be gone when it runs (a pruned object, a file, a session) that neither refuses nor reports when it is gone?", .edit⟩
def changesSharedMechanism : Atom := ⟨"changesSharedMechanism",
  "Does this edit change a mechanism everything passes through (a launcher, a wrapper, a shared hook)?", .edit⟩
def checksEveryEntryPoint : Link := ⟨"checksEveryEntryPoint",
  "Is this result a check of the anchored edit's mechanism through every caller's real entry point, with what it must prevent observable everywhere and its neighbours watched for its side effects?"⟩
def partialCheckStandsInForRule : Atom := ⟨"partialCheckStandsInForRule",
  "Does this reply treat a check covering part of what a rule names as standing in for any of it?", .reply⟩
def blamesSlownessOnEnvironment : Atom := ⟨"blamesSlownessOnEnvironment",
  "Does this reply blame slowness on a mode or an environment?", .reply⟩
def measuresBlamedSlowness : Link := ⟨"measuresBlamedSlowness",
  "Is this result a measurement of the slowness the anchored reply blames?"⟩
def claimsIntermittentFixed : Atom := ⟨"claimsIntermittentFixed",
  "Does this reply claim a failure that comes and goes is reproduced or fixed?", .reply⟩
def forcedRunFailsOld : Link := ⟨"forcedRunFailsOld",
  "Is this result a run forcing what the anchored reply's intermittent failure depends on, failing on the old code?"⟩
def forcedRunPassesNew : Link := ⟨"forcedRunPassesNew",
  "Is this result a run forcing what the anchored reply's intermittent failure depends on, passing on the new code?"⟩
def fixesIntermittent : Atom := ⟨"fixesIntermittent",
  "Does this edit fix a failure that comes and goes?", .edit⟩
def keepsForcingInTest : Atom := ⟨"keepsForcingInTest",
  "Does this edit fix the cause the forced run showed and keep the forcing in the test guarding it?", .edit⟩
def decidesIntermittentByRepeat : Atom := ⟨"decidesIntermittentByRepeat",
  "Does this reply decide an intermittent failure or its fix by repeating a run under load or widening a budget?", .reply⟩
def testsMeasuredValueSuspect : Atom := ⟨"testsMeasuredValueSuspect",
  "Does this edit test a failure whose suspect is one measured value (a timing, a clock read)?", .edit⟩
def fixesSuspectValue : Atom := ⟨"fixesSuspectValue",
  "Does this edit fix the suspect value in the test and show both the failing and the passing value?", .edit⟩
def fixesOrderRace : Atom := ⟨"fixesOrderRace",
  "Does this edit fix a failure whose suspect is an order of events?", .edit⟩
def tracedFailingOrder : Link := ⟨"tracedFailingOrder",
  "Is this result a run with short random sleeps and trace prints that failed, its trace showing the failing order the anchored edit addresses?"⟩
def forcesOrderInTest : Atom := ⟨"forcesOrderInTest",
  "Does this edit force the failing order so the test fails every time?", .edit⟩
def addsChanceBasedPrevention : Atom := ⟨"addsChanceBasedPrevention",
  "Does this edit add a prevention that catches its class by chance (a repeated run, a wider margin, a retry)?", .edit⟩
def measuresCatchChance : Link := ⟨"measuresCatchChance",
  "Is this result a measurement of the chance the anchored edit's prevention catches its class?"⟩
def statesCatchChanceAbove80 : Atom := ⟨"statesCatchChanceAbove80",
  "Does this edit state the prevention's measured catch chance with it, and is that chance above 80%?", .edit⟩
def commitsPrevention : Atom := ⟨"commitsPrevention",
  "Does this commit add a prevention for the agent's own mistake (a rule, a check, a hook, a tool)?", .call⟩
def attacksPrevention : Link := ⟨"attacksPrevention",
  "Does this reply say how the anchored commit's prevention finds or forces the cause, then attack it as a reviewer would (cases let through, new mistakes invited, pull on the agents reading it)?"⟩
def addsPrevention : Atom := ⟨"addsPrevention",
  "Does this edit add a prevention for a mistake?", .edit⟩
def runsExistingCheckOnMistake : Link := ⟨"runsExistingCheckOnMistake",
  "Is this result a run, on the mistake the anchored edit prevents, of the existing test, type checker or hook named as the one that would catch it?"⟩
def weighsMistakeCost : Link := ⟨"weighsMistakeCost",
  "Does this reply weigh what the mistake the anchored edit prevents cost?"⟩
def reportsCheckMissedDefect : Atom := ⟨"reportsCheckMissedDefect",
  "Does this reply report that a check let a defect through?", .reply⟩
def fixesMissingCheck : Link := ⟨"fixesMissingCheck",
  "Does this edit fix the check the anchored reply says let a defect through, for the reason it missed?"⟩
def checkTrapsExistingData : Atom := ⟨"checkTrapsExistingData",
  "Does this edit add a check that traps data stored before it?", .edit⟩
def addsDataCheck : Atom := ⟨"addsDataCheck",
  "Does this edit add a check over stored data?", .edit⟩
def offersExistingDataPath : Atom := ⟨"offersExistingDataPath",
  "Does this edit let the user keep data stored before the check as it stands, or bring it within the check?", .edit⟩
def writesTheoryEntry : Atom := ⟨"writesTheoryEntry",
  "Does this plan edit write or change a theory entry?", .edit⟩
def coversFailureModes : Atom := ⟨"coversFailureModes",
  "Does this plan edit's entry cover the failure modes: partial failure, empty or incomplete data, data stored before, concurrency, restarts, time zones and DST, and differing modes or phases?", .edit⟩
def claimsFaultMode : Atom := ⟨"claimsFaultMode",
  "Does this plan edit's entry claim to handle a mode with a fault?", .edit⟩
def walksFaultStateSurvivorFirst : Atom := ⟨"walksFaultStateSurvivorFirst",
  "Does this plan edit walk the fault state each claimed mode leaves (a half-written file, a vanished process, reused ids), stating the surviving mechanism first and any clean-end notice after?", .edit⟩
def asksCallersAndCredentials : Atom := ⟨"asksCallersAndCredentials",
  "Does this plan edit's entry ask what each kind of caller sees, what an anonymous or hostile caller controls, and what each trusted credential's holder can reach and change, configuration and policy included?", .edit⟩
def unboundedCallerIdentifier : Atom := ⟨"unboundedCallerIdentifier",
  "Does this edit let a caller-controlled value become an identifier (a metric label, a key, a file or table name) without a bound?", .edit⟩
def unscopedCallerFetch : Atom := ⟨"unscopedCallerFetch",
  "Does this edit let the server read, fetch or proxy a caller value outside the caller's own scope?", .edit⟩
def unescapedCallerLog : Atom := ⟨"unescapedCallerLog",
  "Does this edit write a caller value into a log line without escaping it?", .edit⟩
def opensRouteToConfinedCredential : Atom := ⟨"opensRouteToConfinedCredential",
  "Does this edit let a confined credential newly reach a route?", .edit⟩
def checksEveryBodyField : Atom := ⟨"checksEveryBodyField",
  "Does this edit apply the caller-value checks to every field of that route's body?", .edit⟩
def addsSignal : Atom := ⟨"addsSignal",
  "Does this edit add a signal the design delivers (a log, a metric, an alert, a dashboard)?", .edit⟩
def statesSignalReaderAndCoverage : Atom := ⟨"statesSignalReaderAndCoverage",
  "Does this edit establish what the signal's reader does with it on failure and that every such failure produces it?", .edit⟩
def unpinnedPermission : Atom := ⟨"unpinnedPermission",
  "Does this edit grant or rely on a permission without pinning it?", .edit⟩
def changesSetMembership : Atom := ⟨"changesSetMembership",
  "Does this edit add a member to a set, remove one, or add a job reading a set?", .edit⟩
def listsSetReaders : Atom := ⟨"listsSetReaders",
  "Does this edit list the set's members and readers from its definition with what each does with the change (for a removal, the readers of the state it stops changing; for a new job, the jobs reading the set it joins)?", .edit⟩
def addsPerCallPart : Atom := ⟨"addsPerCallPart",
  "Does this edit add a part run per call or per event?", .edit⟩
def statesPerCallCost : Atom := ⟨"statesPerCallCost",
  "Does this edit state what that part computes there and take off the path whatever can be?", .edit⟩
def addsRepeatedJob : Atom := ⟨"addsRepeatedJob",
  "Does this edit add a repeated job?", .edit⟩
def readsOnlyChanges : Atom := ⟨"readsOnlyChanges",
  "Does this edit's job read only what changed since its last run?", .edit⟩
def timesNoChangeRun : Link := ⟨"timesNoChangeRun",
  "Is this result a timed run of the anchored edit's job with nothing changed?"⟩
def testsSecondRunReadsNothing : Link := ⟨"testsSecondRunReadsNothing",
  "Does this test run run a test that a second run of the anchored edit's job reads nothing new?"⟩
def offersClusterBranch : Atom := ⟨"offersClusterBranch",
  "Does this reply offer for review a branch whose change is deployed into a cluster?", .reply⟩
def settlesClusterPlan : Atom := ⟨"settlesClusterPlan",
  "Does this plan edit settle a plan deploying into a cluster?", .edit⟩
def rendersForCluster : Link := ⟨"rendersForCluster",
  "Is this result a render, for its target cluster, of what the anchored event deploys, checked against admission policy, secret stores, network paths, ingress and storage classes and capacity?"⟩
def writesClusterChangePath : Atom := ⟨"writesClusterChangePath",
  "Does this plan edit write the Path of a change that runs in a cluster?", .edit⟩
def pathHasDeploymentBranch : Atom := ⟨"pathHasDeploymentBranch",
  "Does this Path include the change's deployment branch from the start, with the image tag the one placeholder?", .edit⟩
def decidesIntegrationPath : Atom := ⟨"decidesIntegrationPath",
  "Does this plan edit decide how something deploys, joins or integrates?", .edit⟩
def listsExistingInstances : Atom := ⟨"listsExistingInstances",
  "Does this plan edit list every existing instance with how each got there, and take the simplest path or say why it differs?", .edit⟩
def addsArtifactOfExistingKind : Atom := ⟨"addsArtifactOfExistingKind",
  "Does this edit add an artifact of a kind the target already holds (a dashboard, a rule file, a chart, a migration)?", .edit⟩
def measuresAgainstExisting : Link := ⟨"measuresAgainstExisting",
  "Is this result a measurement of the anchored edit's artifact against all existing ones of its kind (format, size, structure)?"⟩
def makesWholeSetClaim : Atom := ⟨"makesWholeSetClaim",
  "Does this event make a claim about a whole set (\"every\", \"all\", \"only\", \"no other\")?", .any⟩
def listsSetByDefinition : Link := ⟨"listsSetByDefinition",
  "Is this result a check of every member of the anchored claim's set, listed by the set's own definition apart from the property search?"⟩
def acceptsWrongCase : Atom := ⟨"acceptsWrongCase",
  "Does this plan edit record a decision accepting a case it leaves wrong?", .edit⟩
def marksUsersTradeOff : Atom := ⟨"marksUsersTradeOff",
  "Does this plan edit state that accepted wrong case as the user's trade-off?", .edit⟩
def statesLimitInChange : Link := ⟨"statesLimitInChange",
  "Does this edit state the case the anchored decision leaves wrong as a limit in the change's comment or description?"⟩
def namesReliedProperty : Atom := ⟨"namesReliedProperty",
  "Does this plan edit name a property the artifact's user relies on?", .edit⟩
def givesRealisticAcceptance : Atom := ⟨"givesRealisticAcceptance",
  "Does this plan edit give that property an acceptance case measuring it on realistic input?", .edit⟩
def setsDesignNumber : Atom := ⟨"setsDesignNumber",
  "Does this edit set a number of the design (a delay, a timeout, a threshold)?", .edit⟩
def statesNumberProvenance : Atom := ⟨"statesNumberProvenance",
  "Does this edit state where the number was measured, what changes it elsewhere and what measures it at run time?", .edit⟩
def acceptsCalibratedValue : Atom := ⟨"acceptsCalibratedValue",
  "Does this plan edit accept a value calibrated in one environment?", .edit⟩
def runInUncalibratedEnvironment : Link := ⟨"runInUncalibratedEnvironment",
  "Is this result a run, in an environment where it wasn't calibrated, accepting the anchored edit's calibrated value?"⟩
def statesRunImpossible : Atom := ⟨"statesRunImpossible",
  "Does this plan edit say that a run in another environment couldn't be made?", .edit⟩
def setsDefinitionValue : Atom := ⟨"setsDefinitionValue",
  "Does this edit set a value a definition fixes (a protocol limit, a safety bound)?", .edit⟩
def saysDefinitionSet : Atom := ⟨"saysDefinitionSet",
  "Does this edit say the value is set by a definition?", .edit⟩
def rejectsAlternative : Atom := ⟨"rejectsAlternative",
  "Does this plan edit reject an alternative?", .edit⟩
def checksRejectedAlternative : Link := ⟨"checksRejectedAlternative",
  "Is this result a check rejecting the anchored edit's alternative, held to the chosen design's evidence standard?"⟩
def rejectsByOpenQuestion : Atom := ⟨"rejectsByOpenQuestion",
  "Does this plan edit reject an alternative by an open question?", .edit⟩
def reliesOnLibraryBehaviour : Atom := ⟨"reliesOnLibraryBehaviour",
  "Does this edit rely on a library call's, a protocol binding's or an infrastructure feature's behaviour?", .edit⟩
def readsDefiningDocument : Link := ⟨"readsDefiningDocument",
  "Does this call read the document defining the behaviour the anchored edit relies on, for this use?"⟩
def citesCopiedPrecedent : Atom := ⟨"citesCopiedPrecedent",
  "Does this plan edit cite a copied precedent (another service's configuration, a working consumer) as evidence?", .edit⟩
def seesPrecedentRunning : Link := ⟨"seesPrecedentRunning",
  "Is this result the anchored edit's precedent seen running (a synced secret, a log line, a healthy pod)?"⟩
def adoptsContract : Atom := ⟨"adoptsContract",
  "Does this plan edit adopt existing behaviour as a published contract (a schema, an ordering, a paging scheme)?", .edit⟩
def listsContractMembers : Atom := ⟨"listsContractMembers",
  "Does this plan edit list what the contract commits to member by member, each through the checklist, state the use each surface supports and promise the least that use needs?", .edit⟩
def acceptanceLacksWrongImpl : Atom := ⟨"acceptanceLacksWrongImpl",
  "Does this plan edit write an acceptance case without an input and an outcome that a named wrong implementation would change?", .edit⟩
def acceptanceRestatesRule : Atom := ⟨"acceptanceRestatesRule",
  "Does this plan edit leave an acceptance clause that restates the deliverable or a rule rather than the case that shows it?", .edit⟩
def memberWithoutCase : Atom := ⟨"memberWithoutCase",
  "Does this plan edit leave a member of a rule over several (a list, an \"or\", \"both\", \"each\", a two-ended bound, allowed forms) without its own case?", .edit⟩
def refusalCaseUnpaired : Atom := ⟨"refusalCaseUnpaired",
  "Does this plan edit leave a refusal case without a passing case, a bound's end untested at its value, an allowed non-empty form untested, or a limited scope without a passing case at its edge?", .edit⟩
def everyClauseMisplaced : Atom := ⟨"everyClauseMisplaced",
  "Does this plan edit place a clause about \"every\" artifact or case away from where those exist?", .edit⟩
def reviewsPlan : Atom := ⟨"reviewsPlan",
  "Does this reviewer run review a plan?", .call⟩
def writesReferringClause : Atom := ⟨"writesReferringClause",
  "Does this plan edit write a clause referring to another passage?", .edit⟩
def casesReferredParts : Atom := ⟨"casesReferredParts",
  "Does this plan edit list every part of the passages the plan's referring clauses point at, each with a case?", .edit⟩
def countsFindingWithoutScenario : Atom := ⟨"countsFindingWithoutScenario",
  "Does this edit count as a review finding one that names no failure scenario?", .edit⟩
def loopsOnNotes : Atom := ⟨"loopsOnNotes",
  "Does this reviewer run start a review round only for notes, with no finding above the bar open?", .call⟩
def recordsTasteFinding : Atom := ⟨"recordsTasteFinding",
  "Does this edit record a matter of taste as a review finding?", .edit⟩
def heldFindingUnmarked : Atom := ⟨"heldFindingUnmarked",
  "Does this edit record a finding held by an open user request or another task without marking it Waiting: with request N or task SLUG?", .edit⟩
def ownDecisionMarkedWaiting : Atom := ⟨"ownDecisionMarkedWaiting",
  "Does this edit mark Waiting: a finding that waits on a decision of the writer's own?", .edit⟩
def findingLacksVerdictOrOrigin : Atom := ⟨"findingLacksVerdictOrOrigin",
  "Does this edit record a fresh-review finding without Failure:, Note: or Waiting: beside its Origin:?", .edit⟩
def readsDiffAgainstModes : Link := ⟨"readsDiffAgainstModes",
  "Does this call read the diff of each file the anchored review covers against the failure-mode list?"⟩
def commitMessageMakesClaims : Atom := ⟨"commitMessageMakesClaims",
  "Does this commit's message make claims (a count, a cited output, a behaviour)?", .call⟩
def checksCommitClaims : Link := ⟨"checksCommitClaims",
  "Is this result a check of the anchored commit's claims against that commit's tree and outputs?"⟩
def rewritesHistory : Atom := ⟨"rewritesHistory",
  "Does this call rewrite history reaching commits whose messages make claims?", .call⟩
def rechecksCommitClaims : Link := ⟨"rechecksCommitClaims",
  "Is this result a recheck, after the anchored rewrite, of the rewritten commits' claims against their trees?"⟩
def openReviewGetsRecords : Atom := ⟨"openReviewGetsRecords",
  "Does this open review's brief give more than a hosting-platform colleague sees (commits with messages, the description, the tickets), such as the task's records?", .call⟩
def isEnumeratedReview : Atom := ⟨"isEnumeratedReview",
  "Is this reviewer run the enumerated review?", .call⟩
def briefHasListAndLedgers : Atom := ⟨"briefHasListAndLedgers",
  "Does this enumerated review's brief give the open review's inputs, the failure-mode list and the ledgers, and have the reviewer name itself the enumerated review?", .call⟩
def briefCarriesOtherReview : Atom := ⟨"briefCarriesOtherReview",
  "Does this reviewer's brief carry the other fresh review's output before the reconciliation?", .call⟩
def startsFreshReview : Atom := ⟨"startsFreshReview",
  "Does this reviewer run start one of a round's two fresh reviews (the open or the enumerated)?", .call⟩
def briefNamesSuspectedDefect : Atom := ⟨"briefNamesSuspectedDefect",
  "Does this review brief name a suspected defect, a kind of defect or an example?", .call⟩

/-! The rules. -/

/-- Rule 141: no replace helper written into a script to get past the Bash guard. -/
def noReplaceHelper : Rule where
  number := 141
  keyword := .mustNot
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom writesReplaceHelper)

/-- Rule 142: commit blockers reported honestly; no unrelated user edits committed. -/
def honestCommits : Rule where
  number := 142
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev commit ∧ₗ atom commitsUnrelatedUserEdits) ∧ₗ
    never (ev reply ∧ₗ atom misreportsCommitBlocker)

/-- Rule 143: archived evidence inspected for secrets before its commit. -/
def inspectEvidenceBeforeCommit : Rule where
  number := 143
  keyword := .must
  domain := .softwareEngineering
  formula := ev commit ∧ₗ atom commitsArchivedEvidence ⟹
    once (ev toolCall ∧ₗ link inspectsEvidenceForSecrets)

/-- Rule 144: correspondence stays in a git-ignored private folder. -/
def correspondenceStaysPrivate : Rule where
  number := 144
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom writesCorrespondenceOutsidePrivate) ∧ₗ
    never (ev commit ∧ₗ atom commitsCorrespondence)

/-- Rule 145: no ledger in its document; a message's ledger lives in `private/`. -/
def ledgerOutOfDocument : Rule where
  number := 145
  keyword := .mustNot
  domain := .tasks
  formula := never (ev editing ∧ₗ atom putsLedgerInDocument) ∧ₗ
    never (ev editing ∧ₗ atom writesMessageLedger ∧ₗ ¬ₗ ev privateEdit)

/-- Rule 146: screenshots and attachments in the task's private folder. -/
def attachmentsPrivate : Rule where
  number := 146
  keyword := .must
  domain := .tasks
  formula := never (ev toolCall ∧ₗ atom savesAttachmentOutsidePrivate)

/-- Rule 147: task scaffolding and tangential write-ups stay out of the target repository. -/
def scaffoldingOutOfTarget : Rule where
  number := 147
  keyword := .must
  domain := .tasks
  formula := never (ev editing ∧ₗ atom writesScaffoldingInTarget) ∧ₗ
    never (ev editing ∧ₗ atom writesBugWriteUpInTarget)

/-- Rule 148: no per-deployment literal in a proposed solution. -/
def noDeploymentLiteral : Rule where
  number := 148
  keyword := .mustNot
  domain := .discipline
  formula := never (ev editing ∧ₗ atom hardcodesDeploymentLiteral)

/-- Rule 149: no reference its reader can't resolve, in committed content or outside artifacts. -/
def resolvableReferences : Rule where
  number := 149
  keyword := .mustNot
  domain := .discipline
  formula := never (ev editing ∧ₗ atom referencesUnresolvable) ∧ₗ
    never (ev commit ∧ₗ atom commitMessageReferencesUnresolvable)

/-- Rule 150: the notebook's links are repo-relative, resolve locally, and are verified. -/
def notebookLocalLinks : Rule where
  number := 150
  keyword := .must
  domain := .mathematics
  formula := never (ev notebookEdit ∧ₗ atom notebookLinkUnresolvable) ∧ₗ
    (ev notebookEdit ∧ₗ atom addsNotebookLink ⟹ eventually (ev toolCall ∧ₗ link verifiesLinkTarget))

/-- Rule 151: no people named in a document colleagues read over time. -/
def noNamesInDocuments : Rule where
  number := 151
  keyword := .mustNot
  domain := .discipline
  formula := never (ev editing ∧ₗ atom namesPeopleInSharedDocument)

/-- Rule 152: a failed or empty fetch is rendered with a headless browser before any secondary
source. -/
def renderBeforeSecondarySource : Rule where
  number := 152
  keyword := .must
  domain := .softwareEngineering
  formula := ev toolCall ∧ₗ atom consultsSecondarySource ⟹
    ¬ₗ since (ev toolResult ∧ₗ atom fetchCameBackEmpty) (ev browserRender)

/-- Rule 153: an unretrievable source becomes a user request. -/
def unretrievableSourceRequest : Rule where
  number := 153
  keyword := .must
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom saysSourceUnretrievable ⟹
    eventually ((ev requestAdd ∨ₗ ev editing) ∧ₗ link filesSourceRequest)

/-- Rule 155: technical state tracked precisely. -/
def preciseTechnicalState : Rule where
  number := 155
  keyword := .must
  domain := .discipline
  formula := never (ev reply ∧ₗ atom misstatesTechnicalState)

/-- Rule 156: a proposal contradicting what is established is flagged. -/
def flagContradiction : Rule where
  number := 156
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom proposesContradictingEstablished ⟹ atom flagsContradiction

/-- Rule 157: an empirical test over a plausible claim. -/
def testOverClaim : Rule where
  number := 157
  keyword := .must
  domain := .discipline
  formula := never (ev reply ∧ₗ atom assertsTestableClaimUntested)

/-- Rule 158: a decision's factual claims are checked, and how is stated. -/
def checkDecisionClaims : Rule where
  number := 158
  keyword := .must
  domain := .tasks
  formula := ev planEdit ∧ₗ atom decisionRestsOnClaim ⟹
    once (ev toolResult ∧ₗ link checksDecisionClaim) ∧ₗ atom statesHowChecked

/-- Rule 159: a delegate's finding enters Resolved once its source is read. -/
def delegateReportIsLead : Rule where
  number := 159
  keyword := .must
  domain := .tasks
  formula := ev planEdit ∧ₗ atom resolvesFromDelegate ⟹ once (ev toolCall ∧ₗ link readsCitedSource)

/-- Rule 160: an unverified claim names every route tried. -/
def unverifiedNamesRoutes : Rule where
  number := 160
  keyword := .must
  domain := .tasks
  formula := ev editing ∧ₗ atom leavesClaimUnverified ⟹ atom namesRoutesTried

/-- Rule 161: cheap checks in the pass, expensive ones to the user as a request. -/
def cheapChecksInPass : Rule where
  number := 161
  keyword := .must
  domain := .tasks
  formula := never (ev editing ∧ₗ atom defersCheapCheck) ∧ₗ
    (ev editing ∧ₗ atom leavesExpensiveCheck ⟹ eventually (ev requestAdd))

/-- Rule 162: a step is called done after a real check, and a failure is reported as the result. -/
def realCheckBeforeDone : Rule where
  number := 162
  keyword := .must
  domain := .tasks
  formula := (ev reply ∧ₗ atom callsStepDone ⟹ once (ev toolResult ∧ₗ link checksThatStep)) ∧ₗ
    never (ev reply ∧ₗ atom hidesFailedCheck)

/-- Rule 163: tests tell correct behaviour from named failures; wiring has both real cases. -/
def distinguishingTests : Rule where
  number := 163
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom testNotDistinguishing) ∧ₗ
    never (ev editing ∧ₗ atom wiringTestLacksBothCases)

/-- Rule 164: enforcement is shown on the production path, never by configuration alone. -/
def productionPath : Rule where
  number := 164
  keyword := .must
  domain := .discipline
  formula := (ev reply ∧ₗ atom claimsEnforcement ⟹ once (ev toolResult ∧ₗ link exercisesProductionPath)) ∧ₗ
    never (ev reply ∧ₗ atom citesConfigAsEnforcement)

/-- Rule 165: no external contract proved by the agent's own mocks. -/
def noOwnMockContract : Rule where
  number := 165
  keyword := .mustNot
  domain := .discipline
  formula := never (ev reply ∧ₗ atom provesContractWithOwnMock)

/-- Rule 166: external systems tested against, a missing test or service a question of its own. -/
def testExternalSystems : Rule where
  number := 166
  keyword := .must
  domain := .tasks
  formula := never (ev editing ∧ₗ atom testsAroundExternalSystem) ∧ₗ
    (ev planEdit ∧ₗ atom findsMissingSystemTest ⟹ atom recordsAsOwnQuestion)

/-- Rule 167: a fake of a library is verified by a contract test against both. -/
def verifiedFakes : Rule where
  number := 167
  keyword := .must
  domain := .tasks
  formula := ev editing ∧ₗ atom addsFakeOfLibrary ⟹ eventually (ev testRun ∧ₗ link runsFakeContractTest)

/-- Rule 168: verification goes into committed tests. -/
def verificationCommitted : Rule where
  number := 168
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom reportsVerifiedBehaviour ⟹ eventually (ev commit ∧ₗ link commitsTestOfIt)

/-- Rule 169: nothing checkable listed as unverified. -/
def noCheckableUnverified : Rule where
  number := 169
  keyword := .mustNot
  domain := .discipline
  formula := never (ev reply ∧ₗ atom listsCheckableAsUnverified)

/-- Rule 171: absence settled by a search in the system's terms and the variants' code. -/
def settleAbsence : Rule where
  number := 171
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom claimsAbsent ⟹
    once (ev toolCall ∧ₗ link searchesOwnTerms) ∧ₗ once (ev reading ∧ₗ link readsVariantCode)

/-- Rule 172: the version in use checked; a miss on a guessed name settles nothing. -/
def checkVersionInUse : Rule where
  number := 172
  keyword := .must
  domain := .discipline
  formula := (ev reply ∧ₗ atom claimsVersionBehaviour ⟹ once (ev toolCall ∧ₗ link checksVersionInUse)) ∧ₗ
    never (ev reply ∧ₗ atom settlesOnGuessedNameMiss)

/-- Rule 173: a fitting find is followed by a look for contradicting evidence. -/
def seekContradiction : Rule where
  number := 173
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom findFitsCase ⟹ eventually (ev toolCall ∧ₗ link seeksContradiction)

/-- Rule 174: an unexplained anomaly is investigated. -/
def investigateAnomaly : Rule where
  number := 174
  keyword := .must
  domain := .discipline
  formula := ev toolResult ∧ₗ atom showsAnomaly ⟹ eventually (ev toolCall ∧ₗ link investigatesAnomaly)

/-- Rule 175: a defect found is swept for its whole class. -/
def sweepDefectClass : Rule where
  number := 175
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom reportsDefectFound ⟹ eventually (ev toolCall ∧ₗ link sweepsDefectClass)

/-- Rule 176: a defect check targets the class and runs over a real corpus. -/
def checkTargetsDefectClass : Rule where
  number := 176
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom writesDefectCheck ⟹
    atom checkTargetsClass ∧ₗ eventually (ev toolResult ∧ₗ link checkRunOverCorpus)

/-- Rule 177: a claim about a check's reach is measured before it is stated. -/
def measureCheckClaim : Rule where
  number := 177
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom claimsCheckCapability ⟹ once (ev toolResult ∧ₗ link measuresCheckCapability)

/-- Rule 178: what must hold is said before building what achieves it. -/
def statementBeforeConstruction : Rule where
  number := 178
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom buildsConstruction ⟹
    once ((ev reply ∨ₗ ev editing) ∧ₗ link statesWhatMustHold)

/-- Rule 179: an instance is evidence for its space only. -/
def wholeSpace : Rule where
  number := 179
  keyword := .must
  domain := .discipline
  formula := never (ev reply ∧ₗ atom generalizesFromInstance)

/-- Rule 180: the statement finds what was undecided; a counterexample corrects. -/
def counterexampleCorrects : Rule where
  number := 180
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom statementLeavesUndecidedUnlisted) ∧ₗ
    (ev toolResult ∧ₗ atom showsCounterexample ⟹ eventually (ev editing ∧ₗ link correctsThingOrStatement))

/-- Rule 181: what runs over time gets its start, step, safety and liveness. -/
def temporalSpecification : Rule where
  number := 181
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom specifiesTemporalSystem ⟹ atom statesStartStepSafetyLiveness

/-- Rule 182: no hidden state. -/
def noHiddenState : Rule where
  number := 182
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom addsHiddenState)

/-- Rule 183: a boundary states what each side establishes, guarantees and preserves. -/
def boundaryContract : Rule where
  number := 183
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom definesBoundary ⟹ atom statesBoundaryContract

/-- Rule 184: a replacement assumes no more and guarantees no less; a breach names its side. -/
def substitutableReplacement : Rule where
  number := 184
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom replacementWeakensContract) ∧ₗ
    (ev toolResult ∧ₗ atom showsBoundaryBreach ⟹ eventually (ev reply ∧ₗ link reportsBreachSide))

/-- Rule 185: each statement says how complete it is. -/
def statedCompleteness : Rule where
  number := 185
  keyword := .must
  domain := .discipline
  formula := never (ev reply ∧ₗ atom omitsCompleteness)

/-- Rule 186: the cheapest wrong thing is found and excluded before relying on anything. -/
def cheapestWrongFirst : Rule where
  number := 186
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom reliesOnStatement ⟹
    once ((ev reply ∨ₗ ev editing) ∧ₗ link namesCheapestWrong)

/-- Rule 187: cases built from the space's definition. -/
def casesFromDefinition : Rule where
  number := 187
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom casesNotFromDefinition)

/-- Rule 188: a generator shown to reach every case; the whole outcome observed. -/
def generatorReachesAll : Rule where
  number := 188
  keyword := .must
  domain := .discipline
  formula := (ev editing ∧ₗ atom writesPredictableConstruction ⟹ eventually (ev toolResult ∧ₗ link showsGeneratorReach)) ∧ₗ
    never (ev editing ∧ₗ atom observesPartOutcome)

/-- Rule 189: a failure reported as its smallest counterexample. -/
def smallestCounterexample : Rule where
  number := 189
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom reportsFailure ⟹ atom givesSmallestCounterexample

/-- Rule 190: the instrument held to the same checks. -/
def checkTheInstrument : Rule where
  number := 190
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom buildsInstrument ⟹ eventually (ev toolResult ∧ₗ link checksInstrument)

/-- Rule 191: every tool gets the discipline. -/
def disciplineForEveryTool : Rule where
  number := 191
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom exemptsSmallTool)

/-- Rule 192: a waiting script bounds its waits and runs on a control first. -/
def boundedWaitsControlFirst : Rule where
  number := 192
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom unboundedWait) ∧ₗ
    (ev toolCall ∧ₗ atom runsWaitingScriptOnTarget ⟹ once (ev toolResult ∧ₗ link controlRunOfScript))

/-- Rule 193: every bug becomes a theorem or property test over its class. -/
def bugBecomesTheorem : Rule where
  number := 193
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom reportsDefectFound ⟹ eventually (ev editing ∧ₗ link writesClassTheorem)

/-- Rule 194: a closable gap is closed in its turn; a report lists only gaps with a reason. -/
def closeGapsNow : Rule where
  number := 194
  keyword := .must
  domain := .discipline
  formula := never (ev reply ∧ₗ atom listsClosableGap) ∧ₗ never (ev reply ∧ₗ atom listsGapWithoutReason)

/-- Rule 195: a test is judged by the wrong versions it rejects. -/
def judgeTestByRejections : Rule where
  number := 195
  keyword := .must
  domain := .discipline
  formula := never (ev reply ∧ₗ atom judgesTestOtherwise)

/-- Rule 196: expected outcomes from an independent account; properties drafted before the body is
read; a mined law justified from the domain. -/
def independentExpectations : Rule where
  number := 196
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom expectationFromCode) ∧ₗ
    (ev editing ∧ₗ atom writesProperty ⟹ ¬ₗ once (ev reading ∧ₗ link readsBodyUnderTest)) ∧ₗ
    never (ev editing ∧ₗ atom minedLawUnjustified)

/-- Rule 197: a negative check has a positive case; an all-negative result is looked at first. -/
def positiveCaseForNegativeCheck : Rule where
  number := 197
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom negativeCheckWithoutPositive) ∧ₗ
    (ev reply ∧ₗ atom explainsAwayAllNegative ⟹ once (ev toolCall ∧ₗ link inspectsCompared))

/-- Rule 198: mutant results count after an unmutated control passed. -/
def unmutatedControlFirst : Rule where
  number := 198
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom reportsMutantResults ⟹ once (ev toolResult ∧ₗ link unmutatedControlPassed)

/-- Rule 199: a step's new tests are mutation-checked. -/
def mutationCheckStepTests : Rule where
  number := 199
  keyword := .must
  domain := .tasks
  formula := ev testEdit ∧ₗ atom addsStepTests ⟹ eventually (ev mutationRun)

/-- Rule 200: mutation testing for new decision logic of uncertain test adequacy. -/
def mutationForDecisionLogic : Rule where
  number := 200
  keyword := .should
  domain := .discipline
  formula := ev editing ∧ₗ atom addsDecisionLogic ∧ₗ atom testAdequacyUncertain ⟹
    eventually (ev mutationRun) ∨ₗ atom justified

/-- Rule 201: a kill counts when a named test failed, and the killing tests are named. -/
def namedKills : Rule where
  number := 201
  keyword := .must
  domain := .discipline
  formula := never (ev reply ∧ₗ atom countsUnshownKill) ∧ₗ
    (ev reply ∧ₗ atom reportsMutantResults ⟹ atom namesKillingTests)

/-- Rule 202: a surviving mutant is a finding, closed or explained. -/
def survivorIsFinding : Rule where
  number := 202
  keyword := .must
  domain := .discipline
  formula := ev toolResult ∧ₗ atom showsSurvivingMutant ⟹
    eventually ((ev editing ∨ₗ ev reply) ∧ₗ link closesOrExplainsSurvivor)

/-- Rule 203: each guarding test shown failing on its defect by mutation. -/
def testFailsOnItsDefect : Rule where
  number := 203
  keyword := .must
  domain := .discipline
  formula := ev testEdit ∧ₗ atom addsGuardTest ⟹ eventually (ev mutationRun ∧ₗ link mutatesGuardedDefect)

/-- Rule 204: a branch's mutation specs run together at its tip before review, the report read. -/
def mutationSpecsAtTip : Rule where
  number := 204
  keyword := .must
  domain := .tasks
  formula := ev reviewerRun ∧ₗ atom reviewsCode ⟹
    once (ev mutationRun ∧ₗ link runsSpecsAtTip) ∧ₗ once (ev reading ∧ₗ link readsBranchMutationSurvivors)

/-- Rule 205: no lookup table tested by its own entries. -/
def noTableEntryTests : Rule where
  number := 205
  keyword := .mustNot
  domain := .discipline
  formula := never (ev editing ∧ₗ atom testsTableByEntries)

/-- Rule 206: a property-test generator checked valid and complete. -/
def generatorValidAndComplete : Rule where
  number := 206
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom writesPredictableConstruction ⟹ eventually (ev toolResult ∧ₗ link showsGeneratorReach)

/-- Rule 207: a failure test raises the real library's error; a constructed one only where the state
can't be produced, built from the library's source, recorded in the plan. -/
def realLibraryErrors : Rule where
  number := 207
  keyword := .must
  domain := .tasks
  formula := ev editing ∧ₗ atom constructsLibraryError ⟹
    atom errorStateUnproducible ∧ₗ once (ev reading ∧ₗ link readsLibraryErrorSource) ∧ₗ
      eventually (ev planEdit ∧ₗ link recordsErrorSource)

/-- Rule 208: each documented error injected through every path. -/
def injectDocumentedErrors : Rule where
  number := 208
  keyword := .must
  domain := .tasks
  formula := ev editing ∧ₗ atom writesFailureTests ⟹ atom injectsEachDocumentedError

/-- Rule 209: each failure mode of the reread a test case, or why it can't apply. -/
def failureModesTested : Rule where
  number := 209
  keyword := .must
  domain := .tasks
  formula := ev editing ∧ₗ atom addsStepTests ⟹ atom coversEachFailureMode

/-- Rule 210: integration tests use the counterpart's client; the other system's deployed source is
read where its documentation is silent. -/
def counterpartClient : Rule where
  number := 210
  keyword := .must
  domain := .tasks
  formula := never (ev editing ∧ₗ atom integrationTestWithoutCounterpartClient) ∧ₗ
    (ev reply ∧ₗ atom reliesOnOtherSystemBehaviour ⟹ once (ev toolCall ∧ₗ link readsDeployedSource))

/-- Rule 211: a test skipped for a missing service is run with it, or a request is filed, in the
cycle that sees the skip: before the next checkpoint, which ends the cycle. -/
def skippedTestRunOrRequest : Rule where
  number := 211
  keyword := .must
  domain := .tasks
  formula := (ev toolResult ∧ₗ atom showsServiceSkip ⟹
      eventually ((ev testRun ∧ₗ link runsSkippedTest) ∨ₗ ev requestAdd)) ∧ₗ
    (ev checkpoint ⟹ ¬ₗ since (ev toolResult ∧ₗ atom showsServiceSkip)
      ((ev testRun ∧ₗ atom runsSkippedServiceTest) ∨ₗ ev requestAdd))

/-- Rule 212: what a cycle builds runs on input it wasn't written against before its tests count,
and the entry links the saved output. -/
def realInputBeforeTestsCount : Rule where
  number := 212
  keyword := .must
  domain := .tasks
  formula := ev entryAppend ∧ₗ atom countsTestsAsCheck ⟹
    once (ev toolResult ∧ₗ link realInputRun) ∧ₗ atom entryLinksSavedOutput

/-- Rule 213: a reader of a set of files runs on the whole set. -/
def readerOnWholeSet : Rule where
  number := 213
  keyword := .must
  domain := .tasks
  formula := ev editing ∧ₗ atom writesSetReader ⟹ eventually (ev toolResult ∧ₗ link runsOverWholeSet)

/-- Rule 214: a procedure's tools get a test walking it before their commit. -/
def procedureWalkTest : Rule where
  number := 214
  keyword := .must
  domain := .tasks
  formula := ev commit ∧ₗ atom commitsProcedureTools ⟹ once (ev testRun ∧ₗ link walksProcedure)

/-- Rule 215: an entry links saved output or says "No real run." with the reason. -/
def entryLinksRun : Rule where
  number := 215
  keyword := .must
  domain := .tasks
  formula := never (ev entryAppend ∧ₗ atom entryLacksRunOrReason)

/-- Rule 216: a real-run script runs through `tools/real_run.py`, each run in a new empty
directory. -/
def realRunThroughTool : Rule where
  number := 216
  keyword := .must
  domain := .tasks
  formula := (ev toolCall ∧ₗ atom runsRealRunScript ⟹ ev realRun) ∧ₗ
    never (ev realRun ∧ₗ atom reusesRunDirectory)

/-- Rule 217: a training run after its untrained baseline; a non-improving model's output read
beside a baseline before another. -/
def baselineBeforeTraining : Rule where
  number := 217
  keyword := .must
  domain := .tasks
  formula := ev toolCall ∧ₗ atom queuesTrainingRun ⟹
    once (ev toolResult ∧ₗ link measuresUntrainedBaseline) ∧ₗ
      ¬ₗ since (ev toolResult ∧ₗ atom showsNonImprovingModel)
        (ev toolCall ∧ₗ atom readsModelOutputBesideBaseline)

/-- Rule 218: test and measurement scripts in Lean in the user's own work. -/
def leanTestScripts : Rule where
  number := 218
  keyword := .must
  domain := .tasks
  formula := never (ev editing ∧ₗ atom writesNonLeanTestScript)

/-- Rule 219: a check's mechanism is named before it runs, and a check with none is skipped. -/
def mechanismBeforeCheck : Rule where
  number := 219
  keyword := .must
  domain := .discipline
  formula := (ev toolCall ∧ₗ atom runsCheckOrBenchmark ⟹ once (ev reply ∧ₗ link namesCheckMechanism)) ∧ₗ
    never (ev toolCall ∧ₗ atom runsCheckOrBenchmark ∧ₗ atom checkHasNoMechanism)

/-- Rule 220: a check's cheapest wrong pass found before relying on it; its verdict from an
independent account. -/
def checkCheapestWrong : Rule where
  number := 220
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom reliesOnCheckVerdict ⟹
    once ((ev reply ∨ₗ ev editing) ∧ₗ link namesCheapestWrong) ∧ₗ atom verdictFromIndependentAccount

/-- Rule 221: an independent check differs only in the assumption under test. -/
def independentCheckDiffers : Rule where
  number := 221
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom checkSharesAssumptionUnderTest)

/-- Rule 222: a known-good call compared before credentials are blamed. -/
def knownGoodBeforeCredentials : Rule where
  number := 222
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom blamesCredentials ⟹ once (ev toolResult ∧ₗ link comparesKnownGoodCall)

/-- Rule 223: a check keyed on its property, named in a sentence, with the stand-in's failing test
written first. -/
def keyOnProperty : Rule where
  number := 223
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom keysCheckOnStandIn) ∧ₗ
    (ev editing ∧ₗ atom writesPropertyCheck ⟹
      atom namesGuardedProperty ∧ₗ once (ev testEdit ∧ₗ link writesStandInFailingTest))

/-- Rule 224: a reviewed code's digest recorded; unpushed commits referenced by what a rebase
keeps. -/
def reviewDigest : Rule where
  number := 224
  keyword := .must
  domain := .discipline
  formula := (ev reviewerRun ∧ₗ atom reviewsCode ⟹ eventually (ev editing ∧ₗ link recordsReviewedDigest)) ∧ₗ
    never (ev editing ∧ₗ atom referencesUnpushedByHash)

/-- Rule 225: a decision's or setting's run-time effect stated. -/
def runtimeEffect : Rule where
  number := 225
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom recordsDecisionOrSetting ⟹ atom statesRuntimeEffect

/-- Rule 226: verdicts keyed on exit status; `pipefail` where a pipeline's status matters. -/
def exitStatusVerdicts : Rule where
  number := 226
  keyword := .must
  domain := .discipline
  formula := never (ev toolCall ∧ₗ atom keysVerdictOnPrintedWord) ∧ₗ
    never (ev pipelineNoPipefail ∧ₗ atom pipelineStatusMatters)

/-- Rule 227: a comparison's shared scenario stated before computing it. -/
def sharedScenario : Rule where
  number := 227
  keyword := .must
  domain := .discipline
  formula := ev toolCall ∧ₗ atom computesComparison ⟹ once (ev reply ∧ₗ link statesSharedScenario)

/-- Rule 228: a check refuses or reports when what it reads is gone. -/
def missingInputReported : Rule where
  number := 228
  keyword := .must
  domain := .discipline
  formula := never (ev editing ∧ₗ atom checkIgnoresMissingInput)

/-- Rule 229: a shared mechanism checked through every caller's entry point. -/
def everyEntryPoint : Rule where
  number := 229
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom changesSharedMechanism ⟹
    eventually (ev toolResult ∧ₗ link checksEveryEntryPoint)

/-- Rule 230: a partial check stands in for none of a rule. -/
def partialCheckIsPartial : Rule where
  number := 230
  keyword := .mustNot
  domain := .discipline
  formula := never (ev reply ∧ₗ atom partialCheckStandsInForRule)

/-- Rule 231: slowness measured before it is blamed. -/
def measureSlowness : Rule where
  number := 231
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom blamesSlownessOnEnvironment ⟹ once (ev toolResult ∧ₗ link measuresBlamedSlowness)

/-- Rule 232: an intermittent failure forced (failing old, passing new), its forcing kept, never
decided by repetition. -/
def forceIntermittent : Rule where
  number := 232
  keyword := .must
  domain := .discipline
  formula := (ev reply ∧ₗ atom claimsIntermittentFixed ⟹
      once (ev toolResult ∧ₗ link forcedRunFailsOld) ∧ₗ once (ev toolResult ∧ₗ link forcedRunPassesNew)) ∧ₗ
    (ev editing ∧ₗ atom fixesIntermittent ⟹ atom keepsForcingInTest) ∧ₗ
    never (ev reply ∧ₗ atom decidesIntermittentByRepeat)

/-- Rule 233: a suspect measured value fixed in the test, both values shown. -/
def fixSuspectValue : Rule where
  number := 233
  keyword := .should
  domain := .discipline
  formula := ev editing ∧ₗ atom testsMeasuredValueSuspect ⟹ atom fixesSuspectValue ∨ₗ atom justified

/-- Rule 234: a suspect order traced with sleeps and forced. -/
def forceSuspectOrder : Rule where
  number := 234
  keyword := .should
  domain := .discipline
  formula := ev editing ∧ₗ atom fixesOrderRace ⟹
    (once (ev toolResult ∧ₗ link tracedFailingOrder) ∧ₗ atom forcesOrderInTest) ∨ₗ atom justified

/-- Rule 235: a chance-based prevention's catch chance measured, stated, above 80%. -/
def chancePreventionMeasured : Rule where
  number := 235
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom addsChanceBasedPrevention ⟹
    once (ev toolResult ∧ₗ link measuresCatchChance) ∧ₗ atom statesCatchChanceAbove80

/-- Rule 236: a prevention attacked before its commit, and its design changed where the attack
lands. -/
def attackPrevention : Rule where
  number := 236
  keyword := .must
  domain := .discipline
  formula := (ev commit ∧ₗ atom commitsPrevention ⟹ once (ev reply ∧ₗ link attacksPrevention)) ∧ₗ
    never (ev commit ∧ₗ atom commitsPrevention ∧ₗ atom keepsDesignAttackLanded)

/-- Rule 237: the existing check run on the mistake, and its cost weighed, before a prevention. -/
def existingCheckFirst : Rule where
  number := 237
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom addsPrevention ⟹
    once (ev toolResult ∧ₗ link runsExistingCheckOnMistake) ∧ₗ once (ev reply ∧ₗ link weighsMistakeCost)

/-- Rule 238: a check that let a defect through is fixed. -/
def fixMissingCheck : Rule where
  number := 238
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom reportsCheckMissedDefect ⟹ eventually (ev editing ∧ₗ link fixesMissingCheck)

/-- Rule 239: a new check traps no data stored before it, and should offer a path for that data. -/
def checkSparesStoredData : Rule where
  number := 239
  keyword := .mustNot
  domain := .tasks
  formula := never (ev editing ∧ₗ atom checkTrapsExistingData) ∧ₗ
    (ev editing ∧ₗ atom addsDataCheck ⟹ atom offersExistingDataPath ∨ₗ atom justified)

/-- Rule 240: each theory entry covers the failure modes. -/
def entryFailureModes : Rule where
  number := 240
  keyword := .must
  domain := .tasks
  formula := ev planEdit ∧ₗ atom writesTheoryEntry ⟹ atom coversFailureModes

/-- Rule 241: each claimed mode's fault state walked, the surviving mechanism first. -/
def walkFaultStates : Rule where
  number := 241
  keyword := .must
  domain := .tasks
  formula := ev planEdit ∧ₗ atom claimsFaultMode ⟹ atom walksFaultStateSurvivorFirst

/-- Rule 242: callers, hostile callers and credential holders asked about. -/
def callersAndCredentials : Rule where
  number := 242
  keyword := .must
  domain := .tasks
  formula := ev planEdit ∧ₗ atom writesTheoryEntry ⟹ atom asksCallersAndCredentials

/-- Rule 243: caller-controlled identifiers bounded. -/
def boundCallerIdentifiers : Rule where
  number := 243
  keyword := .must
  domain := .tasks
  formula := never (ev editing ∧ₗ atom unboundedCallerIdentifier)

/-- Rule 244: caller values the server fetches held to the caller's scope. -/
def scopeCallerFetches : Rule where
  number := 244
  keyword := .must
  domain := .tasks
  formula := never (ev editing ∧ₗ atom unscopedCallerFetch)

/-- Rule 245: caller values escaped in log lines. -/
def escapeCallerLogs : Rule where
  number := 245
  keyword := .must
  domain := .tasks
  formula := never (ev editing ∧ₗ atom unescapedCallerLog)

/-- Rule 246: a route newly reached by a confined credential gets the checks on every body field. -/
def confinedRouteFields : Rule where
  number := 246
  keyword := .must
  domain := .tasks
  formula := ev editing ∧ₗ atom opensRouteToConfinedCredential ⟹ atom checksEveryBodyField

/-- Rule 247: a signal's reader and its coverage of failures established. -/
def signalReader : Rule where
  number := 247
  keyword := .must
  domain := .tasks
  formula := ev editing ∧ₗ atom addsSignal ⟹ atom statesSignalReaderAndCoverage

/-- Rule 248: each permission pinned. -/
def pinPermissions : Rule where
  number := 248
  keyword := .must
  domain := .tasks
  formula := never (ev editing ∧ₗ atom unpinnedPermission)

/-- Rule 249: a set's members and readers listed when it changes. -/
def setReadersListed : Rule where
  number := 249
  keyword := .must
  domain := .tasks
  formula := ev editing ∧ₗ atom changesSetMembership ⟹ atom listsSetReaders

/-- Rule 250: a per-call part's cost stated and moved off the path where it can be. -/
def perCallCost : Rule where
  number := 250
  keyword := .must
  domain := .tasks
  formula := ev editing ∧ₗ atom addsPerCallPart ⟹ atom statesPerCallCost

/-- Rule 251: a repeated job reads only changes, with a timed no-change run and a test of it. -/
def incrementalJob : Rule where
  number := 251
  keyword := .must
  domain := .tasks
  formula := ev editing ∧ₗ atom addsRepeatedJob ⟹
    atom readsOnlyChanges ∧ₗ eventually (ev toolResult ∧ₗ link timesNoChangeRun) ∧ₗ
      eventually (ev testRun ∧ₗ link testsSecondRunReadsNothing)

/-- Rule 252: what deploys into a cluster rendered and checked for it before the plan settles and
before its branches are offered. -/
def renderForCluster : Rule where
  number := 252
  keyword := .must
  domain := .tasks
  formula := (ev planEdit ∧ₗ atom settlesClusterPlan ⟹ once (ev toolResult ∧ₗ link rendersForCluster)) ∧ₗ
    (ev reply ∧ₗ atom offersClusterBranch ⟹ once (ev toolResult ∧ₗ link rendersForCluster))

/-- Rule 253: a cluster change's deployment branch in its Path from the start. -/
def deploymentBranchInPath : Rule where
  number := 253
  keyword := .must
  domain := .tasks
  formula := ev planEdit ∧ₗ atom writesClusterChangePath ⟹ atom pathHasDeploymentBranch

/-- Rule 254: existing instances listed, the simplest path taken or the difference said. -/
def existingInstances : Rule where
  number := 254
  keyword := .must
  domain := .tasks
  formula := ev planEdit ∧ₗ atom decidesIntegrationPath ⟹ atom listsExistingInstances

/-- Rule 255: a new artifact measured against all of its kind, the numbers given in the entry. -/
def measureAgainstKind : Rule where
  number := 255
  keyword := .must
  domain := .tasks
  formula := ev editing ∧ₗ atom addsArtifactOfExistingKind ⟹
    once (ev toolResult ∧ₗ link measuresAgainstExisting) ∧ₗ
      eventually (ev entryAppend ∧ₗ link entryGivesArtifactNumbers)

/-- Rule 256: a whole-set claim backed by a check of every member, listed by definition, and the
listing named. -/
def wholeSetChecked : Rule where
  number := 256
  keyword := .must
  domain := .tasks
  formula := (ev reply ∨ₗ ev editing) ∧ₗ atom makesWholeSetClaim ⟹
    once (ev toolResult ∧ₗ link listsSetByDefinition) ∧ₗ atom namesSetListing

/-- Rule 257: an accepted wrong case is the user's trade-off and a stated limit of the change. -/
def acceptedWrongCase : Rule where
  number := 257
  keyword := .must
  domain := .tasks
  formula := ev planEdit ∧ₗ atom acceptsWrongCase ⟹
    atom marksUsersTradeOff ∧ₗ eventually (ev editing ∧ₗ link statesLimitInChange)

/-- Rule 258: each relied-on property has a realistic acceptance case. -/
def realisticAcceptance : Rule where
  number := 258
  keyword := .must
  domain := .tasks
  formula := ev planEdit ∧ₗ atom namesReliedProperty ⟹ atom givesRealisticAcceptance

/-- Rule 259: each design number's provenance stated. -/
def designNumberProvenance : Rule where
  number := 259
  keyword := .must
  domain := .tasks
  formula := ev editing ∧ₗ atom setsDesignNumber ⟹ atom statesNumberProvenance

/-- Rule 260: a calibrated value accepted by a run elsewhere, or the run said impossible; a
definition's value says so. -/
def calibratedValues : Rule where
  number := 260
  keyword := .must
  domain := .tasks
  formula := (ev planEdit ∧ₗ atom acceptsCalibratedValue ⟹
      once (ev toolResult ∧ₗ link runInUncalibratedEnvironment) ∨ₗ atom statesRunImpossible) ∧ₗ
    (ev editing ∧ₗ atom setsDefinitionValue ⟹ atom saysDefinitionSet)

/-- Rule 261: an alternative rejected by a check, never by an open question. -/
def rejectByCheck : Rule where
  number := 261
  keyword := .must
  domain := .tasks
  formula := (ev planEdit ∧ₗ atom rejectsAlternative ⟹ once (ev toolResult ∧ₗ link checksRejectedAlternative)) ∧ₗ
    never (ev planEdit ∧ₗ atom rejectsByOpenQuestion)

/-- Rule 262: the defining document read for each behaviour relied on. -/
def readDefiningDocument : Rule where
  number := 262
  keyword := .must
  domain := .tasks
  formula := ev editing ∧ₗ atom reliesOnLibraryBehaviour ⟹ once (ev toolCall ∧ₗ link readsDefiningDocument)

/-- Rule 263: a copied precedent counts once seen running. -/
def precedentSeenRunning : Rule where
  number := 263
  keyword := .must
  domain := .tasks
  formula := ev planEdit ∧ₗ atom citesCopiedPrecedent ⟹ once (ev toolResult ∧ₗ link seesPrecedentRunning)

/-- Rule 264: an adopted contract listed member by member, promising the least its use needs. -/
def contractMembers : Rule where
  number := 264
  keyword := .must
  domain := .tasks
  formula := ev planEdit ∧ₗ atom adoptsContract ⟹ atom listsContractMembers

/-- Rule 265: each acceptance case has an input and outcome a named wrong implementation changes. -/
def acceptanceFails : Rule where
  number := 265
  keyword := .must
  domain := .tasks
  formula := never (ev planEdit ∧ₗ atom acceptanceLacksWrongImpl)

/-- Rule 266: no acceptance clause restating the deliverable or a rule. -/
def acceptanceShowsCase : Rule where
  number := 266
  keyword := .must
  domain := .tasks
  formula := never (ev planEdit ∧ₗ atom acceptanceRestatesRule)

/-- Rule 267: each member of a rule over several gets its case. -/
def caseForEachMember : Rule where
  number := 267
  keyword := .must
  domain := .tasks
  formula := never (ev planEdit ∧ₗ atom memberWithoutCase)

/-- Rule 268: refusals paired with passes, bound ends and forms tried, scope edges passing. -/
def pairedCases : Rule where
  number := 268
  keyword := .must
  domain := .tasks
  formula := never (ev planEdit ∧ₗ atom refusalCaseUnpaired)

/-- Rule 269: an "every" clause placed where its members exist. -/
def everyClausePlaced : Rule where
  number := 269
  keyword := .must
  domain := .tasks
  formula := never (ev planEdit ∧ₗ atom everyClauseMisplaced)

/-- Rule 270: a referring clause's passage cased part by part before any review. -/
def referredPartsCased : Rule where
  number := 270
  keyword := .must
  domain := .tasks
  formula := ev reviewerRun ∧ₗ atom reviewsPlan ⟹
    ¬ₗ since (ev planEdit ∧ₗ atom writesReferringClause) (ev planEdit ∧ₗ atom casesReferredParts)

/-- Rule 271: a finding counts only with a failure scenario. -/
def findingNeedsScenario : Rule where
  number := 271
  keyword := .must
  domain := .tasks
  formula := never (ev editing ∧ₗ atom countsFindingWithoutScenario)

/-- Rule 272: no looping on notes; matters of taste left out. -/
def noLoopOnNotes : Rule where
  number := 272
  keyword := .mustNot
  domain := .tasks
  formula := never (ev reviewerRun ∧ₗ atom loopsOnNotes) ∧ₗ never (ev editing ∧ₗ atom recordsTasteFinding)

/-- Rule 273: a held finding marked `Waiting:`; the writer's own decision never waits. -/
def waitingMarked : Rule where
  number := 273
  keyword := .must
  domain := .tasks
  formula := never (ev editing ∧ₗ atom heldFindingUnmarked) ∧ₗ never (ev editing ∧ₗ atom ownDecisionMarkedWaiting)

/-- Rule 274: each fresh-review finding states its verdict beside its origin. -/
def findingVerdictAndOrigin : Rule where
  number := 274
  keyword := .must
  domain := .tasks
  formula := never (ev editing ∧ₗ atom findingLacksVerdictOrOrigin)

/-- Rule 275: each changed file's diff read against the failure-mode list before any reviewer, and
what the pass finds fixed or recorded by then. -/
def writersPassFirst : Rule where
  number := 275
  keyword := .must
  domain := .tasks
  formula := (ev reviewerRun ∧ₗ atom reviewsCode ⟹ once (ev toolCall ∧ₗ link readsDiffAgainstModes)) ∧ₗ
    never (ev reviewerRun ∧ₗ atom reviewsCode ∧ₗ atom writersPassFindingUnhandled)

/-- Rule 276: a commit's claims checked against its tree, and again after a rewrite. -/
def commitClaimsChecked : Rule where
  number := 276
  keyword := .must
  domain := .tasks
  formula := (ev commit ∧ₗ atom commitMessageMakesClaims ⟹ once (ev toolResult ∧ₗ link checksCommitClaims)) ∧ₗ
    (ev toolCall ∧ₗ atom rewritesHistory ⟹ eventually (ev toolResult ∧ₗ link rechecksCommitClaims))

/-- Rule 277: the open review gets only what a hosting-platform colleague sees. -/
def openReviewInputs : Rule where
  number := 277
  keyword := .must
  domain := .tasks
  formula := never (ev reviewerRun ∧ₗ atom openReviewGetsRecords)

/-- Rule 278: the enumerated review gets the list and ledgers and names itself. -/
def enumeratedReviewInputs : Rule where
  number := 278
  keyword := .must
  domain := .tasks
  formula := ev reviewerRun ∧ₗ atom isEnumeratedReview ⟹ atom briefHasListAndLedgers

/-- Rule 279: neither fresh review reads the other's output before reconciliation; both are briefed
in one message. -/
def reviewsApart : Rule where
  number := 279
  keyword := .mustNot
  domain := .tasks
  formula := never (ev reviewerRun ∧ₗ atom briefCarriesOtherReview) ∧ₗ
    (ev reviewerRun ∧ₗ atom startsFreshReview ⟹ sameMessage pairedReviewer)

/-- Rule 280: no suspected defect, kind of defect or example in a review brief. -/
def briefNamesNoDefect : Rule where
  number := 280
  keyword := .mustNot
  domain := .tasks
  formula := never (ev reviewerRun ∧ₗ atom briefNamesSuspectedDefect)

def rules : List Rule :=
  [noReplaceHelper, honestCommits, inspectEvidenceBeforeCommit, correspondenceStaysPrivate,
   ledgerOutOfDocument, attachmentsPrivate, scaffoldingOutOfTarget, noDeploymentLiteral,
   resolvableReferences, notebookLocalLinks, noNamesInDocuments, renderBeforeSecondarySource,
   unretrievableSourceRequest, preciseTechnicalState, flagContradiction, testOverClaim,
   checkDecisionClaims, delegateReportIsLead, unverifiedNamesRoutes, cheapChecksInPass,
   realCheckBeforeDone, distinguishingTests, productionPath, noOwnMockContract, testExternalSystems,
   verifiedFakes, verificationCommitted, noCheckableUnverified, settleAbsence, checkVersionInUse,
   seekContradiction, investigateAnomaly, sweepDefectClass, checkTargetsDefectClass,
   measureCheckClaim, statementBeforeConstruction, wholeSpace, counterexampleCorrects,
   temporalSpecification, noHiddenState, boundaryContract, substitutableReplacement,
   statedCompleteness, cheapestWrongFirst, casesFromDefinition, generatorReachesAll,
   smallestCounterexample, checkTheInstrument, disciplineForEveryTool, boundedWaitsControlFirst,
   bugBecomesTheorem, closeGapsNow, judgeTestByRejections, independentExpectations,
   positiveCaseForNegativeCheck, unmutatedControlFirst, mutationCheckStepTests,
   mutationForDecisionLogic, namedKills, survivorIsFinding, testFailsOnItsDefect,
   mutationSpecsAtTip, noTableEntryTests, generatorValidAndComplete, realLibraryErrors,
   injectDocumentedErrors, failureModesTested, counterpartClient, skippedTestRunOrRequest,
   realInputBeforeTestsCount, readerOnWholeSet, procedureWalkTest, entryLinksRun,
   realRunThroughTool, baselineBeforeTraining, leanTestScripts, mechanismBeforeCheck,
   checkCheapestWrong, independentCheckDiffers, knownGoodBeforeCredentials, keyOnProperty,
   reviewDigest, runtimeEffect, exitStatusVerdicts, sharedScenario, missingInputReported,
   everyEntryPoint, partialCheckIsPartial, measureSlowness, forceIntermittent, fixSuspectValue,
   forceSuspectOrder, chancePreventionMeasured, attackPrevention, existingCheckFirst,
   fixMissingCheck, checkSparesStoredData, entryFailureModes, walkFaultStates,
   callersAndCredentials, boundCallerIdentifiers, scopeCallerFetches, escapeCallerLogs,
   confinedRouteFields, signalReader, pinPermissions, setReadersListed, perCallCost,
   incrementalJob, renderForCluster, deploymentBranchInPath, existingInstances, measureAgainstKind,
   wholeSetChecked, acceptedWrongCase, realisticAcceptance, designNumberProvenance,
   calibratedValues, rejectByCheck, readDefiningDocument, precedentSeenRunning, contractMembers,
   acceptanceFails, acceptanceShowsCase, caseForEachMember, pairedCases, everyClausePlaced,
   referredPartsCased, findingNeedsScenario, noLoopOnNotes, waitingMarked, findingVerdictAndOrigin,
   writersPassFirst, commitClaimsChecked, openReviewInputs, enumeratedReviewInputs, reviewsApart,
   briefNamesNoDefect]

/-! The MAY rule. -/

/-- The firefox-session reads of rule 154: the agent asks the user to sign in, then reads the page
through the saved session with a GET. -/
def firefoxSessionRead : Array Step :=
  seq [.reply "Please sign in to the host in Firefox and run tools/firefox_cookies.py HOST.",
    bash "python3 tools/firefox_cookies.py host.example", bash "python3 tools/firefox_get.py host.example /page"]

/-- Rule 154 (MAY): asking the user to sign in in Firefox and reading through `firefox_get.py`
(GET only) publishes nothing, so rule 1 keeps it with nothing asked of a model; and with every
question answered no, it keeps every rule of this range. -/
theorem r154_firefox_read_allowed :
    run pushNeedsAuthorization firefoxSessionRead [] = .kept ∧
      rules.all (fun r => r.verdict (Ctx.build firefoxSessionRead true fun _ => some false) == .kept) =
        true := by
  decide +kernel

def permissions : List Nat := [154]

end Rails.Ruleset.Range2
