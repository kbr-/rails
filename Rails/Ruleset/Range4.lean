import Rails.Rules
import Rails.Examples
import Rails.Witness

/-!
Rules 421 to 560 of `tasks/agents-on-rails/RULES.md`: numerical verification and computation
output, resource evidence, rented machines, Lean and the design skills, merge request descriptions
and reviews, paper writing, and the task protocol's records. None of them is a MAY rule.
-/

namespace Rails.Ruleset.Range4
open Rails Formula Ruleset Rules Examples

/-! Tests on events. -/

private def word (s : String) (ws : List (List Char)) : Bool := ws.contains s.toList

/-- The call's shell command contains `s`. -/
def commandHas (s : String) (e : Event) : Bool :=
  match command e with
  | some c => occursIn s.toList c.toList
  | none => false

/-- Some command of the call has a word ending `prog` (the program itself, or a script a launcher
such as `compute.sh` runs), with `p` holding of its words. -/
def invokes (prog : String) (p : List (List Char) → Bool) (e : Event) : Bool :=
  (programs e).any fun (_, ws) => ws.any (endsWith prog.toList ·) && p ws

/-- The call edits a file whose path ends `suffix`. -/
def editsPathEnding (suffix : String) (e : Event) : Bool :=
  match writePath e with
  | some p => endsWith suffix.toList p.toList
  | none => false

/-- The call's tool name contains `s` (an MCP tool such as RunPod's `create-pod`). -/
def toolHas (s : String) : Event → Bool
  | .call _ tool _ => occursIn s.toList tool.toList
  | _ => false

def isCompactionSummary : Event → Bool
  | .user t => occursIn "continued from a previous conversation".toList t.toList
  | _ => false

def isTaskPaused (e : Event) : Bool :=
  invokes "task_index.py" (fun ws => word "set" ws && word "paused" ws) e

/-! Event predicates. -/

def toolCall : Pred := ⟨"toolCall", isCall, [bash "ls"]⟩
def anyResult : Pred := ⟨"anyResult", isResult, [.result "c" "out"]⟩
def hookRefusal : Pred := ⟨"hookRefusal", isRefusalEvent, [.refusal "task_lock" "locked"]⟩
def compactionSummary : Pred := ⟨"compactionSummary", isCompactionSummary,
  [.user "This session is being continued from a previous conversation that ran out of context."]⟩
def scriptRun : Pred := ⟨"scriptRun",
  fun e => (programs e).any fun (w, _) => endsWith ".py".toList w || endsWith "compute.sh".toList w,
  [bash "python3 count.py --out r.json", bash "./compute.sh python3 calc.py"]⟩
def commit : Pred := ⟨"commit", runs "git" (word "commit"), [bash "git commit -m fix"]⟩
def gitDiff : Pred := ⟨"gitDiff", runs "git" (word "diff"), [bash "git diff orig HEAD"]⟩
def gitRebase : Pred := ⟨"gitRebase",
  runs "git" fun ws => word "rebase" ws && !word "--continue" ws && !word "--abort" ws &&
    !word "--skip" ws,
  [bash "git rebase -i main"]⟩
def rebaseContinue : Pred := ⟨"rebaseContinue",
  runs "git" (fun ws => word "rebase" ws && word "--continue" ws), [bash "git rebase --continue"]⟩
def forcePush : Pred := ⟨"forcePush",
  runs "git" fun ws => word "push" ws &&
    ws.any fun w => hasPrefix "--force".toList w || w == "-f".toList,
  [bash "git push --force-with-lease origin b", bash "git push -f origin b"]⟩
def readsApprovals : Pred := ⟨"readsApprovals",
  fun e => runs "glab" (fun ws => ws.any (occursIn "approv".toList)) e ||
    runs "gh" (fun ws => ws.any (occursIn "approv".toList)) e,
  [bash "glab mr approvers 3", bash "glab api projects/1/merge_requests/3/approvals"]⟩
def mrOpen : Pred := ⟨"mrOpen",
  fun e => runs "glab" (fun ws => word "mr" ws && word "create" ws) e ||
    runs "gh" (fun ws => word "pr" ws && word "create" ws) e,
  [bash "glab mr create --fill", bash "gh pr create --fill"]⟩
def mrView : Pred := ⟨"mrView",
  fun e => runs "glab" (fun ws => word "mr" ws && word "view" ws) e ||
    runs "gh" (fun ws => word "pr" ws && word "view" ws) e,
  [bash "glab mr view 3", bash "gh pr view 3"]⟩
/-- A merge request's description written: its `_MR.md` cover letter, or a create or update. -/
def mrDescription : Pred := ⟨"mrDescription",
  fun e => editsPathEnding "_MR.md" e ||
    runs "glab" (fun ws => word "mr" ws && (word "create" ws || word "update" ws)) e ||
    runs "gh" (fun ws => word "pr" ws && (word "create" ws || word "edit" ws)) e,
  [edit "tasks/x/X_MR.md", bash "glab mr update 3 --description x"]⟩
def postsReviewComment : Pred := ⟨"postsReviewComment",
  fun e => runs "glab" (fun ws => word "mr" ws && word "note" ws) e ||
    runs "gh" (fun ws => word "pr" ws && (word "comment" ws || word "review" ws)) e,
  [bash "glab mr note 3 -m x", bash "gh pr review 3 --comment -b x"]⟩
def ssh : Pred := ⟨"ssh", runs "ssh" (fun _ => true), [bash "ssh -p 70022 root@pod"]⟩
def cgroupLimitRead : Pred := ⟨"cgroupLimitRead",
  fun e => commandHas "cpu.max" e || commandHas "memory.max" e || commandHas "cfs_quota_us" e ||
    commandHas "memory.limit_in_bytes" e,
  [bash "cat /sys/fs/cgroup/cpu.max /sys/fs/cgroup/memory.max"]⟩
def readsCpuacctUsage : Pred := ⟨"readsCpuacctUsage", commandHas "cpuacct.usage",
  [bash "cat /sys/fs/cgroup/cpuacct/cpuacct.usage"]⟩
def readsCpuStat : Pred := ⟨"readsCpuStat", commandHas "cpu.stat", [bash "cat /sys/fs/cgroup/cpu.stat"]⟩
def nvidiaSmi : Pred := ⟨"nvidiaSmi", runs "nvidia-smi" (fun _ => true), [bash "nvidia-smi"]⟩
def marchNativeBuild : Pred := ⟨"marchNativeBuild",
  fun e => (programs e).any fun (_, ws) => ws.contains "-march=native".toList,
  [bash "gcc -O3 -march=native k.c"]⟩
def hostCpuCheck : Pred := ⟨"hostCpuCheck",
  fun e => runs "lscpu" (fun _ => true) e || commandHas "/proc/cpuinfo" e, [bash "lscpu"]⟩
def disablesAvx512Fp16 : Pred := ⟨"disablesAvx512Fp16", commandHas "-mno-avx512fp16",
  [bash "gcc -O3 -march=native -mno-avx512fp16 k.c"]⟩
def aria2Download : Pred := ⟨"aria2Download", runs "aria2c" (fun _ => true),
  [bash "aria2c -i list.txt -d models"]⟩
def hfDownload : Pred := ⟨"hfDownload",
  fun e => runs "hf" (word "download") e || runs "huggingface-cli" (word "download") e,
  [bash "hf download org/model --local-dir models"]⟩
def aria2FilesListed : Pred := ⟨"aria2FilesListed", commandHas ".aria2", [bash "ls models/*.aria2"]⟩
def interfaceBytesRead : Pred := ⟨"interfaceBytesRead",
  fun e => commandHas "/proc/net/dev" e || commandHas "/sys/class/net" e, [bash "cat /proc/net/dev"]⟩
def podCreate : Pred := ⟨"podCreate",
  fun e => toolHas "create-pod" e || runs "runpodctl" (fun ws => word "create" ws && word "pod" ws) e,
  [.call "p" "mcp__plugin_runpod_runpod__create-pod" []]⟩
def podStatusRead : Pred := ⟨"podStatusRead",
  fun e => toolHas "get-pod" e || toolHas "list-pods" e || runs "runpodctl" (word "get") e,
  [.call "p" "mcp__plugin_runpod_runpod__get-pod" [], bash "runpodctl get pod"]⟩
def jobInspection : Pred := ⟨"jobInspection",
  fun e => invokes "job_metrics.py" (word "inspect") e || runs "strace" (fun _ => true) e ||
    runs "py-spy" (fun _ => true) e,
  [bash "./compute.sh --threads 1 python3 tools/job_metrics.py inspect u.service"]⟩
def leanBuild : Pred := ⟨"leanBuild", invokes "lake" (word "build"), [bash "lake build"]⟩
/-- A Lean check: a build, a file check through `lake env lean`, or the language server's
diagnostics or verification. -/
def leanCheck : Pred := ⟨"leanCheck",
  fun e => invokes "lake" (fun ws => word "build" ws || word "env" ws) e ||
    toolHas "lean_diagnostic" e || toolHas "lean_verify" e,
  [bash "lake env lean A.lean", .call "l" "mcp__lean-lsp__lean_diagnostic_messages" []]⟩
def leanEdit : Pred := ⟨"leanEdit", editsPathEnding ".lean", [edit "Rails/A.lean"]⟩
def notebookEdit : Pred := ⟨"notebookEdit", editsPathEnding "notebook.html", [edit "notebook.html"]⟩
def planEdit : Pred := ⟨"planEdit", editsPathEnding "PLAN.md", [edit "tasks/x/PLAN.md"]⟩
def taskJsonEdit : Pred := ⟨"taskJsonEdit", editsPathEnding "task.json", [edit "tasks/x/task.json"]⟩
def ledgerEdit : Pred := ⟨"ledgerEdit", editsPathEnding "_EVIDENCE.md", [edit "tasks/x/X_MR_EVIDENCE.md"]⟩
def cycleCheckpoint : Pred := ⟨"cycleCheckpoint",
  fun e => invokes "finish-turn.py" (fun _ => true) e || invokes "task_checkpoint.py" (fun _ => true) e,
  [bash "python3 tools/task_checkpoint.py x --entry e.html", bash "./tools/finish-turn.py t"]⟩
def taskIndexNew : Pred := ⟨"taskIndexNew", invokes "task_index.py" (word "new"),
  [bash "python3 tools/task_index.py new x"]⟩
def taskStatusSet : Pred := ⟨"taskStatusSet", invokes "task_index.py" (word "set"),
  [bash "python3 tools/task_index.py set x --status in_progress"]⟩
def taskPaused : Pred := ⟨"taskPaused", isTaskPaused,
  [bash "python3 tools/task_index.py set a --status paused"]⟩
def taskBlocked : Pred := ⟨"taskBlocked",
  invokes "task_index.py" (fun ws => word "set" ws && word "blocked" ws),
  [bash "python3 tools/task_index.py set x --status blocked"]⟩
def requestResolve : Pred := ⟨"requestResolve",
  invokes "task_index.py" (fun ws => word "request" ws && word "resolve" ws),
  [bash "python3 tools/task_index.py request resolve x 3"]⟩
def requestEdit : Pred := ⟨"requestEdit",
  invokes "task_index.py" (fun ws => word "request" ws && word "edit" ws),
  [bash "python3 tools/task_index.py request edit x 3 --body-file f"]⟩
def stableCheck : Pred := ⟨"stableCheck", invokes "task_index.py" (word "stable"),
  [bash "python3 tools/task_index.py stable x"]⟩
def statusTextRun : Pred := ⟨"statusTextRun", invokes "status_text.py" (fun _ => true),
  [bash "python3 tools/status_text.py x"]⟩
def computeRun : Pred := ⟨"computeRun", invokes "compute.sh" (fun _ => true),
  [bash "./compute.sh python3 calc.py"]⟩
def loadsAnySkill : Pred := ⟨"loadsAnySkill", isTool "Skill", [.call "s" "Skill" [("skill", "x")]]⟩

/-- A Skill call loading the skill `s`. -/
def loadsSkill (s : String) : Pred :=
  ⟨"loadsSkill " ++ s, fun e => isTool "Skill" e && e.field "skill" == some s,
   [.call "s" "Skill" [("skill", s)]]⟩

/-- The skills every software task loads (rule 528). -/
def defaultSkills : List String :=
  ["engineering-discipline", "engineering-discipline-personal", "software-design-philosophy",
   "software-design-flexibility", "type-driven-design", "algebra-driven-design", "property-testing"]

def preds : List Pred :=
  [toolCall, anyResult, hookRefusal, compactionSummary, scriptRun, commit, gitDiff, gitRebase,
   rebaseContinue, forcePush, readsApprovals, mrOpen, mrView, mrDescription, postsReviewComment, ssh,
   cgroupLimitRead, readsCpuacctUsage, readsCpuStat, nvidiaSmi, marchNativeBuild, hostCpuCheck,
   disablesAvx512Fp16, aria2Download, hfDownload, aria2FilesListed, interfaceBytesRead, podCreate,
   podStatusRead, jobInspection, leanBuild, leanCheck, leanEdit, notebookEdit, planEdit,
   taskJsonEdit, ledgerEdit, cycleCheckpoint, taskIndexNew, taskStatusSet, taskPaused, taskBlocked,
   requestResolve, requestEdit, stableCheck, statusTextRun, computeRun, loadsAnySkill] ++
  (defaultSkills ++ ["lean4"]).map loadsSkill

theorem preds_wellFormed : preds.all Pred.wellFormed = true := by decide

/-! Relations. -/

/-- The second step sets a task paused. -/
def pausesTask : Rel :=
  ⟨"pausesTask", fun _ t => isTaskPaused t.event,
   [(edit "tasks/b/PLAN.md", bash "python3 tools/task_index.py set a --status paused")]⟩

def rels : List Rel := [pausesTask]
theorem rels_wellFormed : rels.all Rel.wellFormed = true := by decide

/-- `φ` in the current cycle: since the last checkpoint. -/
def inCycle (φ : Formula) : Formula := since φ (ev cycleCheckpoint)

/-- `φ` held since the last compaction summary. -/
def sinceCompaction (φ : Formula) : Formula := since φ (ev compactionSummary)

/-! Atoms: numerical verification and computation output (421 to 437). -/

def writesNumericalCheck : Atom := ⟨"writesNumericalCheck",
  "Does this edit write or change a script that checks a mathematical claim numerically?", .edit⟩
def matchesConventions : Atom := ⟨"matchesConventions",
  "Does the check this edit writes use the claim's intended field, encoding, parameters and degree conventions?", .edit⟩
def checkCanFalsify : Atom := ⟨"checkCanFalsify",
  "Can the check this edit writes falsify the claim, with nonvacuous cases and negative controls?", .edit⟩
def reportsInstanceResult : Atom := ⟨"reportsInstanceResult",
  "Does this reply report the outcome of a finite instance or finite-domain check?", .reply⟩
def statesInstanceKind : Atom := ⟨"statesInstanceKind",
  "Does this reply say whether the instance is unsatisfiable or a satisfiable finite domain?", .reply⟩
def statesSmallestParameters : Link := ⟨"statesSmallestParameters",
  "Does this reply state the smallest nonvacuous parameters and space sizes for the check the anchored edit writes?"⟩
def countsPredictions : Link := ⟨"countsPredictions",
  "Does this reply count the claim's predictions at reachable parameters for the check the anchored edit writes?"⟩
def comparesUnconditionalBounds : Link := ⟨"comparesUnconditionalBounds",
  "Does this reply compare those predictions with unconditional bounds, for the check the anchored edit writes?"⟩
def verifiesHypotheses : Link := ⟨"verifiesHypotheses",
  "Does this reply verify the hypotheses of the claim the anchored edit's check tests?"⟩
def registersFiniteCheck : Atom := ⟨"registersFiniteCheck",
  "Does this notebook edit add an entry registering a finite check?", .edit⟩
def hasNonvacuityCount : Atom := ⟨"hasNonvacuityCount",
  "Does the entry this edit adds give the nonvacuity count in its Nonvacuity paragraph?", .edit⟩
def interpretsSubThresholdFailure : Atom := ⟨"interpretsSubThresholdFailure",
  "Does this reply draw a conclusion from a failure confined to sizes below the nonvacuous threshold?", .reply⟩
def reportsFiniteOutcomes : Atom := ⟨"reportsFiniteOutcomes",
  "Does this reply report outcomes of a finite check over links, fibers or restrictions?", .reply⟩
def bySubInstanceSize : Atom := ⟨"bySubInstanceSize",
  "Does this reply give those outcomes by sub-instance size?", .reply⟩
def reportsBoundTested : Atom := ⟨"reportsBoundTested",
  "Does this reply report that a proposed bound holds or was tested?", .reply⟩
def testsExtremalExamples : Link := ⟨"testsExtremalExamples",
  "Does this run test the anchored reply's bound on the simplest structurally different extremal examples?"⟩
def comparesWithGoalNeed : Atom := ⟨"comparesWithGoalNeed",
  "Does this reply compare the bound's full success with what the goal needs?", .reply⟩
def computesOwnQuantity : Atom := ⟨"computesOwnQuantity",
  "Does the check this edit writes compute the statement's own quantity, not a stronger or weaker surrogate?", .edit⟩
def docstringStatesStatement : Atom := ⟨"docstringStatesStatement",
  "Does the script this edit writes state the tested statement in its docstring?", .edit⟩
def generatesValidInputs : Atom := ⟨"generatesValidInputs",
  "Does the script this edit writes generate inputs meeting the statement's hypotheses and assert them in code?", .edit⟩
def citesRunResults : Atom := ⟨"citesRunResults",
  "Does this reply cite results of computation runs?", .reply⟩
def saysNewOrArchived : Atom := ⟨"saysNewOrArchived",
  "Does this reply say which of the cited results come from new runs and which from archived ones?", .reply⟩
def treatsPrimeAsHypothesis : Atom := ⟨"treatsPrimeAsHypothesis",
  "Does this reply treat a kernel's chosen prime as a theorem's characteristic hypothesis?", .reply⟩
def claimsSmallCharacteristic : Atom := ⟨"claimsSmallCharacteristic",
  "Does this reply claim a result in a small characteristic?", .reply⟩
def citesPerCharacteristicProof : Atom := ⟨"citesPerCharacteristicProof",
  "Does this reply rest that claim on a structural proof or a certificate in each characteristic claimed?", .reply⟩
def reportsLiftedCertificate : Atom := ⟨"reportsLiftedCertificate",
  "Does this reply report a certificate lifted to integral solutions?", .reply⟩
def statesCertificateScope : Atom := ⟨"statesCertificateScope",
  "Does this reply state that certificate's scope (characteristic zero and all but finitely many characteristics)?", .reply⟩
def namesUncomputedPrimes : Atom := ⟨"namesUncomputedPrimes",
  "Does this reply name exceptional primes that were not computed?", .reply⟩
def measuresPcDegree : Atom := ⟨"measuresPcDegree",
  "Does this edit write a computation measuring polynomial calculus refutation degree?", .edit⟩
def usesTruncatedBasis : Atom := ⟨"usesTruncatedBasis",
  "Does that computation use a degree-truncated standard basis (such as Singular's degBound)?", .edit⟩
def usesExactClosure : Atom := ⟨"usesExactClosure",
  "Does that computation use an exact degree-D closure?", .edit⟩
def checksMonotonicity : Atom := ⟨"checksMonotonicity",
  "Does that computation check monotonicity under added axioms as a control?", .edit⟩
def runsKernelAtScale : Atom := ⟨"runsKernelAtScale",
  "Does this call run a computational kernel at a scale beyond its small validation cases?", .call⟩
def validatesAgainstReference : Link := ⟨"validatesAgainstReference",
  "Does this run validate the anchored call's kernel against a reference implementation on small cases?"⟩
def checksRanksWithSecondLibrary : Link := ⟨"checksRanksWithSecondLibrary",
  "Does this run check the anchored call's kernel's ranks against a second library, or does that kernel compute no ranks?"⟩
def callsForeignFunction : Atom := ⟨"callsForeignFunction",
  "Does this edit call a foreign function (ctypes, cffi, an FFI binding)?", .edit⟩
def declaresArgumentTypes : Atom := ⟨"declaresArgumentTypes",
  "Does this edit declare the argument types of every foreign function it calls?", .edit⟩
def reliesOnCasOutput : Atom := ⟨"reliesOnCasOutput",
  "Does this reply rely on the output of a computer algebra script?", .reply⟩
def casOutputComplete : Link := ⟨"casOutputComplete",
  "Is this result the anchored reply's computer algebra output, free of errors and showing the expected completion counts?"⟩
def quotesNumber : Atom := ⟨"quotesNumber",
  "Does this reply quote a number, a case count or a sampling grid from a computation?", .reply⟩
def readsSavedOutputOfNumber : Link := ⟨"readsSavedOutputOfNumber",
  "Is this a script reading the saved output the anchored reply's number comes from?"⟩
def statesCheckingTotal : Atom := ⟨"statesCheckingTotal",
  "Does this reply state a total, sum or comparison that checks a statement?", .reply⟩
def printsTotalAsOneLine : Link := ⟨"printsTotalAsOneLine",
  "Is this the result of one script run over the whole of one set of output, printing the anchored reply's total or comparison as one line?"⟩
def statesDistinctCount : Atom := ⟨"statesDistinctCount",
  "Does this reply state a count of distinct things?", .reply⟩
def printsDistinctKeyCount : Link := ⟨"printsDistinctKeyCount",
  "Is this a result printing the anchored reply's count as a count of distinct keys?"⟩

/-! Atoms: resource evidence and rented machines (438 to 459). -/

def treatsMissingCounterAsZero : Atom := ⟨"treatsMissingCounterAsZero",
  "Does this reply treat a missing or reset resource counter as zero?", .reply⟩
def sumsRamSwapPeaks : Atom := ⟨"sumsRamSwapPeaks",
  "Does this reply sum RAM and swap peaks as one simultaneous peak?", .reply⟩
def treatsSignalAsCause : Atom := ⟨"treatsSignalAsCause",
  "Does this reply treat low CPU use, pressure, memory events or I/O as proof of a cause?", .reply⟩
def addsOverlappingDurations : Atom := ⟨"addsOverlappingDurations",
  "Does this reply add overlapping pressure and wait durations into a partition of elapsed time?", .reply⟩
def statesLongRunCause : Atom := ⟨"statesLongRunCause",
  "Does this reply state the cause of a long-running job?", .reply⟩
def inspectsThatRun : Link := ⟨"inspectsThatRun",
  "Does this call inspect or trace the job whose cause the anchored reply states?"⟩
def bypassesTraceAccessFailure : Atom := ⟨"bypassesTraceAccessFailure",
  "Does this call work around an access failure met while tracing a job?", .call⟩
def slowToolWarning : Atom := ⟨"slowToolWarning",
  "Does this result carry a framework tool's warning that it is still running at one second?", .result⟩
def reportsSlowToolCause : Link := ⟨"reportsSlowToolCause",
  "Does this reply report the investigated cause of the anchored result's slow-tool warning?"⟩
def sshToRentedMachine : Atom := ⟨"sshToRentedMachine",
  "Does this call connect to a rented container?", .call⟩
def withinMinuteOfSsh : Link := ⟨"withinMinuteOfSsh",
  "Is this read of the delivered CPUs and RAM on the anchored call's container, within a minute of it?"⟩
def judgesCapacityFromNproc : Atom := ⟨"judgesCapacityFromNproc",
  "Does this reply state a rented container's CPUs or RAM from nproc or MemTotal?", .reply⟩
def claimsCpuQuota : Atom := ⟨"claimsCpuQuota",
  "Does this reply state the CPU quota a container enforces?", .reply⟩
def spinsMoreThreadsThanQuota : Link := ⟨"spinsMoreThreadsThanQuota",
  "Does this call spin more threads than the quota the anchored reply states allows?"⟩
def treatsPricePageAsPromise : Atom := ⟨"treatsPricePageAsPromise",
  "Does this reply treat a third-party price page as a promise of what will be delivered?", .reply⟩
def quotesCreateResponse : Link := ⟨"quotesCreateResponse",
  "Does this reply read back what the anchored create call's response says was delivered?"⟩
def blamesMachineCapacity : Atom := ⟨"blamesMachineCapacity",
  "Does this reply blame a machine's capacity for a result?", .reply⟩
def measuresAlone : Link := ⟨"measuresAlone",
  "Does this call measure the machine's capacity with nothing else running on it?"⟩
def testsSuspectedLimit : Link := ⟨"testsSuspectedLimit",
  "Does this call test directly the limit the anchored reply suspects?"⟩
def changesSeveralThings : Atom := ⟨"changesSeveralThings",
  "Does this call run a measurement changing more than one thing since the last one?", .call⟩
def judgesProgressByCpu : Atom := ⟨"judgesProgressByCpu",
  "Does this reply judge a job's progress by its CPU use?", .reply⟩
def reportsJobProgress : Atom := ⟨"reportsJobProgress",
  "Does this reply report a job's progress?", .reply⟩
def citesOutputAgeAndCounter : Atom := ⟨"citesOutputAgeAndCounter",
  "Does this reply rest the progress on the output's age and a work counter?", .reply⟩
def callsSilentJobWorking : Atom := ⟨"callsSilentJobWorking",
  "Does this reply call a job that has gone silent working?", .reply⟩
def statesResourceUse : Atom := ⟨"statesResourceUse",
  "Does this reply state a job's or a machine's real GPU or CPU use?", .reply⟩
def launchesRentedJob : Atom := ⟨"launchesRentedJob",
  "Does this call start a job on a rented machine?", .call⟩
def readsEarlierPeakMemory : Link := ⟨"readsEarlierPeakMemory",
  "Does this call read the peak GPU memory and RAM of an earlier run of the anchored call's job?"⟩
def readsFreeMemory : Link := ⟨"readsFreeMemory",
  "Does this call read the current free GPU memory and RAM for the anchored call's job?"⟩
def pinsToHoldingCard : Atom := ⟨"pinsToHoldingCard",
  "Does this call pin the job to a card that holds its peak memory?", .call⟩
def exceedsContainerRam : Atom := ⟨"exceedsContainerRam",
  "Does this call start a job alongside running ones whose combined RAM exceeds the container's, rather than chaining it?", .call⟩
def statesRentedJobState : Atom := ⟨"statesRentedJobState",
  "Does this reply state a rented-machine job's state?", .reply⟩
def readsThatJobStatus : Link := ⟨"readsThatJobStatus",
  "Does this call read the status of the job the anchored reply states?"⟩
def compilesLeanHOnFp16Host : Atom := ⟨"compilesLeanHOnFp16Host",
  "Does this build compile lean.h on a host with AVX-512 FP16?", .call⟩
def statesDownloadProgress : Atom := ⟨"statesDownloadProgress",
  "Does this reply state a download's progress?", .reply⟩
def judgesByDu : Atom := ⟨"judgesByDu",
  "Does this reply judge that progress by du?", .reply⟩
def coversSameDirectory : Link := ⟨"coversSameDirectory",
  "Does this hf download run over the directory the anchored aria2c download wrote?"⟩
def reportsWhatItPrinted : Link := ⟨"reportsWhatItPrinted",
  "Does this reply report what the anchored hf download printed?"⟩
def secondWriterOfFile : Atom := ⟨"secondWriterOfFile",
  "Does this call start a process writing a file another running process also writes?", .call⟩
def downloadsFromHub : Atom := ⟨"downloadsFromHub",
  "Does this download fetch files from the Hugging Face Hub?", .call⟩
def namesEachOutputFile : Atom := ⟨"namesEachOutputFile",
  "Does this download give each file's name (out= in aria2c's input file)?", .call⟩
def givesCapabilityInventory : Atom := ⟨"givesCapabilityInventory",
  "Does this reply give an inventory of the capabilities available to the agent?", .reply⟩
def coversHarnessContracts : Atom := ⟨"coversHarnessContracts",
  "Does that inventory cover the active harness's supplied tool contracts as well as installed CLI and API interfaces?", .reply⟩
def declaresPrimitiveAbsent : Atom := ⟨"declaresPrimitiveAbsent",
  "Does this reply declare a background, notification or lifecycle capability absent, or propose another controller for it?", .reply⟩
def testsExistingPrimitive : Link := ⟨"testsExistingPrimitive",
  "Does this call test the existing primitive for the capability the anchored reply declares absent?"⟩
def leavesOnlyCopyInIgnored : Atom := ⟨"leavesOnlyCopyInIgnored",
  "Does this commit or checkpoint leave a result whose only copy is in ignored logs, tmp or runtime folders?", .call⟩
def truncatesSavedOutput : Atom := ⟨"truncatesSavedOutput",
  "Does this call silently truncate saved computation output or impose an output-size cutoff?", .call⟩
def unstoppableJobRunning : Atom := ⟨"unstoppableJobRunning",
  "Is a job the agent cannot stop running when this reply is sent?", .reply⟩
def namesJobHoldings : Atom := ⟨"namesJobHoldings",
  "Does this reply stop and tell the user what that job holds (card, memory, what waits)?", .reply⟩
def givesStopCommand : Atom := ⟨"givesStopCommand",
  "Does this reply give the one command that stops that job?", .reply⟩

/-! Atoms: Lean and the design skills (460 to 489). -/

def treatsProofAsCertifying : Atom := ⟨"treatsProofAsCertifying",
  "Does this reply treat a proof as certifying that its statement says what was required?", .reply⟩
def startsProof : Atom := ⟨"startsProof",
  "Does this Lean edit start proving a statement?", .edit⟩
def checksStatementServes : Link := ⟨"checksStatementServes",
  "Does this reply check that the statement the anchored edit proves serves its requirement?"⟩
def addsNewStatement : Atom := ⟨"addsNewStatement",
  "Does this Lean edit add a new statement with hypotheses?", .edit⟩
def includesHypothesisWitness : Atom := ⟨"includesHypothesisWitness",
  "Does this edit show the new statement's hypotheses can hold, by a witness or a theorem producing one?", .edit⟩
def witnessesHypotheses : Link := ⟨"witnessesHypotheses",
  "Does this edit show that the anchored edit's new statement's hypotheses can hold?"⟩
def presentsStatement : Atom := ⟨"presentsStatement",
  "Does this reply present a statement as meeting a requirement?", .reply⟩
def recordsUndetermined : Atom := ⟨"recordsUndetermined",
  "Does this reply state, or record as unproved, what the requirement says that the statement leaves undetermined?", .reply⟩
def approvesLeanChange : Atom := ⟨"approvesLeanChange",
  "Does this reply approve or sign off a Lean change?", .reply⟩
def printsTypesAndAxioms : Link := ⟨"printsTypesAndAxioms",
  "Does this call print the types and axioms of the theorems the anchored reply approves?"⟩
def readsUnvouchedCode : Link := ⟨"readsUnvouchedCode",
  "Does this read cover what the kernel does not vouch for in the anchored reply's change (definitions in statements, partial, unsafe, implemented_by, extern, axioms, code outside the proved core)?"⟩
def claimsProofFromSorryGoal : Atom := ⟨"claimsProofFromSorryGoal",
  "Does this reply treat an empty goal after sorry as a certified proof?", .reply⟩
def reliesOnStaleDiagnostics : Atom := ⟨"reliesOnStaleDiagnostics",
  "Does this reply rely on stale or partial Lean diagnostics?", .reply⟩
def reportsLeanDiagnostics : Atom := ⟨"reportsLeanDiagnostics",
  "Does this reply report Lean diagnostics?", .reply⟩
def saysCompletedOrTimedOut : Atom := ⟨"saysCompletedOrTimedOut",
  "Does this reply say whether those diagnostics completed or elaboration timed out?", .reply⟩
def scratchTacticSucceeded : Atom := ⟨"scratchTacticSucceeded",
  "Is this the result of a scratch or REPL tactic trial that succeeded?", .result⟩
def copiesThatTactic : Link := ⟨"copiesThatTactic",
  "Does this edit copy the anchored result's successful tactic into the real file?"⟩
def claimsTacticSucceeded : Atom := ⟨"claimsTacticSucceeded",
  "Does this reply claim a tactic proved a goal?", .reply⟩
def showsGoalsClosedNoBadAxiom : Link := ⟨"showsGoalsClosedNoBadAxiom",
  "Does this result show the anchored reply's tactic closes the required goals without an inadmissible axiom?"⟩
def altersRequestedStatement : Atom := ⟨"altersRequestedStatement",
  "Does this Lean edit change a statement the user or the task requested?", .edit⟩
def findsFalsePremise : Atom := ⟨"findsFalsePremise",
  "Does this reply report a false premise or a needed generalization of a requested statement?", .reply⟩
def recordsFalsePremise : Link := ⟨"recordsFalsePremise",
  "Does this plan edit record the anchored reply's false premise or generalization?"⟩
def reliesOnFileLevelCheck : Atom := ⟨"reliesOnFileLevelCheck",
  "Does this reply rely on a file-level Lean check?", .reply⟩
def editsImportedModule : Atom := ⟨"editsImportedModule",
  "Does this Lean edit change a module other modules import?", .edit⟩
def weakensAxiomOrSourceCheck : Atom := ⟨"weakensAxiomOrSourceCheck",
  "Does this edit remove or weaken an existing axiom or source check?", .edit⟩
def treatsLeanVerifyAsFidelity : Atom := ⟨"treatsLeanVerifyAsFidelity",
  "Does this reply treat lean_verify as establishing statement fidelity?", .reply⟩
def refactorsProof : Atom := ⟨"refactorsProof",
  "Does this Lean edit refactor or golf a proof?", .edit⟩
def inspectsTypeAndAxioms : Link := ⟨"inspectsTypeAndAxioms",
  "Does this call inspect the resulting type and axioms of the anchored edit's proof?"⟩
def readsRemovalAsNecessity : Atom := ⟨"readsRemovalAsNecessity",
  "Does this reply read a failed hypothesis-removal experiment as showing the assumption mathematically necessary?", .reply⟩
def reliesOnRemoteHit : Atom := ⟨"reliesOnRemoteHit",
  "Does this reply rely on a remote Lean search hit?", .reply⟩
def confirmsHitLocally : Link := ⟨"confirmsHitLocally",
  "Does this call confirm the anchored reply's remote search hit in the local toolchain?"⟩
def treatsEmptySearchAsAbsence : Atom := ⟨"treatsEmptySearchAsAbsence",
  "Does this reply treat an empty local search as proof of absence without the index status showing it was consulted?", .reply⟩
def claimsTransformationCorrect : Atom := ⟨"claimsTransformationCorrect",
  "Does this reply claim a transformation or rewrite correct?", .reply⟩
def establishesEachLaw : Link := ⟨"establishesEachLaw",
  "Does this call establish separately each law the anchored reply's transformation uses?"⟩
def showsSidesObservationallyEqual : Link := ⟨"showsSidesObservationallyEqual",
  "Does this call show both sides of the anchored reply's rewrite have the same observations under its preconditions?"⟩
def claimsImplementationPreserves : Atom := ⟨"claimsImplementationPreserves",
  "Does this reply claim a changed implementation preserves its specification's meaning?", .reply⟩
def showsPrimitivesAgree : Link := ⟨"showsPrimitivesAgree",
  "Does this call show the anchored reply's implementation interprets each primitive and composition as specified, identities and failures included?"⟩
def claimsStatefulEquivalence : Atom := ⟨"claimsStatefulEquivalence",
  "Does this reply claim two stateful implementations behave the same?", .reply⟩
def showsStepSimulation : Link := ⟨"showsStepSimulation",
  "Does this call relate the states and show each step preserves outputs and the relation, for the anchored reply's claim?"⟩
def restsOnFinalOutput : Atom := ⟨"restsOnFinalOutput",
  "Does this reply rest that claim on final-output agreement alone?", .reply⟩
def claimsNormalForm : Atom := ⟨"claimsNormalForm",
  "Does this reply claim a canonical normal form?", .reply⟩
def establishesTermination : Link := ⟨"establishesTermination",
  "Does this call establish termination of the anchored reply's normalization?"⟩
def establishesUniqueness : Link := ⟨"establishesUniqueness",
  "Does this call establish uniqueness of the anchored reply's normal form?"⟩
def guessesHiddenIndex : Atom := ⟨"guessesHiddenIndex",
  "Does this edit recover a hidden index by guessing from a non-injective result?", .edit⟩
def addsUncheckedEntrance : Atom := ⟨"addsUncheckedEntrance",
  "Does this edit let deserialization, conversion, mutation or generic construction make a validated type without its check?", .edit⟩
def readsUntrustedInput : Atom := ⟨"readsUntrustedInput",
  "Does this edit add code reading untrusted input?", .edit⟩
def parsesIntoTypedForm : Atom := ⟨"parsesIntoTypedForm",
  "Does that code parse and validate the input into the typed representation?", .edit⟩
def returnsExplicitError : Atom := ⟨"returnsExplicitError",
  "Does that code return an explicit error when validation fails?", .edit⟩
def treatsPhantomAsProof : Atom := ⟨"treatsPhantomAsProof",
  "Does this edit or reply treat a phantom marker alone as proof of validation or permission?", .any⟩
def usesPartialAsEvidence : Atom := ⟨"usesPartialAsEvidence",
  "Does this Lean edit use a partial definition's body or unsafe code as evidence for a theorem?", .edit⟩
def usesBeqAsEquality : Atom := ⟨"usesBeqAsEquality",
  "Does this Lean edit use a BEq result as logical equality?", .edit⟩
def provesBeqLawsHere : Atom := ⟨"provesBeqLawsHere",
  "Does this edit prove the equality laws of that BEq implementation?", .edit⟩
def provesThoseBeqLaws : Link := ⟨"provesThoseBeqLaws",
  "Does this edit prove the equality laws of the BEq the anchored edit uses as equality?"⟩
def reliesOnToolchainBehavior : Atom := ⟨"reliesOnToolchainBehavior",
  "Does this reply rely on a representation or elaboration behaviour of the toolchain?", .reply⟩
def checksActualToolchain : Link := ⟨"checksActualToolchain",
  "Does this call check that behaviour in the toolchain actually in use?"⟩
def addsDispatchCache : Atom := ⟨"addsDispatchCache",
  "Does this edit add or change a dispatch cache?", .edit⟩
def checksCacheKey : Link := ⟨"checksCacheKey",
  "Does this call check that the anchored edit's cache key keeps every distinction affecting handler selection?"⟩
def enablesRetriesOrParallel : Atom := ⟨"enablesRetriesOrParallel",
  "Does this edit allow retries, interleaving or parallel search?", .edit⟩
def definesBranchStateHere : Atom := ⟨"definesBranchStateHere",
  "Does this edit itself define branch-local state and effect handling?", .edit⟩
def definesBranchState : Link := ⟨"definesBranchState",
  "Does this edit define the branch-local state and effect handling the anchored edit's retries or search need?"⟩
def registrationOrderDecides : Atom := ⟨"registrationOrderDecides",
  "Does this edit let accidental registration order decide extensible dispatch?", .edit⟩

/-! Atoms: merge requests, messages and reviews (490 to 498, 515 to 527). -/

def statesWhatVerifiedHow : Atom := ⟨"statesWhatVerifiedHow",
  "Does this description's verification paragraph state exactly what was verified and how?", .call⟩
def namesUnverified : Atom := ⟨"namesUnverified",
  "Does that paragraph name anything not verified or unreachable?", .call⟩
def distinguishesConfidence : Atom := ⟨"distinguishesConfidence",
  "Does this description distinguish confidence levels (unit test, live confirmation, not verifiable locally)?", .call⟩
def partlyChecked : Atom := ⟨"partlyChecked",
  "Does this description describe a change only part of which was checked?", .call⟩
def saysUncheckedPartWhy : Atom := ⟨"saysUncheckedPartWhy",
  "Does it say exactly which part was not checked and why?", .call⟩
def hasCheckForOthers : Atom := ⟨"hasCheckForOthers",
  "Does this description hold a check only someone else can run?", .call⟩
def checkWordedWithCommand : Atom := ⟨"checkWordedWithCommand",
  "Is that check worded as what it needs, with the command?", .call⟩
def addressesPerson : Atom := ⟨"addressesPerson",
  "Does this description address a person?", .call⟩
def asksReviewerQuestion : Atom := ⟨"asksReviewerQuestion",
  "Does this description hold a question for the reviewer?", .call⟩
def mrHasApprovals : Atom := ⟨"mrHasApprovals",
  "Does this force-push go to a merge request that has approvals?", .call⟩
def readsResetSetting : Link := ⟨"readsResetSetting",
  "Does this call read whether the anchored push's project resets approvals on push?"⟩
def claimsApprovalsSurvive : Atom := ⟨"claimsApprovalsSurvive",
  "Does this reply claim a merge request's approvals survive a force-push?", .reply⟩
def viewsThatMr : Link := ⟨"viewsThatMr",
  "Does this call read back the merge request the anchored call opened (target branch, reviewer, description)?"⟩
def hasUnlinkedReference : Atom := ⟨"hasUnlinkedReference",
  "Does this edit or reply hold a reference the reader can open (a ticket, a schema, a page) without a link where it appears?", .any⟩
def draftsChatMessage : Atom := ⟨"draftsChatMessage",
  "Does this edit draft a chat message for the user to send?", .edit⟩
def sentencesCapitalized : Atom := ⟨"sentencesCapitalized",
  "Does every sentence of that draft start with a capital letter?", .edit⟩
def continuesAfterSplit : Atom := ⟨"continuesAfterSplit",
  "Does this rebase continue after splitting a commit?", .call⟩
def diffsSplitAgainstOriginal : Link := ⟨"diffsSplitAgainstOriginal",
  "Does this diff check that the anchored rebase's split reproduces the original tree?"⟩
def rebaseAppliesCutSpecs : Atom := ⟨"rebaseAppliesCutSpecs",
  "Does this rebase apply cut specs to split commits?", .call⟩
def dryRunsCutSpecs : Link := ⟨"dryRunsCutSpecs",
  "Does this call dry-run the anchored rebase's cut specs against the source commit's files?"⟩
def draftsReviewFact : Atom := ⟨"draftsReviewFact",
  "Does this edit write a review comment stating a fact?", .edit⟩
def ledgerRowChecksFact : Link := ⟨"ledgerRowChecksFact",
  "Does this ledger edit check the anchored comment's fact against the code, a render or a run?"⟩
def offersSubstandardReview : Atom := ⟨"offersSubstandardReview",
  "Does this reply offer a review of a colleague's change that skips checks the agent would make on its own branch?", .reply⟩
def offersConfigReview : Atom := ⟨"offersConfigReview",
  "Does this reply offer a review of a change to configuration?", .reply⟩
def rendersPerEnvironment : Link := ⟨"rendersPerEnvironment",
  "Does this call render the anchored review's configuration with the change's values for an environment it touches?"⟩
def diffsAgainstDeployed : Link := ⟨"diffsAgainstDeployed",
  "Does this call diff the rendered configuration against what is deployed, for the anchored review?"⟩
def checksSettingsAtRunTime : Link := ⟨"checksSettingsAtRunTime",
  "Does this call check that the anchored review's settings can do their job at run time (user, capabilities, security context)?"⟩
def offersPinReview : Atom := ⟨"offersPinReview",
  "Does this reply offer a review of a change to dependency pins?", .reply⟩
def comparesPinWithRunning : Link := ⟨"comparesPinWithRunning",
  "Does this call compare a pin of the anchored review's change with the version running now?"⟩
def checksImageHonoursLock : Link := ⟨"checksImageHonoursLock",
  "Does this call check the image build honours the lock file, for the anchored review?"⟩
def offersReview : Atom := ⟨"offersReview",
  "Does this reply offer a review of a colleague's change?", .reply⟩
def readsReliedContracts : Link := ⟨"readsReliedContracts",
  "Does this call read the contracts the anchored review's change relies on, at the version it uses?"⟩
def checksDependenciesInPlace : Link := ⟨"checksDependenciesInPlace",
  "Does this call check that what the anchored review's change depends on is in place (the release, the migrations, the runbook order)?"⟩
def offersImportReview : Atom := ⟨"offersImportReview",
  "Does this reply offer a review of a change importing a profile, chart or rule set?", .reply⟩
def listsWhatImportTurnsOn : Atom := ⟨"listsWhatImportTurnsOn",
  "Does this reply list what the import turns on in the target environment, above all what pages someone?", .reply⟩
def offersAlertRuleReview : Atom := ⟨"offersAlertRuleReview",
  "Does this reply offer a review of alert or recording rules?", .reply⟩
def testsRulesOnEdgeSeries : Link := ⟨"testsRulesOnEdgeSeries",
  "Does this run test the anchored review's rules against series covering counter resets, missing series, scrape gaps, long outages and other clusters?"⟩
def offersAccessReview : Atom := ⟨"offersAccessReview",
  "Does this reply offer a review of a change that opens access to something?", .reply⟩
def saysWhoCanReach : Atom := ⟨"saysWhoCanReach",
  "Does this reply say who can reach what the change opens, and with what credential?", .reply⟩
def rechecksMrDiff : Link := ⟨"rechecksMrDiff",
  "Does this call re-check the merge request's diff for the anchored comment, after it was drafted?"⟩
def rechecksLiveFacts : Link := ⟨"rechecksLiveFacts",
  "Does this call re-check a live fact the anchored comment states, after it was drafted?"⟩

/-! Atoms: paper writing (499 to 514). -/

def addsWorkedExample : Atom := ⟨"addsWorkedExample",
  "Does this edit add an example or counterexample to a manuscript?", .edit⟩
def verifiesExampleAgainstStatement : Link := ⟨"verifiesExampleAgainstStatement",
  "Does this call verify the anchored edit's example against the actual statement?"⟩
def treatsPictureAsProof : Atom := ⟨"treatsPictureAsProof",
  "Does this edit present a picture or analogy as a proof?", .edit⟩
def dropsMathConvention : Atom := ⟨"dropsMathConvention",
  "Does this edit drop or change a quantifier, field or characteristic assumption, encoding, degree convention, parameter range, joint cost or bound-versus-equality distinction?", .edit⟩
def editsMathStatement : Atom := ⟨"editsMathStatement",
  "Does this edit change a mathematical statement, argument, definition or correction?", .edit⟩
def readsEditedPassage : Link := ⟨"readsEditedPassage",
  "Does this read open the passage the anchored edit changes?"⟩
def handsOffManuscript : Atom := ⟨"handsOffManuscript",
  "Does this reply hand off changes to a manuscript?", .reply⟩
def separatesSubstanceFromPresentation : Atom := ⟨"separatesSubstanceFromPresentation",
  "Does this reply separate substantive mathematical corrections from presentation changes?", .reply⟩
def correctsMathStatement : Atom := ⟨"correctsMathStatement",
  "Does this edit correct a mathematical statement?", .edit⟩
def correctsProofToo : Atom := ⟨"correctsProofToo",
  "Does this edit correct the statement's proof with it?", .edit⟩
def checksNearbyConstructions : Link := ⟨"checksNearbyConstructions",
  "Does this call verify that constructions near the anchored edit's correction keep their advertised properties?"⟩
def onlyRemovesWarning : Atom := ⟨"onlyRemovesWarning",
  "Does this edit resolve a defect by only removing its warning?", .edit⟩
def reliesOnBibliographicFact : Atom := ⟨"reliesOnBibliographicFact",
  "Does this edit or reply rely on a bibliographic fact or a cited result's hypotheses?", .any⟩
def readsSourceOfFact : Link := ⟨"readsSourceOfFact",
  "Does this call read the source of the anchored step's bibliographic fact or cited hypotheses?"⟩
def describesPriorWork : Atom := ⟨"describesPriorWork",
  "Does this edit describe a result's relation to prior work?", .edit⟩
def distinguishesContribution : Atom := ⟨"distinguishesContribution",
  "Does it describe the actual comparison and distinguish inherited result, new proof, new formulation and new conclusion?", .edit⟩
def checksExampleIntermediates : Link := ⟨"checksExampleIntermediates",
  "Does this call check the anchored edit's example's intermediate costs, hypotheses and exceptional cases?"⟩
def manufacturesExcludedExample : Atom := ⟨"manufacturesExcludedExample",
  "Does this edit present an example of an object a theorem rules out?", .edit⟩
def hidesFailedCondition : Atom := ⟨"hidesFailedCondition",
  "Does this edit hide a failed condition in an abbreviated edge?", .edit⟩
def appliesDegreeBound : Atom := ⟨"appliesDegreeBound",
  "Does this edit apply a degree-lowering bound?", .edit⟩
def coversWholeExpression : Atom := ⟨"coversWholeExpression",
  "Does it apply the bound to the whole transformed expression, generator multiples included?", .edit⟩
def fixesParameterChoice : Atom := ⟨"fixesParameterChoice",
  "Does this edit fix a final parameter choice?", .edit⟩
def checksAllRequirements : Atom := ⟨"checksAllRequirements",
  "Does it check that choice against all simultaneous requirements and boundary cases?", .edit⟩
def unsupportedClaimOfSupport : Atom := ⟨"unsupportedClaimOfSupport",
  "Does this edit or reply claim novelty, authorship, personal checking or empirical evidence without support?", .any⟩
def editsPublishableManuscript : Atom := ⟨"editsPublishableManuscript",
  "Does this edit prepare a manuscript for publication?", .edit⟩
def acknowledgesAi : Atom := ⟨"acknowledgesAi",
  "Does the manuscript identify material AI contributions in a concise acknowledgment within it?", .edit⟩
def treatsNoGapReviewAsCertification : Atom := ⟨"treatsNoGapReviewAsCertification",
  "Does this reply treat a review finding no gap as certifying the whole paper?", .reply⟩
def reopensProofForExposition : Atom := ⟨"reopensProofForExposition",
  "Does this edit reopen a proof or formal verification merely to improve exposition?", .edit⟩

/-! Atoms: the task protocol (528 to 560). -/

def taskListsExtraSkill : Atom := ⟨"taskListsExtraSkill",
  "Does the task in progress list a skill beyond the defaults?", .edit⟩
def loadsTaskListedSkill : Link := ⟨"loadsTaskListedSkill",
  "Does this call load a skill the task in progress at the anchored edit lists?"⟩
def followsCoverLetterFormat : Atom := ⟨"followsCoverLetterFormat",
  "Does this description follow the mr-cover-letter skill's format?", .call⟩
def slugIsTicketOnly : Atom := ⟨"slugIsTicketOnly",
  "Is this new task's slug a ticket number alone, or one not descriptive and kebab-case?", .call⟩
def createsTaskDirectory : Atom := ⟨"createsTaskDirectory",
  "Does this edit create the first file of a new task's directory?", .edit⟩
def createsThatTask : Link := ⟨"createsThatTask",
  "Does this call create the task whose directory the anchored edit writes?"⟩
def keepsTheoryThenPath : Atom := ⟨"keepsTheoryThenPath",
  "Does this plan edit leave the plan edited in place, with Theory building first and Path second?", .edit⟩
def writesPlanOrCode : Atom := ⟨"writesPlanOrCode",
  "Does this edit write a delegated task's plan steps or code?", .edit⟩
def recordsTaskTheory : Link := ⟨"recordsTaskTheory",
  "Does this plan edit record the theory (questions and investigation) of the anchored edit's task?"⟩
def recordsTheory : Atom := ⟨"recordsTheory",
  "Does this plan edit record the task's theory?", .edit⟩
def theoryAsQuestionsAhead : Atom := ⟨"theoryAsQuestionsAhead",
  "Does it record the theory as questions with answers, as its own section ahead of the plan?", .edit⟩
def asksWhatResearchAnswers : Atom := ⟨"asksWhatResearchAnswers",
  "Does this reply ask the user something the agent's own research could answer?", .reply⟩
def addsResolvedEntry : Atom := ⟨"addsResolvedEntry",
  "Does this plan edit add an entry to Resolved?", .edit⟩
def openedAsQuestionFirst : Link := ⟨"openedAsQuestionFirst",
  "Does this plan edit write the anchored edit's entry as an open question before it was investigated?"⟩
def findsAnswer : Atom := ⟨"findsAnswer",
  "Does this reply find the answer to an open theory question?", .reply⟩
def movesToResolved : Link := ⟨"movesToResolved",
  "Does this plan edit move the anchored reply's question into Resolved with its answer?"⟩
def prunesResolved : Atom := ⟨"prunesResolved",
  "Does this plan edit prune or consolidate entries of Resolved?", .edit⟩
def resolvedEntryMalformed : Atom := ⟨"resolvedEntryMalformed",
  "Does this plan edit add a Resolved entry or decision not written as a question-and-answer pair with the question first and bold?", .edit⟩
def mixesOpenAndResolved : Atom := ⟨"mixesOpenAndResolved",
  "Does this plan edit put open and resolved questions together?", .edit⟩
def leavesStaleStatement : Atom := ⟨"leavesStaleStatement",
  "Does this plan edit leave a stale statement unrewritten, appending a correction beside it?", .edit⟩
def entryStartsWithQuestion : Atom := ⟨"entryStartsWithQuestion",
  "Does the entry this edit adds start with its question, even if answered at once?", .edit⟩
def addsIncidentalFinding : Atom := ⟨"addsIncidentalFinding",
  "Does this plan edit add an incidental or unasked finding?", .edit⟩
def placesUnderAnsweredQuestion : Atom := ⟨"placesUnderAnsweredQuestion",
  "Does it place the finding under the question it answers?", .edit⟩
def rewordsMovedQuestion : Atom := ⟨"rewordsMovedQuestion",
  "Does this plan edit reword a question it moves?", .edit⟩
def taskRunResult : Atom := ⟨"taskRunResult",
  "Is this the result of a run made for the task's theory or Path?", .result⟩
def entersRunResult : Atom := ⟨"entersRunResult",
  "Does this plan edit enter a run's result into Theory building?", .edit⟩
def requestFulfilledOrDropped : Atom := ⟨"requestFulfilledOrDropped",
  "Does this call resolve a request item that is fulfilled or dropped, not to replace its text with a new item?", .call⟩
def movesRequestSubstance : Link := ⟨"movesRequestSubstance",
  "Does this plan edit move the substance of the request the anchored call resolves?"⟩
def reusesItemNumber : Atom := ⟨"reusesItemNumber",
  "Does this request add reuse an item number?", .call⟩
def removesRequestContent : Atom := ⟨"removesRequestContent",
  "Does this call remove fulfilled, decided, summarized or tracked content from an open request?", .call⟩
def statesWhatBlocks : Atom := ⟨"statesWhatBlocks",
  "Does this blocked status come with a required request or a task waited for, stating what blocks it?", .call⟩
def evidenceOutsideTaskDir : Atom := ⟨"evidenceOutsideTaskDir",
  "Does this commit or checkpoint leave evidence the task produced uncommitted or outside its tasks directory?", .call⟩
def appendsCycleEntry : Atom := ⟨"appendsCycleEntry",
  "Does this checkpoint append a dated notebook entry for the cycle, a no-progress cycle included?", .call⟩
def entryHasRequiredParts : Atom := ⟨"entryHasRequiredParts",
  "Does that entry have a stable content-derived anchor, a descriptive title, the task ID label, a status from the four and a claim declaration?", .call⟩
def writesTaskLog : Atom := ⟨"writesTaskLog",
  "Does this edit write a per-task log or a sequential cycle counter?", .edit⟩
def writesLockedTask : Atom := ⟨"writesLockedTask",
  "Does this edit write to a task whose lock another live session holds?", .edit⟩
def reportsTaskLock : Atom := ⟨"reportsTaskLock",
  "Does this result or refusal report that another live session holds the task's lock?", .any⟩
def tellsUserOfLock : Link := ⟨"tellsUserOfLock",
  "Does this reply tell the user about the anchored lock?"⟩
def worksOnOtherTask : Link := ⟨"worksOnOtherTask",
  "Does this edit work on a task other than the one the anchored lock holds?"⟩
def startsOtherTask : Atom := ⟨"startsOtherTask",
  "Does this edit move work to another task than the one in progress?", .edit⟩
def recordsNameWrongTask : Atom := ⟨"recordsNameWrongTask",
  "After this checkpoint, does a record say a task other than the one being worked on is being worked on?", .call⟩
def trajectoryNamesOtherTask : Atom := ⟨"trajectoryNamesOtherTask",
  "Does this trajectory-hook report name a task other than the one being worked on?", .any⟩
def correctsStaleRecords : Link := ⟨"correctsStaleRecords",
  "Does this edit correct the stale records the anchored report shows?"⟩
def holdsFinishedWork : Atom := ⟨"holdsFinishedWork",
  "Does this notebook edit leave Where we stand holding finished work or a closed task?", .edit⟩
def openTaskLacksParagraph : Atom := ⟨"openTaskLacksParagraph",
  "After this checkpoint, does an open task past its first checkpoint lack its Where we stand paragraph?", .call⟩
def statusSaysWhatCycleLeft : Atom := ⟨"statusSaysWhatCycleLeft",
  "Do the task's status, status note and paragraph after this checkpoint say what the cycle left?", .call⟩
def closesFirstCycle : Atom := ⟨"closesFirstCycle",
  "Does this checkpoint close a task's first cycle?", .call⟩
def restatesTask : Link := ⟨"restatesTask",
  "Does this plan edit restate the task the anchored checkpoint's first cycle works?"⟩
def checksStartedElsewhere : Link := ⟨"checksStartedElsewhere",
  "Does this call check whether the anchored checkpoint's task was started elsewhere (a branch, an open MR, related recent work)?"⟩
def entryStatusStarted : Atom := ⟨"entryStatusStarted",
  "Does the entry this checkpoint appends have the status task started?", .call⟩
def asksWhatBlocksNothing : Atom := ⟨"asksWhatBlocksNothing",
  "Does this reply ask the user something whose answer blocks nothing?", .reply⟩
def writesFirstPathSteps : Atom := ⟨"writesFirstPathSteps",
  "Does this plan edit give the Path its first steps?", .edit⟩
def readsWhatTaskTouches : Link := ⟨"readsWhatTaskTouches",
  "Does this read investigate what the anchored edit's task touches?"⟩
def settlesUsersScope : Atom := ⟨"settlesUsersScope",
  "Does this plan edit settle a scope question the task can't be scoped without, unasked of the user?", .edit⟩
def userAnswersQuestion : Atom := ⟨"userAnswersQuestion",
  "Does this message from the user answer an open theory question?", .user⟩
def recordsAnswerPair : Link := ⟨"recordsAnswerPair",
  "Does this plan edit move the anchored message's answer into Resolved as its pair?"⟩
def stepsConcreteOrdered : Atom := ⟨"stepsConcreteOrdered",
  "Are the Path steps this edit writes concrete and ordered, provisional where they depend on an earlier finding?", .edit⟩
def theoryStableHere : Atom := ⟨"theoryStableHere",
  "Was the theory stable (no open question, the last reread changing nothing) when this edit was made?", .edit⟩
def stableSucceeded : Link := ⟨"stableSucceeded",
  "Did this stable check succeed for the anchored edit's task?"⟩
def quotesUserOrder : Atom := ⟨"quotesUserOrder",
  "Does the Path quote the user setting another order, with (the user, DATE)?", .edit⟩
def userStatesPlan : Atom := ⟨"userStatesPlan",
  "Does this message from the user state a plan for the task?", .user⟩
def entersUserPlan : Link := ⟨"entersUserPlan",
  "Does this plan edit enter the anchored message's plan into the Path?"⟩
def queuesTaskRun : Atom := ⟨"queuesTaskRun",
  "Does this call queue a run for a task?", .call⟩
def namesPathStep : Atom := ⟨"namesPathStep",
  "Does that run name the Path step it serves?", .call⟩
def implementsReplacingDecision : Atom := ⟨"implementsReplacingDecision",
  "Is this edit the first implementing a decision that replaces a design?", .edit⟩
def checklistsDecision : Link := ⟨"checklistsDecision",
  "Does this plan edit put the decision the anchored edit implements through the reread checklist?"⟩

/-! Rules 421 to 437: numerical verification and computation output. -/

/-- Rule 421: a numerical check matches the claim's conventions and can falsify it. -/
def numericalCheckMatchesClaim : Rule where
  number := 421
  keyword := .must
  domain := .mathematics
  formula := ev editing ∧ₗ atom writesNumericalCheck ⟹
    atom matchesConventions ∧ₗ atom checkCanFalsify

/-- Rule 422: a finite instance's outcome says unsatisfiable or satisfiable finite domain. -/
def instanceKindStated : Rule where
  number := 422
  keyword := .must
  domain := .mathematics
  formula := ev reply ∧ₗ atom reportsInstanceResult ⟹ atom statesInstanceKind

/-- Rule 423: before coding a check, in the same cycle, its nonvacuity plan. -/
def nonvacuityBeforeCoding : Rule where
  number := 423
  keyword := .must
  domain := .mathematics
  formula := ev editing ∧ₗ atom writesNumericalCheck ⟹
    inCycle (ev reply ∧ₗ link statesSmallestParameters) ∧ₗ inCycle (ev reply ∧ₗ link countsPredictions) ∧ₗ
    inCycle (ev reply ∧ₗ link comparesUnconditionalBounds) ∧ₗ inCycle (ev reply ∧ₗ link verifiesHypotheses)

/-- Rule 424: an entry registering a finite check gives its nonvacuity count. -/
def nonvacuityCountRecorded : Rule where
  number := 424
  keyword := .must
  domain := .mathematics
  formula := ev notebookEdit ∧ₗ atom registersFiniteCheck ⟹ atom hasNonvacuityCount

/-- Rule 425: no reading of failures below the nonvacuous threshold; outcomes by size. -/
def noSubThresholdReading : Rule where
  number := 425
  keyword := .mustNot
  domain := .mathematics
  formula := never (ev reply ∧ₗ atom interpretsSubThresholdFailure) ∧ₗ
    (ev reply ∧ₗ atom reportsFiniteOutcomes ⟹ atom bySubInstanceSize)

/-- Rule 426: a bound is tested on extremal examples and its success weighed against the goal. -/
def boundOnExtremals : Rule where
  number := 426
  keyword := .must
  domain := .mathematics
  formula := ev reply ∧ₗ atom reportsBoundTested ⟹
    once (ev scriptRun ∧ₗ link testsExtremalExamples) ∧ₗ atom comparesWithGoalNeed

/-- Rule 427: a check computes the statement's own quantity, documents and asserts it. -/
def ownQuantityComputed : Rule where
  number := 427
  keyword := .must
  domain := .mathematics
  formula := ev editing ∧ₗ atom writesNumericalCheck ⟹
    atom computesOwnQuantity ∧ₗ atom docstringStatesStatement ∧ₗ atom generatesValidInputs

/-- Rule 428: new runs told apart from archived results. -/
def newRunsDistinguished : Rule where
  number := 428
  keyword := .must
  domain := .mathematics
  formula := ev reply ∧ₗ atom citesRunResults ⟹ atom saysNewOrArchived

/-- Rule 429: a kernel's prime is no characteristic hypothesis; small characteristics need proof. -/
def primeIsNoHypothesis : Rule where
  number := 429
  keyword := .mustNot
  domain := .mathematics
  formula := never (ev reply ∧ₗ atom treatsPrimeAsHypothesis) ∧ₗ
    (ev reply ∧ₗ atom claimsSmallCharacteristic ⟹ atom citesPerCharacteristicProof)

/-- Rule 430: a lifted certificate's scope stated, exceptional primes only when computed. -/
def certificateScopeStated : Rule where
  number := 430
  keyword := .must
  domain := .mathematics
  formula := ev reply ∧ₗ atom reportsLiftedCertificate ⟹
    atom statesCertificateScope ∧ₗ ¬ₗ atom namesUncomputedPrimes

/-- Rule 431: PC degree by exact closure with a monotonicity control, never a truncated basis. -/
def exactPcDegree : Rule where
  number := 431
  keyword := .mustNot
  domain := .mathematics
  formula := ev editing ∧ₗ atom measuresPcDegree ⟹
    ¬ₗ atom usesTruncatedBasis ∧ₗ atom usesExactClosure ∧ₗ atom checksMonotonicity

/-- Rule 432: a kernel validated on small cases and a second library before scaling. -/
def kernelValidatedFirst : Rule where
  number := 432
  keyword := .must
  domain := .mathematics
  formula := ev scriptRun ∧ₗ atom runsKernelAtScale ⟹
    once (ev scriptRun ∧ₗ link validatesAgainstReference) ∧ₗ
    once (ev scriptRun ∧ₗ link checksRanksWithSecondLibrary)

/-- Rule 433: foreign-function argument types declared. -/
def foreignTypesDeclared : Rule where
  number := 433
  keyword := .must
  domain := .mathematics
  formula := ev editing ∧ₗ atom callsForeignFunction ⟹ atom declaresArgumentTypes

/-- Rule 434: computer algebra output relied on is error-free with its completion counts. -/
def casOutputChecked : Rule where
  number := 434
  keyword := .must
  domain := .mathematics
  formula := ev reply ∧ₗ atom reliesOnCasOutput ⟹ once (ev anyResult ∧ₗ link casOutputComplete)

/-- Rule 435: a quoted number comes from saved output read by a script. -/
def numbersFromSavedOutput : Rule where
  number := 435
  keyword := .must
  domain := .mathematics
  formula := ev reply ∧ₗ atom quotesNumber ⟹ once (ev scriptRun ∧ₗ link readsSavedOutputOfNumber)

/-- Rule 436: a checking total is one run's one line. -/
def totalInOneRun : Rule where
  number := 436
  keyword := .must
  domain := .mathematics
  formula := ev reply ∧ₗ atom statesCheckingTotal ⟹ once (ev anyResult ∧ₗ link printsTotalAsOneLine)

/-- Rule 437: a distinct count printed as a count of distinct keys. -/
def distinctKeysCounted : Rule where
  number := 437
  keyword := .must
  domain := .mathematics
  formula := ev reply ∧ₗ atom statesDistinctCount ⟹ once (ev anyResult ∧ₗ link printsDistinctKeyCount)

/-! Rules 438 to 459: resource evidence and rented machines. -/

/-- Rule 438: missing counters unknown, RAM and swap peaks never summed. -/
def countersUnknownNotZero : Rule where
  number := 438
  keyword := .must
  domain := .mathematics
  formula := never (ev reply ∧ₗ atom treatsMissingCounterAsZero) ∧ₗ never (ev reply ∧ₗ atom sumsRamSwapPeaks)

/-- Rule 439: resource signals prove no cause, and overlapping durations don't partition time. -/
def signalsAreNoCause : Rule where
  number := 439
  keyword := .mustNot
  domain := .mathematics
  formula := never (ev reply ∧ₗ atom treatsSignalAsCause) ∧ₗ
    never (ev reply ∧ₗ atom addsOverlappingDurations)

/-- Rule 440: a long run's cause from the inspector or a trace. -/
def longRunCauseInspected : Rule where
  number := 440
  keyword := .mustNot
  domain := .mathematics
  formula := ev reply ∧ₗ atom statesLongRunCause ⟹ once (ev jobInspection ∧ₗ link inspectsThatRun)

/-- Rule 441: no bypassed access failure while tracing. -/
def noTraceBypass : Rule where
  number := 441
  keyword := .mustNot
  domain := .mathematics
  formula := never (ev toolCall ∧ₗ atom bypassesTraceAccessFailure)

/-- Rule 442: a slow-tool warning is investigated and its cause reported. -/
def slowToolInvestigated : Rule where
  number := 442
  keyword := .must
  domain := .mathematics
  formula := ev anyResult ∧ₗ atom slowToolWarning ⟹ eventually (ev reply ∧ₗ link reportsSlowToolCause)

/-- Rule 443: a rented container's limits read from cgroups within a minute of the first ssh. -/
def deliveredLimitsRead : Rule where
  number := 443
  keyword := .must
  domain := .softwareEngineering
  formula := (ev ssh ∧ₗ atom sshToRentedMachine ∧ₗ ¬ₗ once (ev ssh ∧ₗ atom sshToRentedMachine) ⟹
      eventually (ev cgroupLimitRead ∧ₗ link withinMinuteOfSsh)) ∧ₗ
    never (ev reply ∧ₗ atom judgesCapacityFromNproc)

/-- Rule 444: a CPU quota proved under load from cpuacct.usage and cpu.stat. -/
def quotaProvedUnderLoad : Rule where
  number := 444
  keyword := .must
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom claimsCpuQuota ⟹
    once (ev toolCall ∧ₗ link spinsMoreThreadsThanQuota) ∧ₗ once (ev readsCpuacctUsage) ∧ₗ
    once (ev readsCpuStat)

/-- Rule 445: no price page taken as a promise; the create response read back. -/
def createResponseRead : Rule where
  number := 445
  keyword := .mustNot
  domain := .softwareEngineering
  formula := never (ev reply ∧ₗ atom treatsPricePageAsPromise) ∧ₗ
    (ev podCreate ⟹ eventually (ev reply ∧ₗ link quotesCreateResponse))

/-- Rule 446: capacity measured alone, one change per measurement, a suspected limit tested. -/
def measureAloneBeforeBlame : Rule where
  number := 446
  keyword := .must
  domain := .softwareEngineering
  formula := (ev reply ∧ₗ atom blamesMachineCapacity ⟹
      once (ev toolCall ∧ₗ link measuresAlone) ∧ₗ once (ev toolCall ∧ₗ link testsSuspectedLimit)) ∧ₗ
    never (ev toolCall ∧ₗ atom changesSeveralThings)

/-- Rule 447: progress by output age and a work counter; a silent job reported silent. -/
def progressByOutput : Rule where
  number := 447
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev reply ∧ₗ atom judgesProgressByCpu) ∧ₗ
    (ev reply ∧ₗ atom reportsJobProgress ⟹ atom citesOutputAgeAndCounter) ∧ₗ
    never (ev reply ∧ₗ atom callsSilentJobWorking)

/-- Rule 448: real resource use from nvidia-smi and two readings of cpuacct.usage. -/
def realUseRead : Rule where
  number := 448
  keyword := .must
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom statesResourceUse ⟹
    once (ev nvidiaSmi) ∧ₗ once (ev readsCpuacctUsage ∧ₗ once (ev readsCpuacctUsage))

/-- Rule 449: a job placed by its measured memory, jobs exceeding the RAM chained. -/
def placeByMemory : Rule where
  number := 449
  keyword := .must
  domain := .softwareEngineering
  formula := (ev toolCall ∧ₗ atom launchesRentedJob ⟹
      once (ev toolCall ∧ₗ link readsEarlierPeakMemory) ∧ₗ once (ev toolCall ∧ₗ link readsFreeMemory) ∧ₗ
      atom pinsToHoldingCard) ∧ₗ
    never (ev toolCall ∧ₗ atom exceedsContainerRam)

/-- Rule 450: a rented job's state from a status read since the last reply. -/
def stateFromPodStatus : Rule where
  number := 450
  keyword := .must
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom statesRentedJobState ⟹
    since (ev podStatusRead ∧ₗ link readsThatJobStatus) (ev reply)

/-- Rule 451: the host checked before a native build; lean.h on FP16 hosts without FP16. -/
def hostBeforeNativeBuild : Rule where
  number := 451
  keyword := .must
  domain := .softwareEngineering
  formula := ev marchNativeBuild ⟹
    once (ev hostCpuCheck) ∧ₗ (atom compilesLeanHOnFp16Host ⟹ ev disablesAvx512Fp16)

/-- Rule 452: download progress from .aria2 files and the interface counter, never du. -/
def downloadProgressRead : Rule where
  number := 452
  keyword := .must
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom statesDownloadProgress ⟹
    once (ev aria2FilesListed) ∧ₗ once (ev interfaceBytesRead) ∧ₗ ¬ₗ atom judgesByDu

/-- Rule 453: hf download over an aria2c download's directory, and its output reported. -/
def hfDownloadCompletes : Rule where
  number := 453
  keyword := .must
  domain := .softwareEngineering
  formula := (ev aria2Download ⟹ eventually (ev hfDownload ∧ₗ link coversSameDirectory)) ∧ₗ
    (ev hfDownload ∧ₗ once (ev aria2Download) ⟹ eventually (ev reply ∧ₗ link reportsWhatItPrinted))

/-- Rule 454: no two processes writing one file. -/
def oneWriterPerFile : Rule where
  number := 454
  keyword := .mustNot
  domain := .softwareEngineering
  formula := never (ev toolCall ∧ₗ atom secondWriterOfFile)

/-- Rule 455: a Hub download names each file. -/
def hubFilesNamed : Rule where
  number := 455
  keyword := .must
  domain := .softwareEngineering
  formula := ev aria2Download ∧ₗ atom downloadsFromHub ⟹ atom namesEachOutputFile

/-- Rule 456: an inventory covers the harness's contracts; a primitive is tested before declared absent. -/
def inventoryCoversHarness : Rule where
  number := 456
  keyword := .must
  domain := .discipline
  formula := (ev reply ∧ₗ atom givesCapabilityInventory ⟹ atom coversHarnessContracts) ∧ₗ
    (ev reply ∧ₗ atom declaresPrimitiveAbsent ⟹ once (ev toolCall ∧ₗ link testsExistingPrimitive))

/-- Rule 457: no result's only copy left in ignored folders. -/
def resultsPromoted : Rule where
  number := 457
  keyword := .mustNot
  domain := .mathematics
  formula := never ((ev commit ∨ₗ ev cycleCheckpoint) ∧ₗ atom leavesOnlyCopyInIgnored)

/-- Rule 458: no truncated saved output, no output-size cutoff. -/
def noOutputTruncation : Rule where
  number := 458
  keyword := .mustNot
  domain := .mathematics
  formula := never (ev toolCall ∧ₗ atom truncatesSavedOutput)

/-- Rule 459: while an unstoppable job runs, each reply says what it holds and how to stop it. -/
def unstoppableJobReported : Rule where
  number := 459
  keyword := .should
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom unstoppableJobRunning ⟹
    (atom namesJobHoldings ∧ₗ atom givesStopCommand) ∨ₗ atom justified

/-! Rules 460 to 489: Lean and the design skills. -/

/-- Rule 460: a proof certifies no statement; the statement is checked against its requirement first. -/
def statementBeforeProof : Rule where
  number := 460
  keyword := .mustNot
  domain := .softwareEngineering
  formula := never (ev reply ∧ₗ atom treatsProofAsCertifying) ∧ₗ
    (ev leanEdit ∧ₗ atom startsProof ⟹ once (ev reply ∧ₗ link checksStatementServes))

/-- Rule 461: a new statement's hypotheses shown satisfiable. -/
def hypothesesWitnessed : Rule where
  number := 461
  keyword := .must
  domain := .softwareEngineering
  formula := ev leanEdit ∧ₗ atom addsNewStatement ⟹
    atom includesHypothesisWitness ∨ₗ eventually (ev leanEdit ∧ₗ link witnessesHypotheses)

/-- Rule 462: what the statement leaves undetermined is stated or recorded unproved. -/
def undeterminedRecorded : Rule where
  number := 462
  keyword := .must
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom presentsStatement ⟹ atom recordsUndetermined

/-- Rule 463: a Lean change reviewed from its printed types and axioms. -/
def reviewFromPrintedTypes : Rule where
  number := 463
  keyword := .must
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom approvesLeanChange ⟹ once (ev toolCall ∧ₗ link printsTypesAndAxioms)

/-- Rule 464: what the kernel doesn't vouch for is read as code. -/
def unvouchedCodeRead : Rule where
  number := 464
  keyword := .must
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom approvesLeanChange ⟹ once (ev reading ∧ₗ link readsUnvouchedCode)

/-- Rule 465: an empty goal after sorry is no proof. -/
def sorryGoalIsNoProof : Rule where
  number := 465
  keyword := .mustNot
  domain := .softwareEngineering
  formula := never (ev reply ∧ₗ atom claimsProofFromSorryGoal)

/-- Rule 466: no stale diagnostics relied on; completed told from timed out. -/
def freshDiagnostics : Rule where
  number := 466
  keyword := .mustNot
  domain := .softwareEngineering
  formula := never (ev reply ∧ₗ atom reliesOnStaleDiagnostics) ∧ₗ
    (ev reply ∧ₗ atom reportsLeanDiagnostics ⟹ atom saysCompletedOrTimedOut)

/-- Rule 467: a scratch tactic copied into the real file and rechecked there. -/
def scratchTacticCopied : Rule where
  number := 467
  keyword := .must
  domain := .softwareEngineering
  formula := ev anyResult ∧ₗ atom scratchTacticSucceeded ⟹
    eventually (ev leanEdit ∧ₗ link copiesThatTactic ∧ₗ eventually (ev leanCheck))

/-- Rule 468: a successful tactic closes the goals with no inadmissible axiom. -/
def tacticClosesCleanly : Rule where
  number := 468
  keyword := .must
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom claimsTacticSucceeded ⟹ once (ev anyResult ∧ₗ link showsGoalsClosedNoBadAxiom)

/-- Rule 469: the requested statement kept; a false premise recorded in the plan. -/
def requestedStatementKept : Rule where
  number := 469
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev leanEdit ∧ₗ atom altersRequestedStatement) ∧ₗ
    (ev reply ∧ₗ atom findsFalsePremise ⟹ eventually (ev planEdit ∧ₗ link recordsFalsePremise))

/-- Rule 470: changed imports built before a file-level check is relied on. -/
def importsBuiltFirst : Rule where
  number := 470
  keyword := .must
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom reliesOnFileLevelCheck ∧ₗ once (ev leanEdit ∧ₗ atom editsImportedModule) ⟹
    since (ev leanBuild) (ev leanEdit ∧ₗ atom editsImportedModule)

/-- Rule 471: axiom and source checks kept; lean_verify is no fidelity check. -/
def checksPreserved : Rule where
  number := 471
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom weakensAxiomOrSourceCheck) ∧ₗ
    never (ev reply ∧ₗ atom treatsLeanVerifyAsFidelity)

/-- Rule 472: a refactored proof's type and axioms inspected. -/
def refactorInspected : Rule where
  number := 472
  keyword := .must
  domain := .softwareEngineering
  formula := ev leanEdit ∧ₗ atom refactorsProof ⟹ eventually (ev toolCall ∧ₗ link inspectsTypeAndAxioms)

/-- Rule 473: a failed removal shows no necessity. -/
def removalShowsNoNecessity : Rule where
  number := 473
  keyword := .mustNot
  domain := .softwareEngineering
  formula := never (ev reply ∧ₗ atom readsRemovalAsNecessity)

/-- Rule 474: a remote search hit confirmed locally. -/
def remoteHitConfirmed : Rule where
  number := 474
  keyword := .must
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom reliesOnRemoteHit ⟹ once (ev toolCall ∧ₗ link confirmsHitLocally)

/-- Rule 475: an empty search proves no absence without the index status. -/
def emptySearchNoAbsence : Rule where
  number := 475
  keyword := .mustNot
  domain := .softwareEngineering
  formula := never (ev reply ∧ₗ atom treatsEmptySearchAsAbsence)

/-- Rule 476: a transformation's laws each established, a rewrite's sides observationally equal. -/
def transformationLaws : Rule where
  number := 476
  keyword := .must
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom claimsTransformationCorrect ⟹
    once (ev toolCall ∧ₗ link establishesEachLaw) ∧ₗ once (ev toolCall ∧ₗ link showsSidesObservationallyEqual)

/-- Rule 477: a changed implementation's primitives shown to agree with the specification. -/
def primitivesAgree : Rule where
  number := 477
  keyword := .must
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom claimsImplementationPreserves ⟹ once (ev toolCall ∧ₗ link showsPrimitivesAgree)

/-- Rule 478: stateful equivalence by a step relation, not final output alone. -/
def stepSimulation : Rule where
  number := 478
  keyword := .must
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom claimsStatefulEquivalence ⟹
    once (ev toolCall ∧ₗ link showsStepSimulation) ∧ₗ ¬ₗ atom restsOnFinalOutput

/-- Rule 479: a normal form needs termination and uniqueness. -/
def normalFormEstablished : Rule where
  number := 479
  keyword := .mustNot
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom claimsNormalForm ⟹
    once (ev toolCall ∧ₗ link establishesTermination) ∧ₗ once (ev toolCall ∧ₗ link establishesUniqueness)

/-- Rule 480: no hidden index guessed. -/
def noGuessedIndex : Rule where
  number := 480
  keyword := .mustNot
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom guessesHiddenIndex)

/-- Rule 481: no second unchecked entrance to a validated type. -/
def noUncheckedEntrance : Rule where
  number := 481
  keyword := .mustNot
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom addsUncheckedEntrance)

/-- Rule 482: untrusted input parsed into the typed form, with an explicit error. -/
def parseUntrustedInput : Rule where
  number := 482
  keyword := .must
  domain := .softwareEngineering
  formula := ev editing ∧ₗ atom readsUntrustedInput ⟹ atom parsesIntoTypedForm ∧ₗ atom returnsExplicitError

/-- Rule 483: a phantom marker proves nothing alone. -/
def phantomIsNoProof : Rule where
  number := 483
  keyword := .mustNot
  domain := .softwareEngineering
  formula := never ((ev editing ∨ₗ ev reply) ∧ₗ atom treatsPhantomAsProof)

/-- Rule 484: no partial or unsafe code as evidence. -/
def noPartialEvidence : Rule where
  number := 484
  keyword := .mustNot
  domain := .softwareEngineering
  formula := never (ev leanEdit ∧ₗ atom usesPartialAsEvidence)

/-- Rule 485: a BEq's laws proved before its result is used as equality. -/
def beqLawsFirst : Rule where
  number := 485
  keyword := .must
  domain := .softwareEngineering
  formula := ev leanEdit ∧ₗ atom usesBeqAsEquality ⟹
    atom provesBeqLawsHere ∨ₗ once (ev leanEdit ∧ₗ link provesThoseBeqLaws)

/-- Rule 486: the actual toolchain checked before relying on its behaviour. -/
def toolchainChecked : Rule where
  number := 486
  keyword := .must
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom reliesOnToolchainBehavior ⟹ once (ev toolCall ∧ₗ link checksActualToolchain)

/-- Rule 487: a dispatch cache's key checked for every distinction. -/
def cacheKeyChecked : Rule where
  number := 487
  keyword := .must
  domain := .softwareEngineering
  formula := ev editing ∧ₗ atom addsDispatchCache ⟹ eventually (ev toolCall ∧ₗ link checksCacheKey)

/-- Rule 488: branch-local state defined before retries or parallel search. -/
def branchStateFirst : Rule where
  number := 488
  keyword := .must
  domain := .softwareEngineering
  formula := ev editing ∧ₗ atom enablesRetriesOrParallel ⟹
    atom definesBranchStateHere ∨ₗ once (ev editing ∧ₗ link definesBranchState)

/-- Rule 489: no accidental registration order deciding dispatch. -/
def noOrderDispatch : Rule where
  number := 489
  keyword := .mustNot
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom registrationOrderDecides)

/-! Rules 490 to 498: merge request descriptions, approvals, references and chat. -/

/-- Rule 490: a verification paragraph says what was verified, how, and what wasn't. -/
def verificationParagraph : Rule where
  number := 490
  keyword := .must
  domain := .softwareEngineering
  formula := ev mrDescription ⟹ atom statesWhatVerifiedHow ∧ₗ atom namesUnverified

/-- Rule 491: confidence levels distinguished. -/
def confidenceLevels : Rule where
  number := 491
  keyword := .must
  domain := .softwareEngineering
  formula := ev mrDescription ⟹ atom distinguishesConfidence

/-- Rule 492: a partial check says which part went unchecked and why. -/
def uncheckedPartNamed : Rule where
  number := 492
  keyword := .must
  domain := .softwareEngineering
  formula := ev mrDescription ∧ₗ atom partlyChecked ⟹ atom saysUncheckedPartWhy

/-- Rule 493: a check for others worded with its command; no person addressed. -/
def checkForOthersWorded : Rule where
  number := 493
  keyword := .must
  domain := .softwareEngineering
  formula := (ev mrDescription ∧ₗ atom hasCheckForOthers ⟹ atom checkWordedWithCommand) ∧ₗ
    never (ev mrDescription ∧ₗ atom addressesPerson)

/-- Rule 494: no questions for the reviewer in the description. -/
def noQuestionsInDescription : Rule where
  number := 494
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev mrDescription ∧ₗ atom asksReviewerQuestion)

/-- Rule 495: approvals and the reset setting read before a force-push, and read again after; a
claim they survive rests on both reads. -/
def approvalsReadAround : Rule where
  number := 495
  keyword := .must
  domain := .softwareEngineering
  formula := (ev forcePush ∧ₗ atom mrHasApprovals ⟹
      once (ev readsApprovals) ∧ₗ once (ev toolCall ∧ₗ link readsResetSetting) ∧ₗ
      eventually (ev readsApprovals)) ∧ₗ
    (ev reply ∧ₗ atom claimsApprovalsSurvive ⟹
      once (ev readsApprovals ∧ₗ once (ev forcePush ∧ₗ once (ev readsApprovals))))

/-- Rule 496: a merge request read back after it is opened. -/
def mrReadBack : Rule where
  number := 496
  keyword := .must
  domain := .softwareEngineering
  formula := ev mrOpen ⟹ eventually (ev mrView ∧ₗ link viewsThatMr)

/-- Rule 497: every reference the reader can open linked where it appears. -/
def referencesLinked : Rule where
  number := 497
  keyword := .must
  domain := .softwareEngineering
  formula := never ((ev editing ∨ₗ ev reply) ∧ₗ atom hasUnlinkedReference)

/-- Rule 498: every sentence of a chat draft capitalized. -/
def chatSentencesCapitalized : Rule where
  number := 498
  keyword := .must
  domain := .softwareEngineering
  formula := ev editing ∧ₗ atom draftsChatMessage ⟹ atom sentencesCapitalized

/-! Rules 499 to 514: paper writing. -/

/-- Rule 499: examples verified against the statement; no picture as proof. -/
def examplesVerified : Rule where
  number := 499
  keyword := .must
  domain := .mathematics
  formula := (ev editing ∧ₗ atom addsWorkedExample ⟹
      once (ev toolCall ∧ₗ link verifiesExampleAgainstStatement)) ∧ₗ
    never (ev editing ∧ₗ atom treatsPictureAsProof)

/-- Rule 500: quantifiers, assumptions and conventions preserved. -/
def conventionsPreserved : Rule where
  number := 500
  keyword := .must
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom dropsMathConvention)

/-- Rule 501: what is edited is read first. -/
def readBeforeEditingMath : Rule where
  number := 501
  keyword := .must
  domain := .mathematics
  formula := ev editing ∧ₗ atom editsMathStatement ⟹ once (ev reading ∧ₗ link readsEditedPassage)

/-- Rule 502: substance separated from presentation in the handoff. -/
def substanceSeparated : Rule where
  number := 502
  keyword := .must
  domain := .mathematics
  formula := ev reply ∧ₗ atom handsOffManuscript ⟹ atom separatesSubstanceFromPresentation

/-- Rule 503: statement and proof corrected together, nearby constructions checked. -/
def statementAndProofTogether : Rule where
  number := 503
  keyword := .must
  domain := .mathematics
  formula := ev editing ∧ₗ atom correctsMathStatement ⟹
    atom correctsProofToo ∧ₗ eventually (ev toolCall ∧ₗ link checksNearbyConstructions)

/-- Rule 504: a defect isn't resolved by only removing its warning. -/
def noWarningOnlyFix : Rule where
  number := 504
  keyword := .mustNot
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom onlyRemovesWarning)

/-- Rule 505: bibliographic facts verified from sources before relied on. -/
def bibliographyVerified : Rule where
  number := 505
  keyword := .must
  domain := .mathematics
  formula := (ev editing ∨ₗ ev reply) ∧ₗ atom reliesOnBibliographicFact ⟹
    once (ev toolCall ∧ₗ link readsSourceOfFact)

/-- Rule 506: the comparison with prior work described, contributions distinguished. -/
def priorWorkCompared : Rule where
  number := 506
  keyword := .must
  domain := .mathematics
  formula := ev editing ∧ₗ atom describesPriorWork ⟹ atom distinguishesContribution

/-- Rule 507: an example's intermediates and exceptional cases checked. -/
def exampleIntermediatesChecked : Rule where
  number := 507
  keyword := .must
  domain := .mathematics
  formula := ev editing ∧ₗ atom addsWorkedExample ⟹ once (ev toolCall ∧ₗ link checksExampleIntermediates)

/-- Rule 508: no example of an excluded object, no hidden failed condition. -/
def noManufacturedExample : Rule where
  number := 508
  keyword := .mustNot
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom manufacturesExcludedExample) ∧ₗ
    never (ev editing ∧ₗ atom hidesFailedCondition)

/-- Rule 509: a degree-lowering bound on the whole expression. -/
def boundOnWholeExpression : Rule where
  number := 509
  keyword := .must
  domain := .mathematics
  formula := ev editing ∧ₗ atom appliesDegreeBound ⟹ atom coversWholeExpression

/-- Rule 510: a final parameter choice checked against all requirements. -/
def parametersCheckedJointly : Rule where
  number := 510
  keyword := .must
  domain := .mathematics
  formula := ev editing ∧ₗ atom fixesParameterChoice ⟹ atom checksAllRequirements

/-- Rule 511: claims of novelty, authorship, checking or evidence supported. -/
def supportedClaims : Rule where
  number := 511
  keyword := .must
  domain := .mathematics
  formula := never ((ev editing ∨ₗ ev reply) ∧ₗ atom unsupportedClaimOfSupport)

/-- Rule 512: a publishable manuscript acknowledges AI contributions. -/
def aiAcknowledged : Rule where
  number := 512
  keyword := .must
  domain := .mathematics
  formula := ev editing ∧ₗ atom editsPublishableManuscript ⟹ atom acknowledgesAi

/-- Rule 513: a no-gap review certifies no paper. -/
def reviewIsNoCertificate : Rule where
  number := 513
  keyword := .mustNot
  domain := .mathematics
  formula := never (ev reply ∧ₗ atom treatsNoGapReviewAsCertification)

/-- Rule 514: no proof reopened for exposition alone. -/
def proofNotReopened : Rule where
  number := 514
  keyword := .mustNot
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom reopensProofForExposition)

/-! Rules 515 to 527: moving changes between commits and reviewing merge requests. -/

/-- Rule 515: each split diffed against the original before the rebase continues. -/
def splitDiffedBeforeContinue : Rule where
  number := 515
  keyword := .must
  domain := .softwareEngineering
  formula := ev rebaseContinue ∧ₗ atom continuesAfterSplit ⟹
    since (ev gitDiff ∧ₗ link diffsSplitAgainstOriginal) (ev rebaseContinue)

/-- Rule 516: cut specs dry-run before the rebase. -/
def cutSpecsDryRun : Rule where
  number := 516
  keyword := .must
  domain := .softwareEngineering
  formula := ev gitRebase ∧ₗ atom rebaseAppliesCutSpecs ⟹ once (ev toolCall ∧ₗ link dryRunsCutSpecs)

/-- Rule 517: a review comment's facts checked in a ledger first. -/
def reviewFactsInLedger : Rule where
  number := 517
  keyword := .must
  domain := .softwareEngineering
  formula := ev editing ∧ₗ atom draftsReviewFact ⟹ once (ev ledgerEdit ∧ₗ link ledgerRowChecksFact)

/-- Rule 518: a colleague's change reviewed with one's own rigor. -/
def ownRigorInReview : Rule where
  number := 518
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev reply ∧ₗ atom offersSubstandardReview)

/-- Rule 519: configuration rendered per environment and diffed against the deployed. -/
def configRenderedAndDiffed : Rule where
  number := 519
  keyword := .must
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom offersConfigReview ⟹
    once (ev toolCall ∧ₗ link rendersPerEnvironment) ∧ₗ once (ev toolCall ∧ₗ link diffsAgainstDeployed)

/-- Rule 520: settings checked at run time beyond rendering. -/
def settingsWorkAtRunTime : Rule where
  number := 520
  keyword := .must
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom offersConfigReview ⟹ once (ev toolCall ∧ₗ link checksSettingsAtRunTime)

/-- Rule 521: pins compared with what runs; the image build honours the lock. -/
def pinsCompared : Rule where
  number := 521
  keyword := .must
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom offersPinReview ⟹
    once (ev toolCall ∧ₗ link comparesPinWithRunning) ∧ₗ once (ev toolCall ∧ₗ link checksImageHonoursLock)

/-- Rule 522: relied-on contracts read at the version used. -/
def contractsReadAtVersion : Rule where
  number := 522
  keyword := .must
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom offersReview ⟹ once (ev toolCall ∧ₗ link readsReliedContracts)

/-- Rule 523: what the change depends on checked in place. -/
def dependenciesInPlace : Rule where
  number := 523
  keyword := .must
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom offersReview ⟹ once (ev toolCall ∧ₗ link checksDependenciesInPlace)

/-- Rule 524: what an import turns on is listed. -/
def importEffectsListed : Rule where
  number := 524
  keyword := .must
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom offersImportReview ⟹ atom listsWhatImportTurnsOn

/-- Rule 525: alert rules tested on edge series. -/
def alertRulesTested : Rule where
  number := 525
  keyword := .must
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom offersAlertRuleReview ⟹ once (ev toolCall ∧ₗ link testsRulesOnEdgeSeries)

/-- Rule 526: who can reach what the change opens, with what credential. -/
def reachAsked : Rule where
  number := 526
  keyword := .must
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom offersAccessReview ⟹ atom saysWhoCanReach

/-- Rule 527: the diff and live facts re-checked before posting. -/
def recheckBeforePosting : Rule where
  number := 527
  keyword := .must
  domain := .softwareEngineering
  formula := ev postsReviewComment ⟹
    once (ev toolCall ∧ₗ link rechecksMrDiff) ∧ₗ once (ev toolCall ∧ₗ link rechecksLiveFacts)

/-! Rules 528 to 560: the task protocol. -/

/-- Rule 528: the default skills loaded since the last compaction before any edit of a software task. -/
def defaultSkillsLoaded : Rule where
  number := 528
  keyword := .must
  domain := .tasks
  formula := ev editing ∧ₗ atom taskInProgress ⟹
    defaultSkills.foldr (fun s acc => sinceCompaction (ev (loadsSkill s)) ∧ₗ acc) (ev editing)

/-- Rule 529: lean4 loaded since the last compaction before a Lean edit. -/
def lean4Loaded : Rule where
  number := 529
  keyword := .must
  domain := .tasks
  formula := ev leanEdit ⟹ sinceCompaction (ev (loadsSkill "lean4"))

/-- Rule 530: a task's listed extra skills loaded in the context. -/
def extraSkillsLoaded : Rule where
  number := 530
  keyword := .must
  domain := .tasks
  formula := ev editing ∧ₗ atom taskListsExtraSkill ⟹
    sinceCompaction (ev loadsAnySkill ∧ₗ link loadsTaskListedSkill)

/-- Rule 531: a branch's description in the mr-cover-letter format. -/
def coverLetterFormat : Rule where
  number := 531
  keyword := .must
  domain := .tasks
  formula := ev mrDescription ⟹ atom followsCoverLetterFormat

/-- Rule 532: a task's directory made by task_index.py new, with a descriptive slug. -/
def taskDirectoryByTool : Rule where
  number := 532
  keyword := .must
  domain := .tasks
  formula := never (ev taskIndexNew ∧ₗ atom slugIsTicketOnly) ∧ₗ
    (ev editing ∧ₗ atom createsTaskDirectory ⟹ once (ev taskIndexNew ∧ₗ link createsThatTask))

/-- Rule 533: task.json edited only through the tool. -/
def taskJsonByTool : Rule where
  number := 533
  keyword := .must
  domain := .tasks
  formula := never (ev taskJsonEdit)

/-- Rule 534: PLAN.md living, Theory building first, Path second. -/
def planShape : Rule where
  number := 534
  keyword := .must
  domain := .tasks
  formula := ev planEdit ⟹ atom keepsTheoryThenPath

/-- Rule 535: a delegated task's theory before its plan or code. -/
def theoryFirst : Rule where
  number := 535
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom writesPlanOrCode ⟹ once (ev planEdit ∧ₗ link recordsTaskTheory)

/-- Rule 536: the theory as questions with answers, ahead of the plan, answered by research. -/
def theoryAsQuestions : Rule where
  number := 536
  keyword := .must
  domain := .discipline
  formula := (ev planEdit ∧ₗ atom recordsTheory ⟹ atom theoryAsQuestionsAhead) ∧ₗ
    never (ev reply ∧ₗ atom asksWhatResearchAnswers)

/-- Rule 537: a question written open before investigated, and moved to Resolved once answered. -/
def questionOpenFirst : Rule where
  number := 537
  keyword := .must
  domain := .tasks
  formula := (ev planEdit ∧ₗ atom addsResolvedEntry ⟹ once (ev planEdit ∧ₗ link openedAsQuestionFirst)) ∧ₗ
    (ev reply ∧ₗ atom findsAnswer ⟹ eventually (ev planEdit ∧ₗ link movesToResolved))

/-- Rule 538: Resolved a full, unpruned trace of question-and-answer pairs, stale text rewritten. -/
def resolvedTrace : Rule where
  number := 538
  keyword := .must
  domain := .tasks
  formula := never (ev planEdit ∧ₗ atom prunesResolved) ∧ₗ never (ev planEdit ∧ₗ atom resolvedEntryMalformed) ∧ₗ
    never (ev planEdit ∧ₗ atom mixesOpenAndResolved) ∧ₗ never (ev planEdit ∧ₗ atom leavesStaleStatement)

/-- Rule 539: a question first even if answered at once; findings under their question; wording kept. -/
def questionWording : Rule where
  number := 539
  keyword := .must
  domain := .tasks
  formula := (ev planEdit ∧ₗ atom addsResolvedEntry ⟹ atom entryStartsWithQuestion) ∧ₗ
    (ev planEdit ∧ₗ atom addsIncidentalFinding ⟹ atom placesUnderAnsweredQuestion) ∧ₗ
    never (ev planEdit ∧ₗ atom rewordsMovedQuestion)

/-- Rule 540: a run's result entered into the theory before the next step. -/
def runResultEntered : Rule where
  number := 540
  keyword := .must
  domain := .tasks
  formula := ev toolCall ∧ₗ ¬ₗ ev planEdit ⟹
    ¬ₗ since (ev anyResult ∧ₗ atom taskRunResult) (ev planEdit ∧ₗ atom entersRunResult)

/-- Rule 541: the task's status set every cycle. -/
def statusEveryCycle : Rule where
  number := 541
  keyword := .must
  domain := .tasks
  formula := ev cycleCheckpoint ⟹ inCycle (ev taskStatusSet)

/-- Rule 542: a request resolved with the tool in the cycle moving its substance to the plan. -/
def requestResolvedInCycle : Rule where
  number := 542
  keyword := .must
  domain := .tasks
  formula := ev requestResolve ⟹ inCycle (ev planEdit ∧ₗ link movesRequestSubstance)

/-- Rule 543: a request resolved only when fulfilled or dropped; no item number reused. -/
def requestResolvedHonestly : Rule where
  number := 543
  keyword := .must
  domain := .tasks
  formula := (ev requestResolve ⟹ atom requestFulfilledOrDropped) ∧ₗ never (ev requestAdd ∧ₗ atom reusesItemNumber)

/-- Rule 544: content removed from an open request only by request edit. -/
def requestContentByEdit : Rule where
  number := 544
  keyword := .must
  domain := .tasks
  formula := ev toolCall ∧ₗ atom removesRequestContent ⟹ ev requestEdit

/-- Rule 545: a blocked task names what blocks it. -/
def blockedTaskNamesBlocker : Rule where
  number := 545
  keyword := .must
  domain := .tasks
  formula := ev taskBlocked ⟹ atom statesWhatBlocks

/-- Rule 546: the task's other evidence committed under its directory. -/
def evidenceUnderTask : Rule where
  number := 546
  keyword := .must
  domain := .tasks
  formula := never ((ev commit ∨ₗ ev cycleCheckpoint) ∧ₗ atom evidenceOutsideTaskDir)

/-- Rule 547: a dated, complete notebook entry each cycle, and no per-task log or counter. -/
def entryEachCycle : Rule where
  number := 547
  keyword := .must
  domain := .tasks
  formula := (ev cycleCheckpoint ⟹ atom appendsCycleEntry ∧ₗ atom entryHasRequiredParts) ∧ₗ
    never (ev editing ∧ₗ atom writesTaskLog)

/-- Rule 548: no write to a locked task; work on another or tell the user. -/
def respectTaskLock : Rule where
  number := 548
  keyword := .mustNot
  domain := .tasks
  formula := never (ev editing ∧ₗ atom writesLockedTask) ∧ₗ
    ((ev anyResult ∨ₗ ev hookRefusal) ∧ₗ atom reportsTaskLock ⟹
      eventually ((ev reply ∧ₗ link tellsUserOfLock) ∨ₗ (ev editing ∧ₗ link worksOnOtherTask)))

/-- Rule 549: the old task paused in the step that moves work, and the records naming the work right. -/
def pauseOnSwitch : Rule where
  number := 549
  keyword := .must
  domain := .tasks
  formula := (ev editing ∧ₗ atom startsOtherTask ⟹
      sameMessage pausesTask ∨ₗ since (ev taskPaused) (ev editing)) ∧ₗ
    never (ev cycleCheckpoint ∧ₗ atom recordsNameWrongTask)

/-- Rule 550: a trajectory report naming another task means stale records. -/
def staleRecordsCorrected : Rule where
  number := 550
  keyword := .must
  domain := .tasks
  formula := (ev anyResult ∨ₗ ev hookRefusal) ∧ₗ atom trajectoryNamesOtherTask ⟹
    eventually (ev editing ∧ₗ link correctsStaleRecords)

/-- Rule 551: Where we stand holds open tasks only, each from its first checkpoint. -/
def whereWeStandOpenOnly : Rule where
  number := 551
  keyword := .must
  domain := .tasks
  formula := never (ev notebookEdit ∧ₗ atom holdsFinishedWork) ∧ₗ
    never (ev cycleCheckpoint ∧ₗ atom openTaskLacksParagraph)

/-- Rule 552: status, note and paragraph say what the cycle left, through status_text.py. -/
def statusAtCheckpoint : Rule where
  number := 552
  keyword := .must
  domain := .tasks
  formula := ev cycleCheckpoint ⟹ atom statusSaysWhatCycleLeft ∧ₗ inCycle (ev statusTextRun)

/-- Rule 553: the first cycle restates the task and checks for earlier work. -/
def firstCycleRestates : Rule where
  number := 553
  keyword := .must
  domain := .tasks
  formula := ev cycleCheckpoint ∧ₗ atom closesFirstCycle ⟹
    once (ev planEdit ∧ₗ link restatesTask) ∧ₗ once (ev toolCall ∧ₗ link checksStartedElsewhere)

/-- Rule 554: the task investigated, the user asked what scoping needs, nothing else asked. -/
def investigateAndAskNeeded : Rule where
  number := 554
  keyword := .must
  domain := .tasks
  formula := (ev planEdit ∧ₗ atom writesFirstPathSteps ⟹ once (ev reading ∧ₗ link readsWhatTaskTouches)) ∧ₗ
    never (ev planEdit ∧ₗ atom settlesUsersScope) ∧ₗ never (ev reply ∧ₗ atom asksWhatBlocksNothing)

/-- Rule 555: each answer moved into Resolved as its pair. -/
def answersRecorded : Rule where
  number := 555
  keyword := .must
  domain := .tasks
  formula := ev user ∧ₗ atom userAnswersQuestion ⟹ eventually (ev planEdit ∧ₗ link recordsAnswerPair)

/-- Rule 556: the Path written once the theory is stable, as concrete ordered steps. -/
def pathAfterStableTheory : Rule where
  number := 556
  keyword := .must
  domain := .tasks
  formula := ev planEdit ∧ₗ atom writesFirstPathSteps ⟹ atom stepsConcreteOrdered ∧ₗ atom theoryStableHere

/-- Rule 557: no first Path steps without a passing stable check since the theory last changed,
unless the Path quotes the user's order. -/
def stableBeforePath : Rule where
  number := 557
  keyword := .mustNot
  domain := .tasks
  formula := ev planEdit ∧ₗ atom writesFirstPathSteps ⟹
    since (ev stableCheck ∧ₗ link stableSucceeded) (ev planEdit ∧ₗ atom editsTheory) ∨ₗ atom quotesUserOrder

/-- Rule 558: a plan the user states entered at once; each queued run names its step. -/
def userPlanEntered : Rule where
  number := 558
  keyword := .must
  domain := .tasks
  formula := (ev user ∧ₗ atom userStatesPlan ⟹ eventually (ev planEdit ∧ₗ link entersUserPlan)) ∧ₗ
    (ev computeRun ∧ₗ atom queuesTaskRun ⟹ atom namesPathStep)

/-- Rule 559: the first cycle's entry has status task started. -/
def firstEntryStarted : Rule where
  number := 559
  keyword := .must
  domain := .tasks
  formula := ev cycleCheckpoint ∧ₗ atom closesFirstCycle ⟹ atom entryStatusStarted

/-- Rule 560: a replacing decision through the checklist before its first edit. -/
def replacingDecisionChecked : Rule where
  number := 560
  keyword := .must
  domain := .tasks
  formula := ev editing ∧ₗ atom implementsReplacingDecision ⟹ once (ev planEdit ∧ₗ link checklistsDecision)

def rules : List Rule :=
  [numericalCheckMatchesClaim, instanceKindStated, nonvacuityBeforeCoding, nonvacuityCountRecorded,
   noSubThresholdReading, boundOnExtremals, ownQuantityComputed, newRunsDistinguished,
   primeIsNoHypothesis, certificateScopeStated, exactPcDegree, kernelValidatedFirst,
   foreignTypesDeclared, casOutputChecked, numbersFromSavedOutput, totalInOneRun,
   distinctKeysCounted, countersUnknownNotZero, signalsAreNoCause, longRunCauseInspected,
   noTraceBypass, slowToolInvestigated, deliveredLimitsRead, quotaProvedUnderLoad,
   createResponseRead, measureAloneBeforeBlame, progressByOutput, realUseRead, placeByMemory,
   stateFromPodStatus, hostBeforeNativeBuild, downloadProgressRead, hfDownloadCompletes,
   oneWriterPerFile, hubFilesNamed, inventoryCoversHarness, resultsPromoted, noOutputTruncation,
   unstoppableJobReported, statementBeforeProof, hypothesesWitnessed, undeterminedRecorded,
   reviewFromPrintedTypes, unvouchedCodeRead, sorryGoalIsNoProof, freshDiagnostics,
   scratchTacticCopied, tacticClosesCleanly, requestedStatementKept, importsBuiltFirst,
   checksPreserved, refactorInspected, removalShowsNoNecessity, remoteHitConfirmed,
   emptySearchNoAbsence, transformationLaws, primitivesAgree, stepSimulation,
   normalFormEstablished, noGuessedIndex, noUncheckedEntrance, parseUntrustedInput,
   phantomIsNoProof, noPartialEvidence, beqLawsFirst, toolchainChecked, cacheKeyChecked,
   branchStateFirst, noOrderDispatch, verificationParagraph, confidenceLevels, uncheckedPartNamed,
   checkForOthersWorded, noQuestionsInDescription, approvalsReadAround, mrReadBack,
   referencesLinked, chatSentencesCapitalized, examplesVerified, conventionsPreserved,
   readBeforeEditingMath, substanceSeparated, statementAndProofTogether, noWarningOnlyFix,
   bibliographyVerified, priorWorkCompared, exampleIntermediatesChecked, noManufacturedExample,
   boundOnWholeExpression, parametersCheckedJointly, supportedClaims, aiAcknowledged,
   reviewIsNoCertificate, proofNotReopened, splitDiffedBeforeContinue, cutSpecsDryRun,
   reviewFactsInLedger, ownRigorInReview, configRenderedAndDiffed, settingsWorkAtRunTime,
   pinsCompared, contractsReadAtVersion, dependenciesInPlace, importEffectsListed,
   alertRulesTested, reachAsked, recheckBeforePosting, defaultSkillsLoaded, lean4Loaded,
   extraSkillsLoaded, coverLetterFormat, taskDirectoryByTool, taskJsonByTool, planShape,
   theoryFirst, theoryAsQuestions, questionOpenFirst, resolvedTrace, questionWording,
   runResultEntered, statusEveryCycle, requestResolvedInCycle, requestResolvedHonestly,
   requestContentByEdit, blockedTaskNamesBlocker, evidenceUnderTask, entryEachCycle,
   respectTaskLock, pauseOnSwitch, staleRecordsCorrected, whereWeStandOpenOnly,
   statusAtCheckpoint, firstCycleRestates, investigateAndAskNeeded, answersRecorded,
   pathAfterStableTheory, stableBeforePath, userPlanEntered, firstEntryStarted,
   replacingDecisionChecked]

/-- Range 4 holds no MAY rule. -/
def permissions : List Nat := []

/-- The rules are 421 to 560, each once, in number order. -/
theorem rules_numbers : rules.map (·.number) = List.range' 421 140 := by decide

end Rails.Ruleset.Range4
