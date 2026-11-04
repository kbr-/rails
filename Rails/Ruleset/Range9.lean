import Rails.Rules
import Rails.Examples
import Rails.Witness

/-!
Rules 1121 to 1260 of `tasks/agents-on-rails/RULES.md`: the design skills' rules on types, algebra
and property tests, mutation testing, interactive Lean work, merge-request cover letters and stacks,
moving changes between commits, correspondence, paper writing, and reviewing a colleague's merge
request. None of them is a MAY rule.
-/

namespace Rails.Ruleset.Range9
open Rails Formula Ruleset Rules Examples

/-! Tests the predicates below are built from. -/

/-- A word of the command is `s`. -/
def wordIs (s : String) (ws : List (List Char)) : Bool := ws.contains s.toList

/-- A word of the command starts with `s`. -/
def wordStarts (s : String) (ws : List (List Char)) : Bool := ws.any (hasPrefix s.toList)

/-- The call's command text contains `s`. -/
def commandContains (s : String) (e : Event) : Bool :=
  match command e with
  | some c => occursIn s.toList c.toList
  | none => false

/-- Some command of the call has a word ending `s`: a script run directly or through a launcher
such as `compute.sh`. -/
def runsScript (s : String) (e : Event) : Bool :=
  (programs e).any fun (_, ws) => ws.any (endsWith s.toList)

/-- The call's tool name contains `s`; an MCP tool's name carries its server's prefix. -/
def toolNamed (s : String) : Event → Bool
  | .call _ t _ => occursIn s.toList t.toList
  | _ => false

/-- The file an edit writes ends `s`. -/
def writesEnding (s : String) (e : Event) : Bool :=
  match writePath e with
  | some p => endsWith s.toList p.toList
  | none => false

/-- The file an edit writes has `s` in its path. -/
def writesPathWith (s : String) (e : Event) : Bool :=
  match writePath e with
  | some p => occursIn s.toList p.toList
  | none => false

/-! Event predicates. -/

def anyCall : Pred := ⟨"anyCall", isCall, [bash "ls"]⟩
def thinkingStep : Pred := ⟨"thinkingStep", isThinking, [.thinking "t"]⟩
def toolResult : Pred := ⟨"toolResult", isResult, [.result "c" "out"]⟩
def gitCommit : Pred := ⟨"gitCommit", runs "git" (wordIs "commit"), [bash "git commit -m x"]⟩
def fixupCommit : Pred := ⟨"fixupCommit",
  runs "git" (fun ws => wordIs "commit" ws && wordStarts "--fixup" ws),
  [bash "git commit --fixup=abc123"]⟩
def autosquashRebase : Pred := ⟨"autosquashRebase",
  runs "git" (fun ws => wordIs "rebase" ws && wordIs "--autosquash" ws),
  [bash "GIT_SEQUENCE_EDITOR=true git rebase -i --autosquash main"]⟩
def sequenceEditorRebase : Pred := ⟨"sequenceEditorRebase",
  runs "git" (fun ws => wordIs "rebase" ws && wordStarts "GIT_SEQUENCE_EDITOR=" ws),
  [bash "GIT_SEQUENCE_EDITOR='sed -i 1d' git rebase -i main"]⟩
def todoToolsUsed : Pred := ⟨"todoToolsUsed",
  fun e => commandContains "mark_edit.py" e || commandContains "reorder_todo.py" e,
  [bash "GIT_SEQUENCE_EDITOR='python3 mark_edit.py abc' git rebase -i main"]⟩
def interactiveStaging : Pred := ⟨"interactiveStaging",
  runs "git" (fun ws => wordIs "add" ws &&
    (wordIs "-p" ws || wordIs "-i" ws || wordIs "--patch" ws || wordIs "--interactive" ws)),
  [bash "git add -p f.py"]⟩
def authorFromTarget : Pred := ⟨"authorFromTarget", commandContains "GIT_AUTHOR_NAME=",
  [bash "GIT_AUTHOR_NAME=Ann GIT_AUTHOR_EMAIL=a@x git commit -m 'leftover for: x'"]⟩
def leftoverMessage : Pred := ⟨"leftoverMessage",
  fun e => runs "git" (wordIs "commit") e && commandContains "leftover for: " e,
  [bash "git commit -m 'leftover for: Add the parser'"]⟩
def glabAuthStatus : Pred := ⟨"glabAuthStatus",
  runs "glab" (fun ws => wordIs "auth" ws && wordIs "status" ws), [bash "glab auth status"]⟩
def mrCreate : Pred := ⟨"mrCreate",
  fun e => runs "glab" (fun ws => wordIs "mr" ws && wordIs "create" ws) e ||
    runs "gh" (fun ws => wordIs "pr" ws && wordIs "create" ws) e,
  [bash "glab mr create --fill", bash "gh pr create --fill"]⟩
def gitLog : Pred := ⟨"gitLog",
  runs "git" (fun ws => wordIs "log" ws || wordIs "show" ws || wordIs "format-patch" ws),
  [bash "git log --format=%B main..b"]⟩
def searchCall : Pred := ⟨"searchCall",
  fun e => isTool "Grep" e || runs "grep" (fun _ => true) e || runs "rg" (fun _ => true) e,
  [bash "rg -n timeout src", .call "g" "Grep" [("pattern", "timeout")]]⟩
def mutationBatch : Pred := ⟨"mutationBatch", runsScript "mutation_batch.py",
  [bash "python3 tools/mutation_batch.py . spec.json",
   bash "./compute.sh python3 tools/mutation_batch.py . spec.json"]⟩
def underLauncher : Pred := ⟨"underLauncher", runsScript "compute.sh",
  [bash "./compute.sh python3 tools/mutation_batch.py . spec.json"]⟩
def leanCompile : Pred := ⟨"leanCompile",
  fun e => runs "lake" (fun _ => true) e || runs "lean" (fun _ => true) e,
  [bash "lake env lean Rails/X.lean", bash "lake build"]⟩
def leanEdit : Pred := ⟨"leanEdit", writesEnding ".lean", [edit "Rails/X.lean"]⟩
def testEdit : Pred := ⟨"testEdit", writesPathWith "test", [edit "tests/test_rules.py"]⟩
def coverLetterEdit : Pred := ⟨"coverLetterEdit", writesEnding "_MR.md", [edit "tasks/x/X_MR.md"]⟩
def versionNoteEdit : Pred := ⟨"versionNoteEdit",
  fun e => writesEnding "_NOTE.md" e && writesPathWith "_V" e, [edit "tasks/x/TOPIC_V2_NOTE.md"]⟩
def messageDraftEdit : Pred := ⟨"messageDraftEdit", writesEnding "_MESSAGE.md",
  [edit "tasks/x/private/ANN_MESSAGE.md"]⟩
def translationEdit : Pred := ⟨"translationEdit", writesEnding "_MESSAGE_PL.md",
  [edit "tasks/x/private/ANN_MESSAGE_PL.md"]⟩
def ledgerEdit : Pred := ⟨"ledgerEdit", writesEnding "_EVIDENCE.md",
  [edit "tasks/x/private/ANN_MESSAGE_EVIDENCE.md"]⟩
def privateEdit : Pred := ⟨"privateEdit", writesPathWith "/private/",
  [edit "tasks/x/private/ANN_MESSAGE.md"]⟩
def reviewDraftEdit : Pred := ⟨"reviewDraftEdit",
  fun e => writesEnding ".md" e && writesPathWith "REVIEW" e, [edit "tasks/x/MR_REVIEW.md"]⟩
def pdfRead : Pred := ⟨"pdfRead",
  fun e => match readPath e with
    | some p => endsWith ".pdf".toList p.toList
    | none => false,
  [read "paper/main.pdf"]⟩
def agentRun : Pred := ⟨"agentRun", isTool "Agent", [reviewer]⟩
def cheaperModel : Pred := ⟨"cheaperModel",
  fun e => isTool "Agent" e && (e.field "model" == some "sonnet" || e.field "model" == some "haiku"),
  [.call "a" "Agent" [("subagent_type", "medium-reviewer"), ("model", "sonnet")]]⟩
def leanDiagnostics : Pred := ⟨"leanDiagnostics", toolNamed "lean_diagnostic_messages",
  [.call "m" "mcp__lean-lsp__lean_diagnostic_messages" []]⟩
def leanCodeActions : Pred := ⟨"leanCodeActions", toolNamed "lean_code_actions",
  [.call "m" "mcp__lean-lsp__lean_code_actions" []]⟩
def leanLocalSearch : Pred := ⟨"leanLocalSearch", toolNamed "lean_local_search",
  [.call "m" "mcp__lean-lsp__lean_local_search" []]⟩
def leanMultiAttempt : Pred := ⟨"leanMultiAttempt", toolNamed "lean_multi_attempt",
  [.call "m" "mcp__lean-lsp__lean_multi_attempt" []]⟩
def leanProfile : Pred := ⟨"leanProfile", toolNamed "lean_profile_proof",
  [.call "m" "mcp__lean-lsp__lean_profile_proof" []]⟩
def leanInspect : Pred := ⟨"leanInspect",
  fun e => toolNamed "lean_file_outline" e || toolNamed "lean_goal" e ||
    toolNamed "lean_term_goal" e || toolNamed "lean_hover_info" e,
  [.call "m" "mcp__lean-lsp__lean_goal" [], .call "m" "mcp__lean-lsp__lean_hover_info" []]⟩
def leanMcpCall : Pred := ⟨"leanMcpCall", toolNamed "lean-lsp",
  [.call "m" "mcp__lean-lsp__lean_goal" []]⟩

def preds : List Pred :=
  [anyCall, thinkingStep, toolResult, gitCommit, fixupCommit, autosquashRebase,
   sequenceEditorRebase, todoToolsUsed, interactiveStaging, authorFromTarget, leftoverMessage,
   glabAuthStatus, mrCreate, gitLog, searchCall, mutationBatch, underLauncher, leanCompile,
   leanEdit, testEdit, coverLetterEdit, versionNoteEdit, messageDraftEdit, translationEdit,
   ledgerEdit, privateEdit, reviewDraftEdit, pdfRead, agentRun, cheaperModel, leanDiagnostics,
   leanCodeActions, leanLocalSearch, leanMultiAttempt, leanProfile, leanInspect, leanMcpCall]

theorem preds_wellFormed : preds.all Pred.wellFormed = true := by decide

/-- A message file (a draft, its translation, or a ledger in a private folder). -/
def isMessageFile (e : Event) : Bool :=
  writesEnding "_MESSAGE.md" e || writesEnding "_MESSAGE_PL.md" e ||
    (writesEnding "_EVIDENCE.md" e && writesPathWith "/private/" e)

/-- Two edits of one message write two different message files. -/
def messageFilesTogether : Rel := ⟨"messageFilesTogether",
  fun s t => isMessageFile s.event && isMessageFile t.event && writePath s.event != writePath t.event,
  [(edit "tasks/x/private/ANN_MESSAGE.md", edit "tasks/x/private/ANN_MESSAGE_PL.md")]⟩

def rels : List Rel := [messageFilesTogether]

theorem rels_wellFormed : rels.all Rel.wellFormed = true := by decide

/-! Types, evidence and algebra (rules 1121 to 1144). -/

def reviewsAbstractApi : Atom := ⟨"reviewsAbstractApi",
  "Does this reply review an abstract API (its types, quantifiers or indices)?", .reply⟩
def writesQuantifiersExplicitly : Atom := ⟨"writesQuantifiersExplicitly",
  "Does this reply write the API's quantifiers and binder scopes explicitly?", .reply⟩
def saysWhoSelectsIndex : Atom := ⟨"saysWhoSelectsIndex",
  "Does this reply say, for each index, whether the caller or the implementation selects it?", .reply⟩

/-- Rule 1121: an abstract API's review writes its quantifiers and says who picks each index. -/
def explicitQuantifiersInApiReview : Rule where
  number := 1121
  keyword := .should
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom reviewsAbstractApi ⟹
    (atom writesQuantifiersExplicitly ∧ₗ atom saysWhoSelectsIndex) ∨ₗ atom justified

def definesProtocolOperations : Atom := ⟨"definesProtocolOperations",
  "Does this edit define the operations of a protocol (steps that must come in some order)?", .edit⟩
def indexesOperationsByState : Atom := ⟨"indexesOperationsByState",
  "Does this edit index each protocol operation by the states it may start from and end in?", .edit⟩
def statesRuntimeObligations : Atom := ⟨"statesRuntimeObligations",
  "Does this edit state the protocol's remaining runtime obligations (ownership, termination, cleanup, exactly-once effects)?", .edit⟩

/-- Rule 1122: protocol operations indexed by state, with the remaining runtime obligations. -/
def protocolIndexedByState : Rule where
  number := 1122
  keyword := .should
  domain := .softwareEngineering
  formula := ev editing ∧ₗ atom definesProtocolOperations ⟹
    (atom indexesOperationsByState ∧ₗ atom statesRuntimeObligations) ∨ₗ atom justified

def describesSchemaAgain : Atom := ⟨"describesSchemaAgain",
  "Does this edit add an artifact describing a schema another artifact already describes (a type, a serializer, a table)?", .edit⟩
def derivesFromSchema : Atom := ⟨"derivesFromSchema",
  "Does this edit derive that artifact's structure from the authoritative schema?", .edit⟩
def specifiesSchemaPolicy : Atom := ⟨"specifiesSchemaPolicy",
  "Does this edit specify the schema's policy choices (equality, ordering, absent versus null, wire naming)?", .edit⟩

/-- Rule 1123: one authoritative schema, the rest derived, its policy choices specified. -/
def schemaAuthoritative : Rule where
  number := 1123
  keyword := .should
  domain := .softwareEngineering
  formula := ev editing ∧ₗ atom describesSchemaAgain ⟹
    (atom derivesFromSchema ∧ₗ atom specifiesSchemaPolicy) ∨ₗ atom justified

def renameRedefinesProtocol : Atom := ⟨"renameRedefinesProtocol",
  "Does this edit's rename of a source field silently change a public protocol's field?", .edit⟩
def renameExposesPrivateData : Atom := ⟨"renameExposesPrivateData",
  "Does this edit's rename of a source field expose private data?", .edit⟩

/-- Rule 1124: no field rename silently redefining a public protocol or exposing private data. -/
def renameKeepsProtocol : Rule where
  number := 1124
  keyword := .mustNot
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ (atom renameRedefinesProtocol ∨ₗ atom renameExposesPrivateData))

def writesRejection : Atom := ⟨"writesRejection",
  "Does this edit write the message a rejected use of an interface reports?", .edit⟩
def rejectionGivesNextAction : Atom := ⟨"rejectionGivesNextAction",
  "Does that rejection message speak in the domain's terms and name a valid next action?", .edit⟩
def testsInvalidUses : Atom := ⟨"testsInvalidUses",
  "Does this edit add tests of invalid uses of an interface?", .edit⟩
def testsMinimalValidCaller : Atom := ⟨"testsMinimalValidCaller",
  "Does this edit also exercise a minimal valid caller beside the invalid uses?", .edit⟩

/-- Rule 1125: a rejection in domain terms with a next action; a valid caller beside invalid uses. -/
def rejectionInDomainTerms : Rule where
  number := 1125
  keyword := .should
  domain := .softwareEngineering
  formula := (ev editing ∧ₗ atom writesRejection ⟹ atom rejectionGivesNextAction) ∧ₗ
    (ev editing ∧ₗ atom testsInvalidUses ⟹ atom testsMinimalValidCaller) ∨ₗ atom justified

def misusesSubtypeSigmaExists : Atom := ⟨"misusesSubtypeSigmaExists",
  "Does this Lean edit use Subtype, Sigma or Exists where another of them fits (a predicate's proof, dependent data, a logical existence claim)?", .edit⟩
def hidesNeededWitness : Atom := ⟨"hidesNeededWitness",
  "Does this Lean edit put a witness that execution must inspect into a Prop?", .edit⟩

/-- Rule 1126: Subtype, Sigma and Exists each where it fits; a needed witness kept in data. -/
def evidenceTypesFit : Rule where
  number := 1126
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev leanEdit ∧ₗ (atom misusesSubtypeSigmaExists ∨ₗ atom hidesNeededWitness)) ∨ₗ
    atom justified

def boolAsEvidence : Atom := ⟨"boolAsEvidence",
  "Does this Lean edit treat a Bool result as logical evidence without Decidable or a proved reflection theorem?", .edit⟩

/-- Rule 1127: Bool kept apart from Prop, a decision turned into evidence by a proved link. -/
def boolApartFromProp : Rule where
  number := 1127
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev leanEdit ∧ₗ atom boolAsEvidence) ∨ₗ atom justified

def mixesNoncomputableExecutable : Atom := ⟨"mixesNoncomputableExecutable",
  "Does this Lean edit mix a noncomputable existence proof into an executable construction?", .edit⟩

/-- Rule 1128: noncomputable existence apart from executable construction. -/
def noncomputableApart : Rule where
  number := 1128
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev leanEdit ∧ₗ atom mixesNoncomputableExecutable) ∨ₗ atom justified

def assumesErasureRemovesCost : Atom := ⟨"assumesErasureRemovesCost",
  "Does this reply assume proof erasure removes runtime validation, retained witnesses or dictionary costs?", .reply⟩

/-- Rule 1129: no assumption that proof erasure removes runtime costs. -/
def erasureKeepsCosts : Rule where
  number := 1129
  keyword := .shouldNot
  domain := .softwareEngineering
  formula := never (ev reply ∧ₗ atom assumesErasureRemovesCost) ∨ₗ atom justified

def definesValueSemantics : Atom := ⟨"definesValueSemantics",
  "Does this edit define a value type's semantics or its equality?", .edit⟩
def definesObservations : Atom := ⟨"definesObservations",
  "Does this edit define the observations by which callers distinguish the values (observer parameters, errors, outputs, remaining state, future behavior)?", .edit⟩

/-- Rule 1130: a value's semantics names the observations that distinguish values. -/
def observationsDefined : Rule where
  number := 1130
  keyword := .should
  domain := .softwareEngineering
  formula := ev editing ∧ₗ atom definesValueSemantics ⟹ atom definesObservations ∨ₗ atom justified

def claimsEquivalence : Atom := ⟨"claimsEquivalence",
  "Does this reply claim two values or computations are equivalent?", .reply⟩
def statesEquivalenceExplicitly : Atom := ⟨"statesEquivalenceExplicitly",
  "Does this reply state the observational equivalence explicitly, under which observations and in which domain?", .reply⟩
def checksSubstitution : Atom := ⟨"checksSubstitution",
  "Does this reply say how replacing a value by an equivalent one inside the allowed operations was checked to preserve the equivalence?", .reply⟩

/-- Rule 1131: an equivalence stated explicitly and checked to survive substitution. -/
def equivalenceExplicit : Rule where
  number := 1131
  keyword := .should
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom claimsEquivalence ⟹
    (atom statesEquivalenceExplicitly ∧ₗ atom checksSubstitution) ∨ₗ atom justified

def findsDistinguishingContext : Atom := ⟨"findsDistinguishingContext",
  "Does this reply find a context that distinguishes values claimed equivalent?", .reply⟩
def strengthensOrRestricts : Link := ⟨"strengthensOrRestricts",
  "Does this edit strengthen the observations, or restrict the claimed equivalence, for the context the anchored reply found?"⟩

/-- Rule 1132: a distinguishing context strengthens the observations or narrows the equivalence. -/
def distinguishingContextAnswered : Rule where
  number := 1132
  keyword := .should
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom findsDistinguishingContext ⟹
    eventually (ev editing ∧ₗ link strengthensOrRestricts) ∨ₗ atom justified

def statesApiLaws : Atom := ⟨"statesApiLaws",
  "Does this edit state equations or laws among an API's operations?", .edit⟩
def exhibitsDistinctBehaviors : Atom := ⟨"exhibitsDistinctBehaviors",
  "Does this edit exhibit required behaviors the laws must keep distinct?", .edit⟩
def givesRealizingModel : Atom := ⟨"givesRealizingModel",
  "Does this edit give a model realizing those distinct behaviors?", .edit⟩
def anchorsObservationsInDomain : Atom := ⟨"anchorsObservationsInDomain",
  "Does this edit anchor the observations in the domain's meaning?", .edit⟩

/-- Rule 1133: laws come with distinct required behaviors and a model realizing them. -/
def lawsHaveModel : Rule where
  number := 1133
  keyword := .should
  domain := .softwareEngineering
  formula := ev editing ∧ₗ atom statesApiLaws ⟹
    (atom exhibitsDistinctBehaviors ∧ₗ atom givesRealizingModel ∧ₗ atom anchorsObservationsInDomain) ∨ₗ
    atom justified

def definesPrimitive : Atom := ⟨"definesPrimitive",
  "Does this edit define a primitive operation of an API?", .edit⟩
def givesPrimitiveMeaning : Atom := ⟨"givesPrimitiveMeaning",
  "Does this edit give the primitive an observable meaning connected to the other operations?", .edit⟩
def statesEquationConditions : Atom := ⟨"statesEquationConditions",
  "Does this edit write domains, preconditions and exceptional outcomes beside its conditional equations?", .edit⟩

/-- Rule 1134: each primitive's meaning, with its equations' conditions beside them. -/
def primitiveMeaning : Rule where
  number := 1134
  keyword := .should
  domain := .softwareEngineering
  formula := ev editing ∧ₗ atom definesPrimitive ⟹
    (atom givesPrimitiveMeaning ∧ₗ atom statesEquationConditions) ∨ₗ atom justified

def comparesDerivations : Link := ⟨"comparesDerivations",
  "Does this reply compare different derivations of one expression under the laws the anchored edit states?"⟩

/-- Rule 1135: stated laws are tested by comparing derivations of one expression. -/
def derivationsCompared : Rule where
  number := 1135
  keyword := .should
  domain := .softwareEngineering
  formula := ev editing ∧ₗ atom statesApiLaws ⟹
    eventually (ev reply ∧ₗ link comparesDerivations) ∨ₗ atom justified

def algebraLosesStructure : Atom := ⟨"algebraLosesStructure",
  "Does the algebra this edit chooses lose a required order, multiplicity or failure behavior?", .edit⟩

/-- Rule 1136: the chosen algebra keeps required order, multiplicity and failure. -/
def algebraKeepsStructure : Rule where
  number := 1136
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom algebraLosesStructure) ∨ₗ atom justified

def neutralAsMissing : Atom := ⟨"neutralAsMissing",
  "Does this edit treat a neutral value as unknown or missing information where the domain gives it no such meaning?", .edit⟩

/-- Rule 1137: a neutral value means missing only where the domain says so. -/
def neutralValueMeaning : Rule where
  number := 1137
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom neutralAsMissing) ∨ₗ atom justified

def pureLawsClaimEffects : Atom := ⟨"pureLawsClaimEffects",
  "Do this edit's laws over a pure description claim delivery, durability or recovery that only the effectful boundary can give?", .edit⟩

/-- Rule 1138: delivery, durability and recovery stay at the effectful boundary. -/
def effectsAtBoundary : Rule where
  number := 1138
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom pureLawsClaimEffects) ∨ₗ atom justified

def addsConvenience : Atom := ⟨"addsConvenience",
  "Does this edit add a convenience operation whose meaning the primitives can express?", .edit⟩
def convenienceThroughPrimitives : Atom := ⟨"convenienceThroughPrimitives",
  "Does this edit define the convenience through the primitives, its equations tied to that definition?", .edit⟩
def basisByConstructorCount : Atom := ⟨"basisByConstructorCount",
  "Does this edit choose its basis of primitives by constructor count rather than by clarity?", .edit⟩

/-- Rule 1139: conveniences through primitives; the basis chosen for clarity. -/
def conveniencesFromPrimitives : Rule where
  number := 1139
  keyword := .should
  domain := .softwareEngineering
  formula := (ev editing ∧ₗ atom addsConvenience ⟹ atom convenienceThroughPrimitives) ∧ₗ
    never (ev editing ∧ₗ atom basisByConstructorCount) ∨ₗ atom justified

def addsRepresentation : Atom := ⟨"addsRepresentation",
  "Does this edit add a representation (an optimized form, a compiled form) of a semantic model?", .edit⟩
def givesInterpretation : Atom := ⟨"givesInterpretation",
  "Does this edit give that representation an interpretation into the semantic model?", .edit⟩
def addsReferenceInterpreter : Atom := ⟨"addsReferenceInterpreter",
  "Does this edit add a reference interpreter?", .edit⟩
def connectsInterpreterToSpec : Atom := ⟨"connectsInterpreterToSpec",
  "Does this edit connect the reference interpreter to the specification?", .edit⟩

/-- Rule 1140: a representation interpreted into the model; a reference interpreter tied to the spec. -/
def representationInterpreted : Rule where
  number := 1140
  keyword := .should
  domain := .softwareEngineering
  formula := (ev editing ∧ₗ atom addsRepresentation ⟹ atom givesInterpretation) ∧ₗ
    (ev editing ∧ₗ atom addsReferenceInterpreter ⟹ atom connectsInterpreterToSpec) ∨ₗ atom justified

def domainsDiffer : Atom := ⟨"domainsDiffer",
  "Does this edit implement a model over a domain that differs from the model's (floats for reals, bounded integers)?", .edit⟩
def tracksDomainDifferences : Atom := ⟨"tracksDomainDifferences",
  "Does this edit track the rounding, boundaries and partiality where the domains differ?", .edit⟩
def performanceFromSemantics : Atom := ⟨"performanceFromSemantics",
  "Does this reply conclude something about performance from semantic preservation, with no measurement?", .reply⟩

/-- Rule 1141: domain differences tracked; performance measured on its own. -/
def domainDifferencesTracked : Rule where
  number := 1141
  keyword := .should
  domain := .softwareEngineering
  formula := (ev editing ∧ₗ atom domainsDiffer ⟹ atom tracksDomainDifferences) ∧ₗ
    never (ev reply ∧ₗ atom performanceFromSemantics) ∨ₗ atom justified

def partialInterpreter : Atom := ⟨"partialInterpreter",
  "Does this Lean edit interpret a syntax with an interpreter that isn't total?", .edit⟩
def interpretationEqualityNotRelation : Atom := ⟨"interpretationEqualityNotRelation",
  "Does this Lean edit state equality of interpretations other than as a relation?", .edit⟩
def quotientWithoutRespect : Atom := ⟨"quotientWithoutRespect",
  "Does this Lean edit use a quotient whose operations aren't shown to respect the relation?", .edit⟩

/-- Rule 1142: a total interpreter; interpretation equality a relation; a quotient only when respected. -/
def totalInterpreter : Rule where
  number := 1142
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev leanEdit ∧ₗ (atom partialInterpreter ∨ₗ atom interpretationEqualityNotRelation ∨ₗ
    atom quotientWithoutRespect)) ∨ₗ atom justified

def conflatesEqualities : Atom := ⟨"conflatesEqualities",
  "Does this Lean edit state a theorem leaving unclear whether it means syntactic equality or semantic equivalence?", .edit⟩

/-- Rule 1143: syntactic equality and semantic equivalence explicit in theorems. -/
def equalitiesExplicit : Rule where
  number := 1143
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev leanEdit ∧ₗ atom conflatesEqualities) ∨ₗ atom justified

def addsTransformation : Atom := ⟨"addsTransformation",
  "Does this Lean edit add an interpreter law or a transformation over a syntax?", .edit⟩
def provesPreservationByInduction : Link := ⟨"provesPreservationByInduction",
  "Does this Lean edit prove the anchored law or transformation's preservation by structural induction, extra state or accumulators generalized?"⟩

/-- Rule 1144: a transformation's preservation proved by structural induction. -/
def preservationByInduction : Rule where
  number := 1144
  keyword := .should
  domain := .softwareEngineering
  formula := ev leanEdit ∧ₗ atom addsTransformation ⟹
    eventually (ev leanEdit ∧ₗ link provesPreservationByInduction) ∨ₗ atom justified

/-! Property tests (rules 1145 to 1159). -/

def statesProperty : Atom := ⟨"statesProperty",
  "Does this edit state a property test?", .edit⟩
def propertyFromCallers : Atom := ⟨"propertyFromCallers",
  "Is the property this edit states taken from what callers assume of the code?", .edit⟩

/-- Rule 1145: properties from what callers assume. -/
def propertiesFromCallers : Rule where
  number := 1145
  keyword := .should
  domain := .softwareEngineering
  formula := ev testEdit ∧ₗ atom statesProperty ⟹ atom propertyFromCallers ∨ₗ atom justified

def combinesRelations : Atom := ⟨"combinesRelations",
  "Does this edit combine several relations for the code under test?", .edit⟩
def statesPropertySetCompleteness : Atom := ⟨"statesPropertySetCompleteness",
  "Does this edit state how complete its set of properties is and what it leaves open?", .edit⟩

/-- Rule 1146: several relations, and how complete the set is. -/
def severalRelations : Rule where
  number := 1146
  keyword := .should
  domain := .softwareEngineering
  formula := ev testEdit ∧ₗ atom statesProperty ⟹
    (atom combinesRelations ∧ₗ atom statesPropertySetCompleteness) ∨ₗ atom justified

def specifiesStatefulCode : Atom := ⟨"specifiesStatefulCode",
  "Does this edit specify or test stateful code?", .edit⟩
def statesStartStepsSafetyLiveness : Atom := ⟨"statesStartStepsSafetyLiveness",
  "Does this edit state where the state may start, how steps change it, what must never happen and what must eventually happen?", .edit⟩

/-- Rule 1147: stateful code's start, steps, safety and liveness. -/
def statefulSpecified : Rule where
  number := 1147
  keyword := .should
  domain := .softwareEngineering
  formula := ev editing ∧ₗ atom specifiesStatefulCode ⟹ atom statesStartStepsSafetyLiveness ∨ₗ
    atom justified

def writesOracle : Atom := ⟨"writesOracle",
  "Does this edit write a test oracle?", .edit⟩
def oracleIndependentPlain : Atom := ⟨"oracleIndependentPlain",
  "Is the oracle this edit writes an independent, simpler version of the code in its plainest form?", .edit⟩
def addsFasterOracle : Atom := ⟨"addsFasterOracle",
  "Does this edit add a faster form of an oracle?", .edit⟩
def checksFasterOracle : Atom := ⟨"checksFasterOracle",
  "Does this edit give the faster form its own equivalence check against the plain one?", .edit⟩

/-- Rule 1148: a plain, independent oracle; a faster one checked against it. -/
def plainOracle : Rule where
  number := 1148
  keyword := .should
  domain := .softwareEngineering
  formula := (ev testEdit ∧ₗ atom writesOracle ⟹ atom oracleIndependentPlain) ∧ₗ
    (ev testEdit ∧ₗ atom addsFasterOracle ⟹ atom checksFasterOracle) ∨ₗ atom justified

def propertyOverEveryInput : Atom := ⟨"propertyOverEveryInput",
  "Does this edit state its property over every input of the domain?", .edit⟩
def labelsProperty : Atom := ⟨"labelsProperty",
  "Does this edit label each property so a failure names it?", .edit⟩

/-- Rule 1149: each property over every input, labelled. -/
def propertiesLabelled : Rule where
  number := 1149
  keyword := .should
  domain := .softwareEngineering
  formula := ev testEdit ∧ₗ atom statesProperty ⟹
    (atom propertyOverEveryInput ∧ₗ atom labelsProperty) ∨ₗ atom justified

def filtersGeneratedInputs : Atom := ⟨"filtersGeneratedInputs",
  "Does this edit meet a domain constraint by filtering or assuming generated inputs instead of constructing them?", .edit⟩
def generatorIgnoresStructure : Atom := ⟨"generatorIgnoresStructure",
  "Does this edit generate inputs without following the domain's structure?", .edit⟩

/-- Rule 1150: inputs built from the domain's structure, constraints by construction. -/
def inputsByConstruction : Rule where
  number := 1150
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev testEdit ∧ₗ (atom filtersGeneratedInputs ∨ₗ atom generatorIgnoresStructure)) ∨ₗ
    atom justified

def generatesThroughInternals : Atom := ⟨"generatesThroughInternals",
  "Does this edit generate abstract values other than through their public constructors?", .edit⟩
def mixesMalformedRaw : Atom := ⟨"mixesMalformedRaw",
  "Does this edit test malformed raw representations other than separately at the boundary that accepts them?", .edit⟩

/-- Rule 1151: abstract values through public constructors; malformed input at its boundary. -/
def publicConstructorsInTests : Rule where
  number := 1151
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev testEdit ∧ₗ (atom generatesThroughInternals ∨ₗ atom mixesMalformedRaw)) ∨ₗ
    atom justified

def shrinkingBreaksConstraints : Atom := ⟨"shrinkingBreaksConstraints",
  "Can the shrinking this edit defines or uses produce inputs outside the property's domain constraints?", .edit⟩

/-- Rule 1152: shrinking keeps the domain's constraints. -/
def shrinkingKeepsDomain : Rule where
  number := 1152
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev testEdit ∧ₗ atom shrinkingBreaksConstraints) ∨ₗ atom justified

def instanceHidesOrder : Atom := ⟨"instanceHidesOrder",
  "Does this edit test polymorphic code at an instance that hides order or multiplicity or adds identities (a commutative or idempotent type)?", .edit⟩

/-- Rule 1153: polymorphic tests at instances exposing order and multiplicity. -/
def revealingInstances : Rule where
  number := 1153
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev testEdit ∧ₗ atom instanceHidesOrder) ∨ₗ atom justified

def samplesSmallDomain : Atom := ⟨"samplesSmallDomain",
  "Does this edit sample a domain small enough to enumerate whole?", .edit⟩
def leavesBoundaryUntested : Atom := ⟨"leavesBoundaryUntested",
  "Does this edit leave a boundary of the domain without an explicit case or an aimed generator?", .edit⟩

/-- Rule 1154: small domains enumerated, boundaries tested. -/
def smallDomainsWhole : Rule where
  number := 1154
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev testEdit ∧ₗ (atom samplesSmallDomain ∨ₗ atom leavesBoundaryUntested)) ∨ₗ
    atom justified

def writesInputGenerator : Atom := ⟨"writesInputGenerator",
  "Does this edit write a generator of test inputs with independently chosen parts?", .edit⟩
def weightsTowardCoincidences : Atom := ⟨"weightsTowardCoincidences",
  "Does the generator this edit writes weight toward coincidences between its independently chosen parts?", .edit⟩

/-- Rule 1155: generators weighted toward coincidences. -/
def generatorsHitCoincidences : Rule where
  number := 1155
  keyword := .should
  domain := .softwareEngineering
  formula := ev testEdit ∧ₗ atom writesInputGenerator ⟹ atom weightsTowardCoincidences ∨ₗ atom justified

def assertsPartOfResult : Atom := ⟨"assertsPartOfResult",
  "Does this edit assert on only part of the result the code under test returns?", .edit⟩
def showsSlowProperty : Atom := ⟨"showsSlowProperty",
  "Does this test run's output show a property test that is slow (a second or more)?", .result⟩

/-- Rule 1156: assert on the whole result; keep properties fast. -/
def wholeResultFastProperties : Rule where
  number := 1156
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev testEdit ∧ₗ atom assertsPartOfResult) ∧ₗ
    never (ev toolResult ∧ₗ atom showsSlowProperty) ∨ₗ atom justified

def needlessExampleTest : Atom := ⟨"needlessExampleTest",
  "Does this edit add an example test where a relation could state the behavior?", .edit⟩
def exampleExpectationFromCode : Atom := ⟨"exampleExpectationFromCode",
  "Does this edit's example test take its expected values from the code rather than working them out apart?", .edit⟩

/-- Rule 1157: example tests only where no relation states the rule, expectations worked apart. -/
def examplesOnlyWhereNeeded : Rule where
  number := 1157
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev testEdit ∧ₗ (atom needlessExampleTest ∨ₗ atom exampleExpectationFromCode)) ∨ₗ
    atom justified

def handRolledPropertyTest : Atom := ⟨"handRolledPropertyTest",
  "Does this edit write a property test without a property-testing library?", .edit⟩
def testOwnedFixedSeed : Atom := ⟨"testOwnedFixedSeed",
  "Does that test use the repository's test framework and a test-owned, fixed-seed random source separate from the code under test's?", .edit⟩

/-- Rule 1158: a hand-rolled property test owns a fixed-seed random source. -/
def handRolledPropertySeed : Rule where
  number := 1158
  keyword := .must
  domain := .softwareEngineering
  formula := ev testEdit ∧ₗ atom handRolledPropertyTest ⟹ atom testOwnedFixedSeed

def runsManyCases : Atom := ⟨"runsManyCases",
  "Does the property test this edit writes run many cases?", .edit⟩
def printsSeedAndInput : Atom := ⟨"printsSeedAndInput",
  "Does the property test this edit writes print its seed and the failing input on failure?", .edit⟩

/-- Rule 1159: many cases per property test; seed and failing input printed. -/
def manyCasesSeedPrinted : Rule where
  number := 1159
  keyword := .must
  domain := .softwareEngineering
  formula := ev testEdit ∧ₗ atom statesProperty ⟹ atom runsManyCases ∧ₗ atom printsSeedAndInput

/-! Mutation testing (rules 1160 to 1175). -/

def changesWiring : Atom := ⟨"changesWiring",
  "Does this edit change a thin wrapper, configuration or integration wiring?", .edit⟩
def integrationCasesFor : Link := ⟨"integrationCasesFor",
  "Does this edit add real positive and negative integration cases for the wiring the anchored edit changes?"⟩
def mutatesWiring : Atom := ⟨"mutatesWiring",
  "Does this mutation run target only thin wrappers, configuration or wiring?", .call⟩

/-- Rule 1160: wiring gets real positive and negative cases, not a mutation campaign. -/
def wiringByIntegrationCases : Rule where
  number := 1160
  keyword := .should
  domain := .softwareEngineering
  formula := (ev editing ∧ₗ atom changesWiring ⟹ eventually (ev testEdit ∧ₗ link integrationCasesFor)) ∧ₗ
    never (ev mutationBatch ∧ₗ atom mutatesWiring) ∨ₗ atom justified

def namesDetectionUncertainty : Atom := ⟨"namesDetectionUncertainty",
  "Does this reply name an uncertainty about whether the tests detect defects in new decision logic?", .reply⟩

/-- Rule 1161: a named detection uncertainty is answered by targeted mutants. -/
def uncertaintyGetsMutants : Rule where
  number := 1161
  keyword := .should
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom namesDetectionUncertainty ⟹ eventually (ev mutationBatch) ∨ₗ
    atom justified

def runsGenericMutants : Atom := ⟨"runsGenericMutants",
  "Does this mutation run generate generic mutants?", .call⟩
def substantialDecisionLogic : Atom := ⟨"substantialDecisionLogic",
  "Is the code this mutation run mutates substantial new decision logic?", .call⟩
def statesCoverageQuestion : Link := ⟨"statesCoverageQuestion",
  "Does this reply state the coverage question the anchored generic mutation run answers?"⟩

/-- Rule 1162: generic mutants only for substantial logic, their question stated first. -/
def genericMutantsJustified : Rule where
  number := 1162
  keyword := .should
  domain := .softwareEngineering
  formula := ev mutationBatch ∧ₗ atom runsGenericMutants ⟹
    (atom substantialDecisionLogic ∧ₗ once (ev reply ∧ₗ link statesCoverageQuestion)) ∨ₗ
    atom justified

def runsVerification : Atom := ⟨"runsVerification",
  "Does this call run a verification step (a test, a check, a review, a mutation run)?", .call⟩
def saysFailureModesSettled : Atom := ⟨"saysFailureModesSettled",
  "Does this reply say the evidence settles the change's failure modes?", .reply⟩

/-- Rule 1163: no further verification once the evidence settles the failure modes, the change
unchanged since. -/
def stopWhenSettled : Rule where
  number := 1163
  keyword := .should
  domain := .softwareEngineering
  formula := ev anyCall ∧ₗ atom runsVerification ⟹
    ¬ₗ since (ev reply ∧ₗ atom saysFailureModesSettled) (ev editing) ∨ₗ atom justified

def overridesUserRequirement : Link := ⟨"overridesUserRequirement",
  "Does this message from the user state a requirement the anchored mutation run departs from for a mutation-testing default?"⟩

/-- Rule 1164: the user's requirements over mutation-testing defaults. -/
def userRequirementsFirst : Rule where
  number := 1164
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev mutationBatch ∧ₗ once (ev user ∧ₗ link overridesUserRequirement))

def writesMutant : Atom := ⟨"writesMutant",
  "Does this edit write a mutant (a targeted mutation spec)?", .edit⟩
def mutantBreaksOneBehavior : Atom := ⟨"mutantBreaksOneBehavior",
  "Does the mutant this edit writes break exactly one guarded behavior?", .edit⟩
def checksIntendedTestFailed : Link := ⟨"checksIntendedTestFailed",
  "Does this reply check that the test meant to kill a mutant of the anchored run is the one that failed?"⟩

/-- Rule 1165: one mutant per guarded behavior, and the intended test is the one failing. -/
def oneMutantPerBehavior : Rule where
  number := 1165
  keyword := .should
  domain := .softwareEngineering
  formula := (ev editing ∧ₗ atom writesMutant ⟹ atom mutantBreaksOneBehavior) ∧ₗ
    (ev mutationBatch ⟹ eventually (ev reply ∧ₗ link checksIntendedTestFailed)) ∨ₗ atom justified

def mutantBreaksUnrelated : Atom := ⟨"mutantBreaksUnrelated",
  "Does the mutant this edit writes break code unrelated to the behavior it targets?", .edit⟩

/-- Rule 1166: each mutant precise. -/
def preciseMutants : Rule where
  number := 1166
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom mutantBreaksUnrelated) ∨ₗ atom justified

def selectsUnbreakableTests : Atom := ⟨"selectsUnbreakableTests",
  "Does the mutant spec this edit writes select tests the mutant can't break?", .edit⟩
def needlessPaths : Atom := ⟨"needlessPaths",
  "Does the mutant spec this edit writes set PATHS for an ordinary layout that discovery handles?", .edit⟩

/-- Rule 1167: each mutant selects only tests it can break; PATHS only for unusual layouts. -/
def mutantTestSelection : Rule where
  number := 1167
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ (atom selectsUnbreakableTests ∨ₗ atom needlessPaths)) ∨ₗ
    atom justified

def expectedOverMinute : Atom := ⟨"expectedOverMinute",
  "Is this mutation run expected to take over a minute?", .call⟩
def runsInBackground : Atom := ⟨"runsInBackground",
  "Does this call run in the background?", .call⟩

/-- Rule 1168: a long mutation batch through the protected launcher, in the background. -/
def longBatchInBackground : Rule where
  number := 1168
  keyword := .should
  domain := .softwareEngineering
  formula := ev mutationBatch ∧ₗ atom expectedOverMinute ⟹
    (ev underLauncher ∧ₗ atom runsInBackground) ∨ₗ atom justified

def startsWorkerPool : Atom := ⟨"startsWorkerPool",
  "Does this edit start a worker pool inside a test that mutation testing runs?", .edit⟩

/-- Rule 1169: no worker pools inside mutation-tested tests. -/
def noPoolsInMutatedTests : Rule where
  number := 1169
  keyword := .mustNot
  domain := .softwareEngineering
  formula := never (ev testEdit ∧ₗ atom startsWorkerPool)

def citesEarlierVerdict : Atom := ⟨"citesEarlierVerdict",
  "Does this reply rest on an earlier verdict (a test, review or mutation result)?", .reply⟩
def isCitedVerdict : Link := ⟨"isCitedVerdict",
  "Is this result the verdict the anchored reply rests on?"⟩
def changesVerdictInputs : Link := ⟨"changesVerdictInputs",
  "Does this edit change an input of the verdict the anchored reply rests on?"⟩

/-- Rule 1170: a verdict stands only while its inputs are unchanged. -/
def noStaleVerdicts : Rule where
  number := 1170
  keyword := .shouldNot
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom citesEarlierVerdict ⟹
    since (ev toolResult ∧ₗ link isCitedVerdict) (ev editing ∧ₗ link changesVerdictInputs) ∨ₗ
    atom justified

def skippedScopePassed : Atom := ⟨"skippedScopePassed",
  "Does this reply count a skipped mutation scope as passed rather than incomplete?", .reply⟩

/-- Rule 1171: a skipped mutation scope is incomplete. -/
def skippedScopesIncomplete : Rule where
  number := 1171
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev reply ∧ₗ atom skippedScopePassed)

def readsMutationReport : Link := ⟨"readsMutationReport",
  "Does this read open the anchored mutation run's report.md, summary.json or a survivor patch?"⟩
def reportsSurvivors : Atom := ⟨"reportsSurvivors",
  "Does this reply report a mutation run's survivors?", .reply⟩
def classifiesSurvivors : Atom := ⟨"classifiesSurvivors",
  "Does this reply classify each survivor as a real gap, equivalent or cosmetic?", .reply⟩
def sameMutationCommand : Link := ⟨"sameMutationCommand",
  "Is this mutation run the same command as the anchored one?"⟩

/-- Rule 1172: a run's report and survivors read and classified; the same command repeated. -/
def survivorsRead : Rule where
  number := 1172
  keyword := .should
  domain := .softwareEngineering
  formula := (ev mutationBatch ⟹ eventually (ev reading ∧ₗ link readsMutationReport)) ∧ₗ
    (ev reply ∧ₗ atom reportsSurvivors ⟹ atom classifiesSurvivors) ∧ₗ
    (ev mutationBatch ∧ₗ once (ev mutationBatch) ⟹ once (ev mutationBatch ∧ₗ link sameMutationCommand)) ∨ₗ
    atom justified

def addsNonDistinctTest : Atom := ⟨"addsNonDistinctTest",
  "Does this edit add a test for a case not logically distinct from an existing test's, rather than strengthen that test?", .edit⟩

/-- Rule 1173: strengthen an existing test before adding one. -/
def strengthenBeforeAdding : Rule where
  number := 1173
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev testEdit ∧ₗ atom addsNonDistinctTest) ∨ₗ atom justified

def removesRedundantTest : Atom := ⟨"removesRedundantTest",
  "Does this edit remove a test flagged redundant?", .edit⟩
def confirmsCoveringTest : Link := ⟨"confirmsCoveringTest",
  "Does this read confirm another test covers the behavior of the test the anchored edit removes?"⟩
def dropsUniqueAssertion : Atom := ⟨"dropsUniqueAssertion",
  "Does this edit drop an assertion of the removed test that no retained test holds?", .edit⟩

/-- Rule 1174: a redundant test goes only once another covers it, its unique assertions moved. -/
def redundantTestRemoval : Rule where
  number := 1174
  keyword := .must
  domain := .softwareEngineering
  formula := ev testEdit ∧ₗ atom removesRedundantTest ⟹
    once (ev reading ∧ₗ link confirmsCoveringTest) ∧ₗ ¬ₗ atom dropsUniqueAssertion

def reportsMutationResult : Atom := ⟨"reportsMutationResult",
  "Does this reply report a mutation run's result?", .reply⟩
def givesAllMutationCounts : Atom := ⟨"givesAllMutationCounts",
  "Does this reply give the run's measured counts of killed, survived, broken, timed out and skipped mutants?", .reply⟩
def saysHowGapsClosed : Atom := ⟨"saysHowGapsClosed",
  "Does this reply name each real gap with how it was closed?", .reply⟩
def survivorsByKind : Atom := ⟨"survivorsByKind",
  "Does this reply list the equivalent and cosmetic survivors by kind?", .reply⟩

/-- Rule 1175: a mutation report gives its measured counts, the gaps closed and survivors by kind. -/
def mutationReportComplete : Rule where
  number := 1175
  keyword := .must
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom reportsMutationResult ⟹
    once (ev mutationBatch) ∧ₗ atom givesAllMutationCounts ∧ₗ atom saysHowGapsClosed ∧ₗ
    atom survivorsByKind

/-! Interactive Lean work (rules 1176 to 1185). -/

def changesSignature : Atom := ⟨"changesSignature",
  "Does this Lean edit change a declaration's signature?", .edit⟩
def readsSignatureContext : Link := ⟨"readsSignatureContext",
  "Does this read open the anchored edit's declaration, its type or its callers (with its Lake project, toolchain and imports)?"⟩

/-- Rule 1176: a signature's declaration and callers read before it changes. -/
def readBeforeSignatureChange : Rule where
  number := 1176
  keyword := .should
  domain := .softwareEngineering
  formula := ev leanEdit ∧ₗ atom changesSignature ⟹
    once (ev reading ∧ₗ link readsSignatureContext) ∨ₗ atom justified

def editsProof : Atom := ⟨"editsProof",
  "Does this Lean edit change a proof?", .edit⟩
def inspectsWithoutExactPosition : Atom := ⟨"inspectsWithoutExactPosition",
  "Does this Lean inspection call omit the exact position (line and column) where several goals or terms share its line?", .call⟩

/-- Rule 1177: the proof state inspected before a proof edit, at exact positions; diagnostics after
each edit. -/
def inspectAndDiagnose : Rule where
  number := 1177
  keyword := .should
  domain := .softwareEngineering
  formula := (ev leanEdit ∧ₗ atom editsProof ⟹ once (ev leanInspect)) ∧ₗ
    never (ev leanInspect ∧ₗ atom inspectsWithoutExactPosition) ∧ₗ
    (ev leanEdit ⟹ eventually (ev leanDiagnostics)) ∨ₗ atom justified

def appliesTacticSuggestion : Atom := ⟨"appliesTacticSuggestion",
  "Does this Lean edit apply a suggestion such as simp? or exact? output?", .edit⟩

/-- Rule 1178: a suggested edit comes from lean_code_actions, applied with the editing tool. -/
def suggestionsFromCodeActions : Rule where
  number := 1178
  keyword := .should
  domain := .softwareEngineering
  formula := ev leanEdit ∧ₗ atom appliesTacticSuggestion ⟹ once (ev leanCodeActions) ∨ₗ
    atom justified

def constructsNewProof : Atom := ⟨"constructsNewProof",
  "Does this Lean edit construct a proof of a statement that might already be proved in the project or its dependencies?", .edit⟩
def usesFoundLemma : Atom := ⟨"usesFoundLemma",
  "Does this Lean edit use a lemma found by a search?", .edit⟩
def checksLemmaSignature : Link := ⟨"checksLemmaSignature",
  "Does this call show the exact type, namespace and implicit parameters of a lemma the anchored edit uses?"⟩

/-- Rule 1179: search before proving again; a found lemma's exact type checked. -/
def searchBeforeProving : Rule where
  number := 1179
  keyword := .should
  domain := .softwareEngineering
  formula := (ev leanEdit ∧ₗ atom constructsNewProof ⟹ once (ev leanLocalSearch)) ∧ₗ
    (ev leanEdit ∧ₗ atom usesFoundLemma ⟹ once (ev leanInspect ∧ₗ link checksLemmaSignature)) ∨ₗ
    atom justified

def triesEveryTactic : Atom := ⟨"triesEveryTactic",
  "Does this multi-attempt call try tactics chosen without regard to the goal's structure (every tactic at hand)?", .call⟩
def trialEditOfOneCandidate : Atom := ⟨"trialEditOfOneCandidate",
  "Does this Lean edit try one tactic candidate of several independent ones by editing the file?", .edit⟩

/-- Rule 1180: tactics from the goal's structure; candidates together through lean_multi_attempt. -/
def tacticsFromGoal : Rule where
  number := 1180
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev leanMultiAttempt ∧ₗ atom triesEveryTactic) ∧ₗ
    never (ev leanEdit ∧ₗ atom trialEditOfOneCandidate) ∨ₗ atom justified

def monolithicSemanticProof : Atom := ⟨"monolithicSemanticProof",
  "Does this Lean edit prove a semantic argument in one piece where helper lemmas would make its missing implication explicit?", .edit⟩

/-- Rule 1181: a semantic argument split into helper lemmas. -/
def helperLemmas : Rule where
  number := 1181
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev leanEdit ∧ₗ atom monolithicSemanticProof) ∨ₗ atom justified

def declaresLeanComplete : Atom := ⟨"declaresLeanComplete",
  "Does this reply declare Lean work complete?", .reply⟩
def isProjectVerification : Link := ⟨"isProjectVerification",
  "Is this result a run of the project's incremental verification command on the work the anchored reply declares complete?"⟩

/-- Rule 1182: completion rests on the project's incremental verification command. -/
def completionByProjectCheck : Rule where
  number := 1182
  keyword := .should
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom declaresLeanComplete ⟹
    once (ev passingResult ∧ₗ link isProjectVerification) ∨ₗ atom justified

def measuresSlowness : Link := ⟨"measuresSlowness",
  "Does this result measure the code the anchored profiling call profiles as slow?"⟩
def optimizesForSpeed : Atom := ⟨"optimizesForSpeed",
  "Does this Lean edit change code to make it faster?", .edit⟩
def claimsSpeedup : Atom := ⟨"claimsSpeedup",
  "Does this reply claim a Lean declaration got faster?", .reply⟩
def sameDeclarationToolchain : Atom := ⟨"sameDeclarationToolchain",
  "Does this reply compare the same declaration on the same toolchain?", .reply⟩

/-- Rule 1183: profiling only measured slowness, optimizing its measured cause, compared like for like. -/
def profileMeasuredSlowness : Rule where
  number := 1183
  keyword := .should
  domain := .softwareEngineering
  formula := (ev leanProfile ⟹ once (ev toolResult ∧ₗ link measuresSlowness)) ∧ₗ
    (ev leanEdit ∧ₗ atom optimizesForSpeed ⟹ once (ev leanProfile)) ∧ₗ
    (ev reply ∧ₗ atom claimsSpeedup ⟹ atom sameDeclarationToolchain) ∨ₗ atom justified

def refactorWithoutGain : Atom := ⟨"refactorWithoutGain",
  "Does this Lean edit refactor or golf with no gain in clarity, reuse or measured cost?", .edit⟩

/-- Rule 1184: refactoring and golfing only for clarity, reuse or measured cost. -/
def refactorForGain : Rule where
  number := 1184
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev leanEdit ∧ₗ atom refactorWithoutGain) ∨ₗ atom justified

def reportsLeanResult : Atom := ⟨"reportsLeanResult",
  "Does this reply report the result of Lean work?", .reply⟩
def statesFallbackLimits : Atom := ⟨"statesFallbackLimits",
  "Does this reply state the limits of compiler-only feedback?", .reply⟩

/-- Rule 1185: Lean through the lean-lsp server; compiler-only work reports its limits. -/
def leanServerOrLimits : Rule where
  number := 1185
  keyword := .should
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom reportsLeanResult ∧ₗ once (ev leanCompile) ∧ₗ ¬ₗ once (ev leanMcpCall) ⟹
    atom statesFallbackLimits ∨ₗ atom justified

/-! Cover letters and stacked merge requests (rules 1186 to 1204). -/

def letterForSingleCommit : Atom := ⟨"letterForSingleCommit",
  "Does this edit write a cover letter for a merge request of a single commit?", .edit⟩
def singleCommitMrCommit : Atom := ⟨"singleCommitMrCommit",
  "Does this commit make the single commit of a merge request?", .call⟩
def carriesDescription : Atom := ⟨"carriesDescription",
  "Does this commit's message carry the context, scope, verification and Refs line?", .call⟩

/-- Rule 1186: a single-commit MR has no cover letter; its commit message is the description. -/
def singleCommitNoLetter : Rule where
  number := 1186
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev coverLetterEdit ∧ₗ atom letterForSingleCommit) ∧ₗ
    (ev gitCommit ∧ₗ atom singleCommitMrCommit ⟹ atom carriesDescription)

def opensWithoutContext : Atom := ⟨"opensWithoutContext",
  "Does this cover letter open with something other than prose giving the context and goal (a commit list, a count line)?", .edit⟩

/-- Rule 1187: a cover letter opens with its context and goal in prose. -/
def letterOpensWithContext : Rule where
  number := 1187
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev coverLetterEdit ∧ₗ atom opensWithoutContext)

def wrongTense : Atom := ⟨"wrongTense",
  "Does this cover letter describe the fixed problem other than in the past tense, or what the MR does other than in the present?", .edit⟩

/-- Rule 1188: the problem in the past tense, the change in the present. -/
def letterTenses : Rule where
  number := 1188
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev coverLetterEdit ∧ₗ atom wrongTense)

def inventedScenario : Atom := ⟨"inventedScenario",
  "Does this description (a cover letter or commit message) state an invented narrow scenario instead of the problem's actual general condition?", .call⟩

/-- Rule 1189: the problem's actual general condition. -/
def generalCondition : Rule where
  number := 1189
  keyword := .must
  domain := .softwareEngineering
  formula := never ((ev coverLetterEdit ∨ₗ ev gitCommit) ∧ₗ atom inventedScenario)

def commentsOnCommitList : Atom := ⟨"commentsOnCommitList",
  "Does this cover letter comment on its commit list, such as by counting the commits?", .edit⟩

/-- Rule 1190: no meta-commentary about the commit list. -/
def noCommitListCommentary : Rule where
  number := 1190
  keyword := .mustNot
  domain := .softwareEngineering
  formula := never (ev coverLetterEdit ∧ₗ atom commentsOnCommitList)

def longCommitSummary : Atom := ⟨"longCommitSummary",
  "Does this cover letter give a commit a long summary or repeat its commit message's rationale?", .edit⟩

/-- Rule 1191: short commit summaries, no repeated rationale. -/
def shortCommitSummaries : Rule where
  number := 1191
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev coverLetterEdit ∧ₗ atom longCommitSummary) ∨ₗ atom justified

def sectionsForSmallChange : Atom := ⟨"sectionsForSmallChange",
  "Does this cover letter use grouped ## sections for a change that isn't large and multi-area?", .edit⟩

/-- Rule 1192: sections only for large multi-area changes, the context paragraph still first. -/
def sectionsOnlyWhenLarge : Rule where
  number := 1192
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev coverLetterEdit ∧ₗ (atom sectionsForSmallChange ∨ₗ atom opensWithoutContext))

def refsLinesWrong : Atom := ⟨"refsLinesWrong",
  "Does this cover letter end other than with exactly one Refs: <ticket URL> line per ticket and nothing after?", .edit⟩

/-- Rule 1193: the letter ends with one Refs line per ticket. -/
def refsAtEnd : Rule where
  number := 1193
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev coverLetterEdit ∧ₗ atom refsLinesWrong)

def reworksReviewedBranch : Atom := ⟨"reworksReviewedBranch",
  "Does this commit rework a branch under review?", .call⟩
def noteForRework : Link := ⟨"noteForRework",
  "Does this version note cover the anchored rework?"⟩

/-- Rule 1194: every rework of a branch under review writes its version note in the same step: the
note since the commit before the rework, or after it with no commit in between (the next commit
refused while a rework without a note since its own previous commit has no note edit after it). -/
def versionNoteWithRework : Rule where
  number := 1194
  keyword := .must
  domain := .softwareEngineering
  formula := (ev gitCommit ∧ₗ atom reworksReviewedBranch ⟹
      since (ev versionNoteEdit ∧ₗ link noteForRework) (ev gitCommit) ∨ₗ
        eventually (ev versionNoteEdit ∧ₗ link noteForRework)) ∧ₗ
    (ev gitCommit ⟹
      ¬ₗ since (ev gitCommit ∧ₗ atom reworksReviewedBranch ∧ₗ
          ¬ₗ since (ev versionNoteEdit ∧ₗ link noteForRework) (ev gitCommit))
        (ev versionNoteEdit))

def updatesLetterForNote : Link := ⟨"updatesLetterForNote",
  "Does this edit update the cover letter as the whole description for the anchored version note's rework?"⟩

/-- Rule 1195: a version note comes with the cover letter updated as the whole description, when it
is written: the update since the commit before the note, or after it with no commit in between. -/
def letterWithNote : Rule where
  number := 1195
  keyword := .must
  domain := .softwareEngineering
  formula := (ev versionNoteEdit ⟹
      since (ev coverLetterEdit ∧ₗ link updatesLetterForNote) (ev gitCommit) ∨ₗ
        eventually (ev coverLetterEdit ∧ₗ link updatesLetterForNote)) ∧ₗ
    (ev gitCommit ⟹
      ¬ₗ since (ev versionNoteEdit ∧ₗ
          ¬ₗ since (ev coverLetterEdit ∧ₗ link updatesLetterForNote) (ev gitCommit))
        (ev coverLetterEdit))

def noteNotFlatPerChange : Atom := ⟨"noteNotFlatPerChange",
  "Is this version note other than one flat bullet list, one bullet per review comment or change?", .edit⟩
def noteOutOfDiffOrder : Atom := ⟨"noteOutOfDiffOrder",
  "Does this version note list its bullets out of the diff's reading order?", .edit⟩
def noteMissingHowChecked : Atom := ⟨"noteMissingHowChecked",
  "Does a bullet of this version note leave out how its change was checked?", .edit⟩

/-- Rule 1196: a version note is one flat list, in diff order, each item with how it was checked. -/
def versionNoteShape : Rule where
  number := 1196
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev versionNoteEdit ∧ₗ
    (atom noteNotFlatPerChange ∨ₗ atom noteOutOfDiffOrder ∨ₗ atom noteMissingHowChecked))

def noteForRebaseOnly : Atom := ⟨"noteForRebaseOnly",
  "Is this version note for a stacked branch whose only change is a rebase?", .edit⟩

/-- Rule 1197: no version note for a rebase alone. -/
def noNoteForRebase : Rule where
  number := 1197
  keyword := .mustNot
  domain := .softwareEngineering
  formula := never (ev versionNoteEdit ∧ₗ atom noteForRebaseOnly)

def dependsOnAnchoredMr : Link := ⟨"dependsOnAnchoredMr",
  "Does the MR this call opened depend on the MR the anchored call opens?"⟩

/-- Rule 1198: MRs opened in dependency order. -/
def mrsInDependencyOrder : Rule where
  number := 1198
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev mrCreate ∧ₗ once (ev mrCreate ∧ₗ link dependsOnAnchoredMr))

def pushesForGitlab : Atom := ⟨"pushesForGitlab",
  "Does this push send a branch for a GitLab merge request?", .push⟩

/-- Rule 1199: `glab auth status` before pushing. -/
def signInCheckedBeforePush : Rule where
  number := 1199
  keyword := .must
  domain := .softwareEngineering
  formula := ev push ∧ₗ atom pushesForGitlab ⟹ once (ev glabAuthStatus)

def dependentNotStacked : Atom := ⟨"dependentNotStacked",
  "Does this call open a dependent MR whose branch isn't built on its base or doesn't target it?", .call⟩

/-- Rule 1200: dependent MRs stacked, each on and targeting its base. -/
def stackedMrs : Rule where
  number := 1200
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev mrCreate ∧ₗ atom dependentNotStacked)

def pushesNewMrBranch : Atom := ⟨"pushesNewMrBranch",
  "Does this push send a branch whose MR is not opened yet?", .push⟩

/-- Rule 1201: push and open MRs one at a time. -/
def oneMrAtATime : Rule where
  number := 1201
  keyword := .must
  domain := .softwareEngineering
  formula := ev push ∧ₗ atom pushesNewMrBranch ⟹
    ¬ₗ since (ev push ∧ₗ atom pushesNewMrBranch) (ev mrCreate)

def pushesDependentMr : Atom := ⟨"pushesDependentMr",
  "Does this push send the branch of an MR that depends on earlier MRs?", .push⟩
def linksEarlierMrs : Link := ⟨"linksEarlierMrs",
  "Does this edit give the anchored push's MR description GitLab links to every earlier MR it depends on?"⟩

/-- Rule 1202: a dependent MR's description links its earlier MRs before its push. -/
def dependentLinksEarlier : Rule where
  number := 1202
  keyword := .must
  domain := .softwareEngineering
  formula := ev push ∧ₗ atom pushesDependentMr ⟹ once (ev coverLetterEdit ∧ₗ link linksEarlierMrs)

def omitsOrderConstraint : Atom := ⟨"omitsOrderConstraint",
  "Does this description (a cover letter or commit message) leave a merge, deploy or health constraint unstated, or not say there is none?", .call⟩

/-- Rule 1203: each order constraint stated, or none said. -/
def orderConstraintsStated : Rule where
  number := 1203
  keyword := .must
  domain := .softwareEngineering
  formula := never ((ev coverLetterEdit ∨ₗ ev gitCommit) ∧ₗ atom omitsOrderConstraint)

def recordsMrUrl : Atom := ⟨"recordsMrUrl",
  "Does this edit record an opened MR's URL in the task's records?", .edit⟩

/-- Rule 1204: each opened MR's URL recorded before the next MR. -/
def mrUrlRecorded : Rule where
  number := 1204
  keyword := .must
  domain := .softwareEngineering
  formula := ev mrCreate ⟹
    eventually (ev editing ∧ₗ atom recordsMrUrl) ∧ₗ ¬ₗ since (ev mrCreate) (ev editing ∧ₗ atom recordsMrUrl)

/-! Moving changes between commits (rules 1205 to 1213). -/

def mapsEveryMove : Link := ⟨"mapsEveryMove",
  "Does this step map every move of the anchored rebase: source commit, target commit and each piece's exact text?"⟩

/-- Rule 1205: every move mapped before the rebase. -/
def movesMappedFirst : Rule where
  number := 1205
  keyword := .must
  domain := .softwareEngineering
  formula := ev anyCall ∧ₗ atom movesChanges ⟹ once ((ev reply ∨ₗ ev editing) ∧ₗ link mapsEveryMove)

def reversesCut : Atom := ⟨"reversesCut",
  "Does this edit build an intermediate state by reversing a cut instead of from the original files?", .edit⟩

/-- Rule 1206: intermediate states from the original files. -/
def statesFromOriginals : Rule where
  number := 1206
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev editing ∧ₗ atom reversesCut)

def leavesDraggedAlong : Atom := ⟨"leavesDraggedAlong",
  "Does this commit, moving a piece out, leave behind what the piece dragged along (imports, test assertions, fixture fields, doc comments)?", .call⟩

/-- Rule 1207: what a moved piece drags along goes with it. -/
def removeDraggedAlong : Rule where
  number := 1207
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev gitCommit ∧ₗ atom leavesDraggedAlong)

def whileSplittingCommit : Atom := ⟨"whileSplittingCommit",
  "Does this staging serve splitting a commit?", .call⟩

/-- Rule 1208: exact-text cut specs, not interactive staging, to split commits. -/
def cutSpecsNotInteractive : Rule where
  number := 1208
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev interactiveStaging ∧ₗ atom whileSplittingCommit)

def malformedTodoLine : Atom := ⟨"malformedTodoLine",
  "Does this edit write a rebase todo line other than as pick <hash> # <subject>?", .edit⟩

/-- Rule 1209: the todo through mark_edit.py and reorder_todo.py, its lines `pick <hash> # <subject>`. -/
def todoThroughTools : Rule where
  number := 1209
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev sequenceEditorRebase ∧ₗ ¬ₗ ev todoToolsUsed) ∧ₗ
    never (ev editing ∧ₗ atom malformedTodoLine)

def misplacesFixup : Atom := ⟨"misplacesFixup",
  "Does this call place a fixup in a rebase todo wrongly: one whose target is earlier other than as plain fixup after it, or one whose target is later other than as fixup -C before it?", .call⟩

/-- Rule 1210: a fixup's form and place follow its target's position. -/
def fixupPlacement : Rule where
  number := 1210
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev anyCall ∧ₗ atom misplacesFixup)

def pureEditForEarlier : Atom := ⟨"pureEditForEarlier",
  "Does this commit hold a pure edit, moving nothing, that belongs to an earlier commit?", .call⟩

/-- Rule 1211: a pure edit as `git commit --fixup` and an autosquash rebase. -/
def pureEditsAsFixups : Rule where
  number := 1211
  keyword := .must
  domain := .softwareEngineering
  formula := (ev gitCommit ∧ₗ atom pureEditForEarlier ⟹ ev fixupCommit) ∧ₗ
    (ev fixupCommit ⟹ eventually (ev autosquashRebase))

def commitsLeftover : Atom := ⟨"commitsLeftover",
  "Does this commit make a leftover of a split meant to fold into another commit?", .call⟩

/-- Rule 1212: a leftover keeps its target's authorship. -/
def leftoverAuthorship : Rule where
  number := 1212
  keyword := .should
  domain := .softwareEngineering
  formula := ev gitCommit ∧ₗ atom commitsLeftover ⟹ ev authorFromTarget ∨ₗ atom justified

def quotesTargetSubject : Atom := ⟨"quotesTargetSubject",
  "Does this leftover commit's message quote its target's subject exactly?", .call⟩

/-- Rule 1213: a leftover's message is exactly "leftover for: <target subject>". -/
def leftoverMessageExact : Rule where
  number := 1213
  keyword := .must
  domain := .softwareEngineering
  formula := ev gitCommit ∧ₗ atom commitsLeftover ⟹ ev leftoverMessage ∧ₗ atom quotesTargetSubject

/-! Correspondence (rules 1214 to 1221). -/

def showsMessageDraft : Atom := ⟨"showsMessageDraft",
  "Does this reply show the user a drafted message to someone?", .reply⟩

/-- Rule 1214: a draft in a private message file, after its ledger, before it is shown. -/
def draftAfterLedger : Rule where
  number := 1214
  keyword := .must
  domain := .discipline
  formula := (ev messageDraftEdit ⟹ ev privateEdit ∧ₗ once (ev ledgerEdit)) ∧ₗ
    (ev reply ∧ₗ atom showsMessageDraft ⟹ once (ev messageDraftEdit))

def showsTranslatedDraft : Atom := ⟨"showsTranslatedDraft",
  "Does this reply show a draft to be sent in a language other than English?", .reply⟩

/-- Rule 1215: the English draft stays the source; its translation beside it. -/
def englishSourceKept : Rule where
  number := 1215
  keyword := .must
  domain := .discipline
  formula := (ev translationEdit ⟹ once (ev messageDraftEdit)) ∧ₗ
    (ev reply ∧ₗ atom showsTranslatedDraft ⟹ once (ev translationEdit))

def changesDraftFact : Atom := ⟨"changesDraftFact",
  "Does this edit change a fact a message draft states?", .edit⟩

/-- Rule 1216: a change goes ledger, English draft, translation, each in its own message. -/
def messageChangeOrder : Rule where
  number := 1216
  keyword := .must
  domain := .discipline
  formula := (ev messageDraftEdit ∧ₗ atom changesDraftFact ⟹ once (ev ledgerEdit)) ∧ₗ
    (ev translationEdit ⟹ once (ev messageDraftEdit)) ∧ₗ never (sameMessage messageFilesTogether)

def formalChat : Atom := ⟨"formalChat",
  "Is this chat message to a daily colleague other than short, informal and direct, as the user would type it?", .edit⟩

/-- Rule 1217: short, informal, direct chat to daily colleagues. -/
def informalChat : Rule where
  number := 1217
  keyword := .must
  domain := .discipline
  formula := never (ev messageDraftEdit ∧ₗ atom formalChat)

def chatBuriesPoint : Atom := ⟨"chatBuriesPoint",
  "Does this chat message open other than with its point in one line, reason included?", .edit⟩

/-- Rule 1218: a chat message opens with its point and reason. -/
def pointFirst : Rule where
  number := 1218
  keyword := .must
  domain := .discipline
  formula := never (ev messageDraftEdit ∧ₗ atom chatBuriesPoint)

def requestWithoutWhy : Atom := ⟨"requestWithoutWhy",
  "Does this message make a request without saying why this person is asked?", .edit⟩

/-- Rule 1219: a request says why this person is asked. -/
def requestSaysWhy : Rule where
  number := 1219
  keyword := .must
  domain := .discipline
  formula := never (ev messageDraftEdit ∧ₗ atom requestWithoutWhy)

def needlessExplanation : Atom := ⟨"needlessExplanation",
  "Does this message explain something the colleague doesn't need to act on?", .edit⟩
def explainsToolOutput : Atom := ⟨"explainsToolOutput",
  "Does this message explain how to read a command's output to someone who knows the tool?", .edit⟩

/-- Rule 1220: no explanation the colleague doesn't need. -/
def onlyNeededExplanation : Rule where
  number := 1220
  keyword := .must
  domain := .discipline
  formula := never (ev messageDraftEdit ∧ₗ (atom needlessExplanation ∨ₗ atom explainsToolOutput))

def externalWithoutGreeting : Atom := ⟨"externalWithoutGreeting",
  "Does this message to an external reader lack the \"Hi NAME,\" opening or polite phrasing?", .edit⟩
def colleagueGreeting : Atom := ⟨"colleagueGreeting",
  "Does this message to a daily colleague have a greeting or a sign-off?", .edit⟩

/-- Rule 1221: "Hi NAME," and politeness for external readers; none for daily colleagues. -/
def greetingByAudience : Rule where
  number := 1221
  keyword := .must
  domain := .discipline
  formula := never (ev messageDraftEdit ∧ₗ (atom externalWithoutGreeting ∨ₗ atom colleagueGreeting))

/-! Paper writing (rules 1222 to 1244). -/

def startsPaperDraft : Atom := ⟨"startsPaperDraft",
  "Does this edit start drafting a paper?", .edit⟩
def establishesPaperBasis : Link := ⟨"establishesPaperBasis",
  "Does this step establish the anchored paper's audience, scope, main contribution and evidence?"⟩
def asksImmaterialChoice : Atom := ⟨"asksImmaterialChoice",
  "Does this reply ask the user about a writing choice that doesn't materially matter?", .reply⟩

/-- Rule 1222: audience, scope, contribution and evidence before drafting; questions only that matter. -/
def paperBasisFirst : Rule where
  number := 1222
  keyword := .must
  domain := .mathematics
  formula := (ev editing ∧ₗ atom startsPaperDraft ⟹
      once ((ev reply ∨ₗ ev editing) ∧ₗ link establishesPaperBasis)) ∧ₗ
    never (ev reply ∧ₗ atom asksImmaterialChoice)

def manuscriptNeedsConversation : Atom := ⟨"manuscriptNeedsConversation",
  "Does this edit leave a publishable manuscript's claims, references, contribution statement, copyediting or layout depending on the conversation?", .edit⟩

/-- Rule 1223: a publishable manuscript stands alone. -/
def standaloneManuscript : Rule where
  number := 1223
  keyword := .must
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom manuscriptNeedsConversation)

def contributionNotEarly : Atom := ⟨"contributionNotEarly",
  "Does this edit leave a research paper's problem, exact contribution or scope out of its opening, or its main result or relation to prior work out of the introduction?", .edit⟩

/-- Rule 1224: problem, contribution and scope early. -/
def contributionEarly : Rule where
  number := 1224
  keyword := .must
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom contributionNotEarly)

def proofWithoutOverview : Atom := ⟨"proofWithoutOverview",
  "Does this edit give an argument of several nontrivial components without a short overview explaining its main obstacle?", .edit⟩

/-- Rule 1225: a proof overview for arguments of several components. -/
def proofOverview : Rule where
  number := 1225
  keyword := .should
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom proofWithoutOverview) ∨ₗ atom justified

def spaceNotByDifficulty : Atom := ⟨"spaceNotByDifficulty",
  "Does this edit spend space against difficulty (routine checks developed, novel steps compressed, optional material in the main text)?", .edit⟩

/-- Rule 1226: space allocated by difficulty. -/
def spaceByDifficulty : Rule where
  number := 1226
  keyword := .should
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom spaceNotByDifficulty) ∨ₗ atom justified

def resultMissingHypotheses : Atom := ⟨"resultMissingHypotheses",
  "Does this edit state a result without the hypotheses needed to apply it?", .edit⟩
def theoremMixedWithProof : Atom := ⟨"theoremMixedWithProof",
  "Does this edit mix a theorem's statement with its proof?", .edit⟩
def buriesRestriction : Atom := ⟨"buriesRestriction",
  "Does this edit put a result's restriction in a distant remark?", .edit⟩

/-- Rule 1227: results with their hypotheses, apart from their proofs, restrictions in place. -/
def resultsWithHypotheses : Rule where
  number := 1227
  keyword := .must
  domain := .mathematics
  formula := never (ev editing ∧ₗ
    (atom resultMissingHypotheses ∨ₗ atom theoremMixedWithProof ∨ₗ atom buriesRestriction))

def longArgumentUnsplit : Atom := ⟨"longArgumentUnsplit",
  "Does this edit give a long argument without lemmas of short descriptive names and connecting transitions?", .edit⟩

/-- Rule 1228: long arguments in named lemmas. -/
def argumentsInLemmas : Rule where
  number := 1228
  keyword := .should
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom longArgumentUnsplit) ∨ₗ atom justified

def callsStepObvious : Atom := ⟨"callsStepObvious",
  "Does this edit call a step \"obvious\" or \"easy\" without its short reason?", .edit⟩

/-- Rule 1229: no "obvious" or "easy" without the reason. -/
def noObviousClaims : Rule where
  number := 1229
  keyword := .must
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom callsStepObvious)

def definitionBeforeQuestion : Atom := ⟨"definitionBeforeQuestion",
  "Does this edit give a definition before the reader meets its question, or start an explanation from what the reader can't picture?", .edit⟩

/-- Rule 1230: explanations start from what the reader can picture. -/
def questionBeforeDefinition : Rule where
  number := 1230
  keyword := .must
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom definitionBeforeQuestion)

def tighteningDropsExplanation : Atom := ⟨"tighteningDropsExplanation",
  "Does this tightening edit drop an explanatory passage?", .edit⟩
def tightensText : Atom := ⟨"tightensText",
  "Does this edit tighten a manuscript's text?", .edit⟩
def comparesWithOriginal : Link := ⟨"comparesWithOriginal",
  "Does this reply compare the anchored edit's revision with the original for lost reasoning?"⟩

/-- Rule 1231: tightening keeps explanations, checked against the original. -/
def tighteningKeepsReasoning : Rule where
  number := 1231
  keyword := .must
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom tighteningDropsExplanation) ∧ₗ
    (ev editing ∧ₗ atom tightensText ⟹ eventually (ev reply ∧ₗ link comparesWithOriginal))

def multiStageArgument : Atom := ⟨"multiStageArgument",
  "Does this edit write an argument that transforms its objects through several stages?", .edit⟩
def overarchingExample : Atom := ⟨"overarchingExample",
  "Does this edit carry an example whose objects survive the stages, mapping each stage's lemma, hypotheses and preserved quantities?", .edit⟩

/-- Rule 1232: an overarching example through a multi-stage argument. -/
def runningExample : Rule where
  number := 1232
  keyword := .should
  domain := .mathematics
  formula := ev editing ∧ₗ atom multiStageArgument ⟹ atom overarchingExample ∨ₗ atom justified

def illustrationsInOverview : Atom := ⟨"illustrationsInOverview",
  "Does this edit put illustrations in the overview rather than where their technique is developed?", .edit⟩

/-- Rule 1233: illustrations where their technique is developed. -/
def illustrationsInPlace : Rule where
  number := 1233
  keyword := .must
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom illustrationsInOverview)

def figureConflates : Atom := ⟨"figureConflates",
  "Does this edit's figure conflate a mathematical object with its evaluation?", .edit⟩

/-- Rule 1234: figures keep objects distinct from their evaluations. -/
def figuresDistinguish : Rule where
  number := 1234
  keyword := .must
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom figureConflates)

def polishesFrontMatter : Atom := ⟨"polishesFrontMatter",
  "Does this edit polish a manuscript's title, abstract, contribution claims or conclusion?", .edit⟩
def settlesArgumentScope : Link := ⟨"settlesArgumentScope",
  "Does this reply settle the argument and scope of the manuscript the anchored edit polishes?"⟩
def frontMatterDisagrees : Atom := ⟨"frontMatterDisagrees",
  "Does this edit leave the title, abstract, contribution claims and conclusion describing different results?", .edit⟩

/-- Rule 1235: argument and scope settled before the front matter, which agrees with itself. -/
def frontMatterLast : Rule where
  number := 1235
  keyword := .must
  domain := .mathematics
  formula := (ev editing ∧ₗ atom polishesFrontMatter ⟹ once (ev reply ∧ₗ link settlesArgumentScope)) ∧ₗ
    never (ev editing ∧ₗ atom frontMatterDisagrees)

def reviewDemonstratesError : Atom := ⟨"reviewDemonstratesError",
  "Does this result, a review, demonstrate an error or a missing assumption in a manuscript?", .result⟩
def resolvesReviewError : Link := ⟨"resolvesReviewError",
  "Does this edit resolve the error or missing assumption the anchored review demonstrates?"⟩
def removesVoiceForPreference : Atom := ⟨"removesVoiceForPreference",
  "Does this edit remove effective humor, voice or illustration on a reviewer's preference alone?", .edit⟩

/-- Rule 1236: demonstrated errors resolved; voice kept against mere preference. -/
def reviewErrorsResolved : Rule where
  number := 1236
  keyword := .must
  domain := .mathematics
  formula := (ev toolResult ∧ₗ atom reviewDemonstratesError ⟹
      eventually (ev editing ∧ₗ link resolvesReviewError)) ∧ₗ
    never (ev editing ∧ₗ atom removesVoiceForPreference)

def substantiveManuscriptChange : Atom := ⟨"substantiveManuscriptChange",
  "Does this edit make a substantive change to a publishable manuscript?", .edit⟩
def wholeCopyeditPass : Atom := ⟨"wholeCopyeditPass",
  "Is this edit a separate copyediting pass over the whole manuscript?", .edit⟩

/-- Rule 1237: a whole-manuscript copyediting pass after substantive changes. -/
def copyeditAfterChanges : Rule where
  number := 1237
  keyword := .must
  domain := .mathematics
  formula := ev editing ∧ₗ atom substantiveManuscriptChange ⟹
    eventually (ev editing ∧ₗ atom wholeCopyeditPass)

def narratesOwnPedagogy : Atom := ⟨"narratesOwnPedagogy",
  "Does this edit leave narration of the manuscript's own pedagogy in it?", .edit⟩

/-- Rule 1238: no narration of the manuscript's own pedagogy. -/
def noPedagogyNarration : Rule where
  number := 1238
  keyword := .must
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom narratesOwnPedagogy)

def deliversUnrequested : Atom := ⟨"deliversUnrequested",
  "Does this reply deliver an artifact beyond the one requested?", .reply⟩
def removesEditableSources : Atom := ⟨"removesEditableSources",
  "Does this call make a deliverable's editable sources unavailable?", .call⟩

/-- Rule 1239: only the requested artifact delivered, its sources kept. -/
def requestedArtifactOnly : Rule where
  number := 1239
  keyword := .must
  domain := .mathematics
  formula := never (ev reply ∧ₗ atom deliversUnrequested) ∧ₗ
    never (ev anyCall ∧ₗ atom removesEditableSources)

def deliversPdf : Atom := ⟨"deliversPdf",
  "Does this reply deliver a rendered PDF?", .reply⟩
def repaginatesDelivered : Link := ⟨"repaginatesDelivered",
  "Does this edit repaginate the PDF the anchored reply delivers?"⟩
def viewsEveryPage : Link := ⟨"viewsEveryPage",
  "Does this read view every page of the PDF the anchored reply delivers?"⟩

/-- Rule 1240: rendered pages inspected, all of them after a repagination. -/
def pdfInspected : Rule where
  number := 1240
  keyword := .must
  domain := .mathematics
  formula := ev reply ∧ₗ atom deliversPdf ⟹
    once (ev pdfRead) ∧ₗ
    (once (ev editing ∧ₗ link repaginatesDelivered) ⟹
      since (ev pdfRead ∧ₗ link viewsEveryPage) (ev editing ∧ₗ link repaginatesDelivered))

def buildsOutsideWorkflow : Atom := ⟨"buildsOutsideWorkflow",
  "Does this call build or validate a document other than through the repository's existing workflow for its format?", .call⟩

/-- Rule 1241: the repository's own build and validation workflow. -/
def repositoryWorkflow : Rule where
  number := 1241
  keyword := .must
  domain := .mathematics
  formula := never (ev anyCall ∧ₗ atom buildsOutsideWorkflow)

def runsBuildOrValidation : Atom := ⟨"runsBuildOrValidation",
  "Does this call run a check (a build, a validation, a test)?", .call⟩
def passOfSameCheck : Link := ⟨"passOfSameCheck",
  "Is this passing result a run of the same check the anchored call runs?"⟩

/-- Rule 1242: a passed check repeated only after a change, a failure or a concern. -/
def reusePassedChecks : Rule where
  number := 1242
  keyword := .should
  domain := .mathematics
  formula := ev anyCall ∧ₗ atom runsBuildOrValidation ⟹
    ¬ₗ since (ev passingResult ∧ₗ link passOfSameCheck) (ev editing) ∨ₗ atom justified

def closesManuscriptWork : Atom := ⟨"closesManuscriptWork",
  "Does this reply close a round of work on a document?", .reply⟩
def reportsEditsChecksGaps : Atom := ⟨"reportsEditsChecksGaps",
  "Does this reply report the edits and checks performed and name the remaining substantive gaps?", .reply⟩

/-- Rule 1243: the edits and checks actually performed, and the gaps left. -/
def reportWorkDone : Rule where
  number := 1243
  keyword := .must
  domain := .mathematics
  formula := ev reply ∧ₗ atom closesManuscriptWork ⟹
    atom reportsEditsChecksGaps ∧ₗ ¬ₗ atom inventsProgress

def replacesTypesetting : Atom := ⟨"replacesTypesetting",
  "Does this call replace good typesetting with raw source?", .call⟩
def callsRawSourceFidelity : Atom := ⟨"callsRawSourceFidelity",
  "Does this reply call raw source in place of typesetting greater fidelity?", .reply⟩

/-- Rule 1244: typesetting kept, raw source not called fidelity. -/
def keepTypesetting : Rule where
  number := 1244
  keyword := .mustNot
  domain := .mathematics
  formula := never (ev anyCall ∧ₗ atom replacesTypesetting) ∧ₗ
    never (ev reply ∧ₗ atom callsRawSourceFidelity)

/-! Reviewing a colleague's merge request (rules 1245 to 1260). -/

def startsHunkLedger : Atom := ⟨"startsHunkLedger",
  "Does this call start a review's hunk-ledger phase?", .call⟩
def finishesClassicDraft : Atom := ⟨"finishesClassicDraft",
  "Does this edit finish the classic review's draft?", .edit⟩

/-- Rule 1245: the classic review's draft finished before the hunk ledger. -/
def classicReviewFirst : Rule where
  number := 1245
  keyword := .must
  domain := .softwareEngineering
  formula := ev anyCall ∧ₗ atom startsHunkLedger ⟹ once (ev reviewDraftEdit ∧ₗ atom finishesClassicDraft)

def omitsSyncRestarts : Atom := ⟨"omitsSyncRestarts",
  "Does this review draft leave unasked what rolls or restarts when the change syncs, and whether the description says so?", .edit⟩

/-- Rule 1246: what rolls or restarts on sync is asked. -/
def askWhatRestarts : Rule where
  number := 1246
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev reviewDraftEdit ∧ₗ atom omitsSyncRestarts)

def readsBeyondDiff : Link := ⟨"readsBeyondDiff",
  "Does this read open, beyond the diff, what the anchored review's change hands its workload and what the change fails to do?"⟩

/-- Rule 1247: the review looks beyond the diff, at what the change hands its workload and what it
fails to do. -/
def lookBeyondDiff : Rule where
  number := 1247
  keyword := .must
  domain := .softwareEngineering
  formula := ev reviewDraftEdit ⟹ once ((ev reading ∨ₗ ev searchCall) ∧ₗ link readsBeyondDiff)

def commentsOnName : Atom := ⟨"commentsOnName",
  "Does this review draft comment on a name, label or setting?", .edit⟩
def findsEveryOccurrence : Link := ⟨"findsEveryOccurrence",
  "Does this call find every place the name, label or setting the anchored review comments on appears?"⟩

/-- Rule 1248: every place a name appears read side by side. -/
def everyOccurrenceRead : Rule where
  number := 1248
  keyword := .must
  domain := .softwareEngineering
  formula := ev reviewDraftEdit ∧ₗ atom commentsOnName ⟹
    once ((ev reading ∨ₗ ev searchCall) ∧ₗ link findsEveryOccurrence)

def readsExistingInstance : Link := ⟨"readsExistingInstance",
  "Does this call read how an existing instance of the same thing does what the anchored review's change does?"⟩

def leavesDifferenceUnasked : Atom := ⟨"leavesDifferenceUnasked",
  "Does this review draft leave unasked why the change differs from how existing instances of the same thing do it?", .edit⟩

/-- Rule 1249: the change compared with existing instances, and why it differs asked. -/
def compareWithInstances : Rule where
  number := 1249
  keyword := .must
  domain := .softwareEngineering
  formula := ev reviewDraftEdit ⟹
    once ((ev reading ∨ₗ ev searchCall) ∧ₗ link readsExistingInstance) ∧ₗ ¬ₗ atom leavesDifferenceUnasked

def readsCommitMessages : Link := ⟨"readsCommitMessages",
  "Does this call show the commit messages of the change the anchored review reviews?"⟩

/-- Rule 1250: the change's commit messages read against its final code. -/
def messagesAgainstCode : Rule where
  number := 1250
  keyword := .must
  domain := .softwareEngineering
  formula := ev reviewDraftEdit ⟹ once (ev gitLog ∧ₗ link readsCommitMessages)

def asksAboutEnumeratedReviewer : Atom := ⟨"asksAboutEnumeratedReviewer",
  "Does this reply ask the user whether to add an enumerated reviewer?", .reply⟩

/-- Rule 1251: the enumerated reviewer asked about at the start, the review going on meanwhile. -/
def enumeratedReviewerAsked : Rule where
  number := 1251
  keyword := .must
  domain := .softwareEngineering
  formula := (ev reviewDraftEdit ⟹ once (ev reply ∧ₗ atom asksAboutEnumeratedReviewer)) ∧ₗ
    never (ev reply ∧ₗ atom asksAboutEnumeratedReviewer ∧ₗ atom asksUserAndStops)

def briefsMrReviewer : Atom := ⟨"briefsMrReviewer",
  "Does this agent call brief a reviewer of a merge request?", .call⟩
def briefBeyondDiff : Atom := ⟨"briefBeyondDiff",
  "Does this reviewer brief give more than the diff, its commit messages and the description?", .call⟩

/-- Rule 1252: reviewers get the diff, messages and description only, on the cheaper model. -/
def leanReviewerBrief : Rule where
  number := 1252
  keyword := .should
  domain := .softwareEngineering
  formula := ev agentRun ∧ₗ atom briefsMrReviewer ⟹
    (¬ₗ atom briefBeyondDiff ∧ₗ ev cheaperModel) ∨ₗ atom justified

def raisesSelfClosingPoint : Atom := ⟨"raisesSelfClosingPoint",
  "Does this review draft raise as a comment a point that blocks nothing and closes by itself, instead of moving it to \"Checked, no comment\"?", .edit⟩
def withholdsApproval : Atom := ⟨"withholdsApproval",
  "Does this review draft withhold approval when only such points remain?", .edit⟩

/-- Rule 1253: self-closing points under "Checked, no comment", and approve. -/
def nonBlockingPointsChecked : Rule where
  number := 1253
  keyword := .should
  domain := .softwareEngineering
  formula := never (ev reviewDraftEdit ∧ₗ (atom raisesSelfClosingPoint ∨ₗ atom withholdsApproval)) ∨ₗ
    atom justified

def raisesAnsweredPoint : Atom := ⟨"raisesAnsweredPoint",
  "Does this review draft raise again a point the author answered or one waiting on a decision?", .edit⟩

/-- Rule 1254: an answered or waiting point isn't raised again. -/
def noRepeatedPoints : Rule where
  number := 1254
  keyword := .mustNot
  domain := .softwareEngineering
  formula := never (ev reviewDraftEdit ∧ₗ atom raisesAnsweredPoint)

def proposesFix : Atom := ⟨"proposesFix",
  "Does this review draft propose a fix?", .edit⟩
def scrutinizesFix : Link := ⟨"scrutinizesFix",
  "Does this step scrutinize the fix the anchored review proposes for what it leaves uncovered?"⟩

/-- Rule 1255: a proposed fix scrutinized first. -/
def fixScrutinized : Rule where
  number := 1255
  keyword := .must
  domain := .softwareEngineering
  formula := ev reviewDraftEdit ∧ₗ atom proposesFix ⟹
    once ((ev reply ∨ₗ ev thinkingStep) ∧ₗ link scrutinizesFix)

def postsCommentAskingUse : Atom := ⟨"postsCommentAskingUse",
  "Does this call post a review comment asking the author to use something not yet built?", .publish⟩
def opensAskedForBuild : Link := ⟨"opensAskedForBuild",
  "Does this call open the merge request of what the anchored comment asks the author to use?"⟩

/-- Rule 1256: what a comment asks the author to use is built and its MR opened before posting. -/
def buildBeforeAsking : Rule where
  number := 1256
  keyword := .must
  domain := .softwareEngineering
  formula := ev publish ∧ₗ atom postsCommentAskingUse ⟹ once (ev mrCreate ∧ₗ link opensAskedForBuild)

def ownFollowUpInComments : Atom := ⟨"ownFollowUpInComments",
  "Does this review draft put our own follow-up among the comments rather than in its \"Ours\" section?", .edit⟩

/-- Rule 1257: our own follow-ups in "Ours". -/
def ownFollowUpsApart : Rule where
  number := 1257
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev reviewDraftEdit ∧ₗ atom ownFollowUpInComments)

def asksCheckableQuestion : Atom := ⟨"asksCheckableQuestion",
  "Does this review draft ask the author something the reviewer could check?", .edit⟩
def followUpUnfolded : Atom := ⟨"followUpUnfolded",
  "Does this review draft leave an expected follow-up question out of the comment it follows from?", .edit⟩

/-- Rule 1258: checkable points settled; expected follow-ups folded in. -/
def settleCheckable : Rule where
  number := 1258
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev reviewDraftEdit ∧ₗ (atom asksCheckableQuestion ∨ₗ atom followUpUnfolded))

def offersReviewComments : Atom := ⟨"offersReviewComments",
  "Does this reply offer the user a review's comments?", .reply⟩
def comparesComments : Link := ⟨"comparesComments",
  "Does this step read the comments the anchored reply offers against each other?"⟩

/-- Rule 1259: the comments read against each other before they are offered. -/
def commentsCrossRead : Rule where
  number := 1259
  keyword := .must
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom offersReviewComments ⟹
    once ((ev reading ∨ₗ ev thinkingStep) ∧ₗ link comparesComments)

def holdsFindingForLater : Atom := ⟨"holdsFindingForLater",
  "Does this reply keep a review finding back for a later round?", .reply⟩

/-- Rule 1260: every finding in one draft. -/
def allFindingsAtOnce : Rule where
  number := 1260
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev reply ∧ₗ atom holdsFindingForLater)

def rules : List Rule :=
  [explicitQuantifiersInApiReview, protocolIndexedByState, schemaAuthoritative, renameKeepsProtocol,
   rejectionInDomainTerms, evidenceTypesFit, boolApartFromProp, noncomputableApart,
   erasureKeepsCosts, observationsDefined, equivalenceExplicit, distinguishingContextAnswered,
   lawsHaveModel, primitiveMeaning, derivationsCompared, algebraKeepsStructure, neutralValueMeaning,
   effectsAtBoundary, conveniencesFromPrimitives, representationInterpreted,
   domainDifferencesTracked, totalInterpreter, equalitiesExplicit, preservationByInduction,
   propertiesFromCallers, severalRelations, statefulSpecified, plainOracle, propertiesLabelled,
   inputsByConstruction, publicConstructorsInTests, shrinkingKeepsDomain, revealingInstances,
   smallDomainsWhole, generatorsHitCoincidences, wholeResultFastProperties, examplesOnlyWhereNeeded,
   handRolledPropertySeed, manyCasesSeedPrinted, wiringByIntegrationCases, uncertaintyGetsMutants,
   genericMutantsJustified, stopWhenSettled, userRequirementsFirst, oneMutantPerBehavior,
   preciseMutants, mutantTestSelection, longBatchInBackground, noPoolsInMutatedTests,
   noStaleVerdicts, skippedScopesIncomplete, survivorsRead, strengthenBeforeAdding,
   redundantTestRemoval, mutationReportComplete, readBeforeSignatureChange, inspectAndDiagnose,
   suggestionsFromCodeActions, searchBeforeProving, tacticsFromGoal, helperLemmas,
   completionByProjectCheck, profileMeasuredSlowness, refactorForGain, leanServerOrLimits,
   singleCommitNoLetter, letterOpensWithContext, letterTenses, generalCondition,
   noCommitListCommentary, shortCommitSummaries, sectionsOnlyWhenLarge, refsAtEnd,
   versionNoteWithRework, letterWithNote, versionNoteShape, noNoteForRebase, mrsInDependencyOrder,
   signInCheckedBeforePush, stackedMrs, oneMrAtATime, dependentLinksEarlier, orderConstraintsStated,
   mrUrlRecorded, movesMappedFirst, statesFromOriginals, removeDraggedAlong, cutSpecsNotInteractive,
   todoThroughTools, fixupPlacement, pureEditsAsFixups, leftoverAuthorship, leftoverMessageExact,
   draftAfterLedger, englishSourceKept, messageChangeOrder, informalChat, pointFirst,
   requestSaysWhy, onlyNeededExplanation, greetingByAudience, paperBasisFirst, standaloneManuscript,
   contributionEarly, proofOverview, spaceByDifficulty, resultsWithHypotheses, argumentsInLemmas,
   noObviousClaims, questionBeforeDefinition, tighteningKeepsReasoning, runningExample,
   illustrationsInPlace, figuresDistinguish, frontMatterLast, reviewErrorsResolved,
   copyeditAfterChanges, noPedagogyNarration, requestedArtifactOnly, pdfInspected,
   repositoryWorkflow, reusePassedChecks, reportWorkDone, keepTypesetting, classicReviewFirst,
   askWhatRestarts, lookBeyondDiff, everyOccurrenceRead, compareWithInstances, messagesAgainstCode,
   enumeratedReviewerAsked, leanReviewerBrief, nonBlockingPointsChecked, noRepeatedPoints,
   fixScrutinized, buildBeforeAsking, ownFollowUpsApart, settleCheckable, commentsCrossRead,
   allFindingsAtOnce]

/-- Range 9 holds no MAY rule. -/
def permissions : List Nat := []

/-- The range's rules are 1121 to 1260, in order, each once. -/
theorem rules_numbers : rules.map (·.number) = List.range' 1121 140 := by decide

end Rails.Ruleset.Range9
