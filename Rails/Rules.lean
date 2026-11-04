import Rails.Ruleset.Atoms
import Rails.RuleText

/-!
Twenty rules of `tasks/agents-on-rails/RULES.md`, sampled across its keywords and domains, written
first as if the decision model existed; `Rails.Trace` and `Rails.Logic` were then shaped to what
they needed.

Each rule is a formula that must hold at every position of a trace (`Rule.verdict`). A MUST NOT rule
is `never bad`; a MUST rule `always (trigger ⟹ obligation)`; a SHOULD rule allows its exception
through the atom `justified`; a MAY rule is no formula but a theorem that the rules don't forbid
what it permits (in `Rails.Examples`). The semantic atoms (`Atom`) are answered by a mechanical
decider where one exists (`Atom.decide`) and by a model otherwise.
-/

namespace Rails.Rules
open Rails Formula Ruleset

inductive Keyword where
  | must | mustNot | should | shouldNot | may
  deriving Repr, DecidableEq

inductive Domain where
  | softwareEngineering | mathematics | discipline | tasks
  deriving Repr, DecidableEq

structure Rule where
  /-- The rule's number in `tasks/agents-on-rails/RULES.md`. -/
  number : Nat
  keyword : Keyword
  domain : Domain
  formula : Formula

/-- The rule's text as RULES.md states it, from the generated table. -/
def Rule.text (r : Rule) : String :=
  ((RuleText.entries.find? (·.number == r.number)).map (·.text)).getD ""

/-- Rule 1: no push, publish or deploy on the agent's own initiative (`isPublish`); each needs the
user's authorization given since the previous one, or a standing grant covering it (AGENTS.md makes
a recorded grant the ask, and a grant held only outside the trace leaves it undecided). -/
def pushNeedsAuthorization : Rule where
  number := 1
  keyword := .mustNot
  domain := .softwareEngineering
  formula := ev publish ⟹
    (since (ev user ∧ₗ atom authorizesPush) (ev publish) ∨ₗ atom grantCoversPush)

/-- Rule 23: no change to running state unless the latest user message asked for it. -/
def runningStateNeedsAsk : Rule where
  number := 23
  keyword := .mustNot
  domain := .discipline
  formula := atom changesRunningState ∧ₗ ¬ₗ ev requestAdd ⟹
    since (ev user ∧ₗ atom asksForThisChange) (ev user)

/-- Rule 38: no Claude attribution in a commit message. -/
def noAttribution : Rule where
  number := 38
  keyword := .mustNot
  domain := .softwareEngineering
  formula := never (ev attributedCommit)

/-- Rule 56: no edit after an exploratory request until a plan is confirmed. -/
def exploreBeforeEditing : Rule where
  number := 56
  keyword := .mustNot
  domain := .discipline
  formula := ev editing ⟹ ¬ₗ since (ev user ∧ₗ atom exploratoryRequest) (ev user ∧ₗ atom confirmsPlan)

/-- Rule 71: no interactive prompt that stops the turn while a task is in progress. -/
def noStoppingPrompt : Rule where
  number := 71
  keyword := .mustNot
  domain := .tasks
  formula := never (ev promptsUser ∧ₗ atom taskInProgress)

/-- Rule 97: no invented progress in a reply. -/
def noInventedProgress : Rule where
  number := 97
  keyword := .mustNot
  domain := .mathematics
  formula := never (ev reply ∧ₗ atom inventsProgress)

/-- Rule 838: no call reading a file another call of the same message writes. -/
def readAfterWrite : Rule where
  number := 838
  keyword := .mustNot
  domain := .softwareEngineering
  formula := never (sameMessage readsWrittenFile)

/-- Rule 7: a step needing the user's action ends in a request. -/
def blockedStepBecomesRequest : Rule where
  number := 7
  keyword := .must
  domain := .tasks
  formula := atom needsUserAction ⟹ eventually (ev requestAdd)

/-- Rule 53: a question asks for information, not action. -/
def questionIsNoGoAhead : Rule where
  number := 53
  keyword := .must
  domain := .discipline
  formula := atom changesRunningState ∧ₗ ¬ₗ ev requestAdd ⟹
    ¬ₗ since (ev user ∧ₗ atom onlyAsks) (ev user)

/-- Rule 110: a claim that a check passes rests on its run. -/
def passNeedsRun : Rule where
  number := 110
  keyword := .must
  domain := .discipline
  formula := ev reply ∧ₗ atom claimsCheckPasses ⟹ once (ev passingResult ∧ₗ link runOfClaimedCheck)

/-- Rule 170: after a push that deploys, check the running system. -/
def checkAfterDeploy : Rule where
  number := 170
  keyword := .must
  domain := .softwareEngineering
  formula := ev push ∧ₗ atom pushDeploys ⟹ eventually (atom checksRunningSystem)

/-- Rule 341: a claim is read before it is relied on. -/
def readClaimFirst : Rule where
  number := 341
  keyword := .must
  domain := .mathematics
  formula := ev reply ∧ₗ atom reliesOnClaim ⟹ once (ev reading ∧ₗ link readsReliedClaim)

/-- Rule 383: a fix is preceded by the invariant it restores. -/
def invariantBeforeFix : Rule where
  number := 383
  keyword := .must
  domain := .discipline
  formula := ev editing ∧ₗ atom isFix ⟹ once (ev reply ∧ₗ link statesFixedInvariant)

/-- Rule 420: exact arithmetic over finite fields. -/
def exactFiniteField : Rule where
  number := 420
  keyword := .must
  domain := .mathematics
  formula := never (ev editing ∧ₗ atom floatingPointOverFiniteField)

/-- Rule 605: one reviewer per round, save the review loop's exceptions. -/
def oneReviewerPerRound : Rule where
  number := 605
  keyword := .should
  domain := .tasks
  formula := ev reviewerRun ⟹ ¬ₗ once (ev reviewerRun ∧ₗ link sameRound) ∨ₗ atom justified

/-- Rule 844: a computer algebra system is considered before a hand-built kernel. -/
def algebraSystemFirst : Rule where
  number := 844
  keyword := .should
  domain := .mathematics
  formula := ev editing ∧ₗ atom writesKernel ⟹ once (ev reply ∧ₗ link weighsAlgebraSystems) ∨ₗ
    atom justified

/-- Rule 677: a question to the user doesn't idle the agent past two minutes. -/
def noLongWait : Rule where
  number := 677
  keyword := .shouldNot
  domain := .tasks
  formula := ev reply ∧ₗ atom asksUserAndStops ⟹
    (within 120000 (ev anyStep) ∨ₗ atom nothingUnblocked) ∨ₗ atom justified

/-- Rule 926: no growing list of cases where a general claim could be stated. -/
def generalOverCases : Rule where
  number := 926
  keyword := .shouldNot
  domain := .mathematics
  formula := ev reply ∧ₗ atom addsCaseToList ⟹ atom generalClaimStated ∨ₗ atom justified

/-- The formulas above; the MAY rules (9 and 1293) are theorems in `Rails.Examples`. -/
def all : List Rule :=
  [pushNeedsAuthorization, runningStateNeedsAsk, noAttribution, exploreBeforeEditing,
   noStoppingPrompt, noInventedProgress, readAfterWrite, blockedStepBecomesRequest,
   questionIsNoGoAhead, passNeedsRun, checkAfterDeploy, readClaimFirst, invariantBeforeFix,
   exactFiniteField, oneReviewerPerRound, algebraSystemFirst, noLongWait, generalOverCases]

/-- The verdict of a rule on a trace: its formula at every position. -/
def Rule.verdict (rule : Rule) (ctx : Ctx) : Tri := evalAlways ctx rule.formula

end Rails.Rules
