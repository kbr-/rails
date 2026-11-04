import SpecTools.Audit
import SpecTools.GapsRun
import Rails.Rules
import Rails.Examples

/-!
The sample's 20 rules through lean-specification-tools' ledger: one row per rule, its clause the
rule's prose. A formula rule's row claims the formula written out (`rN_formula`, by `rfl`, so a copy
drifting from `Rails.Rules` fails to compile) and its verdict examples in `Rails.Examples`; a MAY
rule's row claims its theorem there. `Rails.LedgerCoverage` proves every rule has a row.

`lake env lean RailsLedger.lean` prints the audit; with `SPEC_TOOLS_GAPS=MODEL` set it asks that
model for the gaps between the clauses and the statements.
-/

namespace Rails.Ledger
open Rails Rules Ruleset Formula SpecTools.Ledger

theorem r1_formula : pushNeedsAuthorization.formula = (ev publish ⟹
    (since (ev user ∧ₗ atom authorizesPush) (ev publish) ∨ₗ atom grantCoversPush)) := rfl
theorem r23_formula : runningStateNeedsAsk.formula = (atom changesRunningState ∧ₗ ¬ₗ ev requestAdd ⟹
    since (ev user ∧ₗ atom asksForThisChange) (ev user)) := rfl
theorem r38_formula : noAttribution.formula = never (ev attributedCommit) := rfl
theorem r56_formula : exploreBeforeEditing.formula = (ev editing ⟹
    ¬ₗ since (ev user ∧ₗ atom exploratoryRequest) (ev user ∧ₗ atom confirmsPlan)) := rfl
theorem r71_formula : noStoppingPrompt.formula = never (ev promptsUser ∧ₗ atom taskInProgress) :=
  rfl
theorem r97_formula : noInventedProgress.formula = never (ev reply ∧ₗ atom inventsProgress) := rfl
theorem r838_formula : readAfterWrite.formula = never (sameMessage readsWrittenFile) := rfl
theorem r7_formula : blockedStepBecomesRequest.formula =
    (atom needsUserAction ⟹ eventually (ev requestAdd)) := rfl
theorem r53_formula : questionIsNoGoAhead.formula = (atom changesRunningState ∧ₗ ¬ₗ ev requestAdd ⟹
    ¬ₗ since (ev user ∧ₗ atom onlyAsks) (ev user)) := rfl
theorem r110_formula : passNeedsRun.formula = (ev reply ∧ₗ atom claimsCheckPasses ⟹
    once (ev passingResult ∧ₗ link runOfClaimedCheck)) := rfl
theorem r170_formula : checkAfterDeploy.formula =
    (ev push ∧ₗ atom pushDeploys ⟹ eventually (atom checksRunningSystem)) := rfl
theorem r341_formula : readClaimFirst.formula = (ev reply ∧ₗ atom reliesOnClaim ⟹
    once (ev reading ∧ₗ link readsReliedClaim)) := rfl
theorem r383_formula : invariantBeforeFix.formula = (ev editing ∧ₗ atom isFix ⟹
    once (ev reply ∧ₗ link statesFixedInvariant)) := rfl
theorem r420_formula : exactFiniteField.formula =
    never (ev editing ∧ₗ atom floatingPointOverFiniteField) := rfl
theorem r605_formula : oneReviewerPerRound.formula = (ev reviewerRun ⟹
    ¬ₗ once (ev reviewerRun ∧ₗ link sameRound) ∨ₗ atom justified) := rfl
theorem r844_formula : algebraSystemFirst.formula = (ev editing ∧ₗ atom writesKernel ⟹
    once (ev reply ∧ₗ link weighsAlgebraSystems) ∨ₗ atom justified) := rfl
theorem r677_formula : noLongWait.formula = (ev reply ∧ₗ atom asksUserAndStops ⟹
    (gapAtMost 120000 ∨ₗ atom nothingUnblocked) ∨ₗ atom justified) := rfl
theorem r926_formula : generalOverCases.formula = (ev reply ∧ₗ atom addsCaseToList ⟹
    atom generalClaimStated ∨ₗ atom justified) := rfl

/-- Each formula rule of `Rules.all`, in its order, with the statements its row claims. -/
def formulaRows : List (Rule × List Lean.Name) := [
  (pushNeedsAuthorization, [``r1_formula, ``Examples.r1_kept, ``Examples.r1_broken,
    ``Examples.r1_unanswered, ``Examples.r1_granted, ``Examples.r1_codex_broken,
    ``Examples.r1_codex_kept, ``Examples.r1_publish_broken, ``Examples.r1_publish_kept,
    ``Examples.publish_forms, ``Examples.reading_forms_no_publish]),
  (runningStateNeedsAsk, [``r23_formula, ``Examples.r23_kept, ``Examples.r23_broken]),
  (noAttribution, [``r38_formula, ``Examples.r38_kept, ``Examples.r38_broken]),
  (exploreBeforeEditing, [``r56_formula, ``Examples.r56_kept, ``Examples.r56_broken]),
  (noStoppingPrompt, [``r71_formula, ``Examples.r71_kept, ``Examples.r71_broken]),
  (noInventedProgress, [``r97_formula, ``Examples.r97_kept, ``Examples.r97_broken,
    ``Examples.r97_unanswered]),
  (readAfterWrite, [``r838_formula, ``Examples.r838_kept, ``Examples.r838_broken]),
  (blockedStepBecomesRequest, [``r7_formula, ``Examples.r7_kept, ``Examples.r7_broken,
    ``Examples.r7_undecided]),
  (questionIsNoGoAhead, [``r53_formula, ``Examples.r53_kept, ``Examples.r53_broken]),
  (passNeedsRun, [``r110_formula, ``Examples.r110_kept, ``Examples.r110_broken]),
  (checkAfterDeploy, [``r170_formula, ``Examples.r170_kept, ``Examples.r170_broken]),
  (readClaimFirst, [``r341_formula, ``Examples.r341_kept, ``Examples.r341_broken]),
  (invariantBeforeFix, [``r383_formula, ``Examples.r383_kept, ``Examples.r383_broken]),
  (exactFiniteField, [``r420_formula, ``Examples.r420_kept, ``Examples.r420_broken]),
  (oneReviewerPerRound, [``r605_formula, ``Examples.r605_kept, ``Examples.r605_broken]),
  (algebraSystemFirst, [``r844_formula, ``Examples.r844_kept, ``Examples.r844_broken]),
  (noLongWait, [``r677_formula, ``Examples.r677_kept, ``Examples.r677_broken]),
  (generalOverCases, [``r926_formula, ``Examples.r926_kept, ``Examples.r926_broken])]

/-- The MAY rules, numbered as in `tasks/agents-on-rails/RULES.md`, with their theorems; their
clauses come from the generated table. -/
def mayRows : List (Nat × List Lean.Name) := [
  (9, [``Examples.r9_request_always_allowed]),
  (1293, [``Examples.r1293_plain_push])]

/-- A rule's text in the generated table. -/
def textOf (n : Nat) : String := ((RuleText.entries.find? (·.number == n)).map (·.text)).getD ""

def ledger : List Row :=
  formulaRows.map (fun (r, ts) => { id := s!"r{r.number}", clause := r.text, theorems := ts }) ++
    mayRows.map fun (n, ts) => { id := s!"r{n}", clause := textOf n, theorems := ts }

/-- The prose `gaps` reads: the rows' clauses, one to a line. -/
def prose : String := "\n".intercalate (ledger.map (·.clause))

end Rails.Ledger
