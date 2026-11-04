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
open Rails Rules Formula SpecTools.Ledger

theorem r1_formula : pushNeedsAuthorization.formula = (ev isPublish ⟹
    (since (ev isUser ∧ₗ atom .authorizesPush) (ev isPublish) ∨ₗ atom .grantCoversPush)) := rfl
theorem r23_formula : runningStateNeedsAsk.formula =
    (atom .changesRunningState ⟹ since (ev isUser ∧ₗ atom .asksForThisChange) (ev isUser)) := rfl
theorem r38_formula : noAttribution.formula = never (ev isAttributedCommit) := rfl
theorem r56_formula : exploreBeforeEditing.formula = (ev isEdit ⟹
    ¬ₗ since (ev isUser ∧ₗ atom .exploratoryRequest) (ev isUser ∧ₗ atom .confirmsPlan)) := rfl
theorem r71_formula : noStoppingPrompt.formula =
    never (ev (isTool "AskUserQuestion") ∧ₗ atom .taskInProgress) := rfl
theorem r97_formula : noInventedProgress.formula = never (ev isReply ∧ₗ atom .inventsProgress) :=
  rfl
theorem r838_formula : readAfterWrite.formula = never (sameMessage readsWhatOtherWrites) := rfl
theorem r7_formula : blockedStepBecomesRequest.formula =
    (atom .needsUserAction ⟹ eventually (ev isRequestAdd)) := rfl
theorem r53_formula : questionIsNoGoAhead.formula =
    (atom .changesRunningState ⟹ ¬ₗ since (ev isUser ∧ₗ atom .onlyAsks) (ev isUser)) := rfl
theorem r110_formula : passNeedsRun.formula = (ev isReply ∧ₗ atom .claimsCheckPasses ⟹
    once (ev isPassingResult ∧ₗ link .runOfClaimedCheck)) := rfl
theorem r170_formula : checkAfterDeploy.formula =
    (ev isPush ∧ₗ atom .pushDeploys ⟹ eventually (atom .checksRunningSystem)) := rfl
theorem r341_formula : readClaimFirst.formula = (ev isReply ∧ₗ atom .reliesOnClaim ⟹
    once (ev isRead ∧ₗ link .readsReliedClaim)) := rfl
theorem r383_formula : invariantBeforeFix.formula = (ev isEdit ∧ₗ atom .isFix ⟹
    once (ev isReply ∧ₗ link .statesFixedInvariant)) := rfl
theorem r420_formula : exactFiniteField.formula =
    never (ev isEdit ∧ₗ atom .floatingPointOverFiniteField) := rfl
theorem r605_formula : oneReviewerPerRound.formula = (ev isReviewerRun ⟹
    ¬ₗ once (ev isReviewerRun ∧ₗ link .sameRound) ∨ₗ atom .justified) := rfl
theorem r844_formula : algebraSystemFirst.formula = (ev isEdit ∧ₗ atom .writesKernel ⟹
    once (ev isReply ∧ₗ link .weighsAlgebraSystems) ∨ₗ atom .justified) := rfl
theorem r677_formula : noLongWait.formula = (ev isReply ∧ₗ atom .asksUserAndStops ⟹
    (gapAtMost 120000 ∨ₗ atom .nothingUnblocked) ∨ₗ atom .justified) := rfl
theorem r926_formula : generalOverCases.formula = (ev isReply ∧ₗ atom .addsCaseToList ⟹
    atom .generalClaimStated ∨ₗ atom .justified) := rfl

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

/-- The MAY rules, numbered and quoted from `tasks/agents-on-rails/RULES.md`, with their theorems. -/
def mayRows : List (Nat × String × List Lean.Name) := [
  (9, "You MAY add or resolve a request at any time and commit it freely.",
    [``Examples.r9_request_always_allowed]),
  (1293, "You MAY, after a plain branch push, only confirm the remote branch.",
    [``Examples.r1293_plain_push])]

def ledger : List Row :=
  formulaRows.map (fun (r, ts) => { id := s!"r{r.number}", clause := r.text, theorems := ts }) ++
    mayRows.map fun (n, c, ts) => { id := s!"r{n}", clause := c, theorems := ts }

/-- The prose `gaps` reads: the rows' clauses, one to a line. -/
def prose : String := "\n".intercalate (ledger.map (·.clause))

end Rails.Ledger
