import Rails.Atoms
import Rails.Examples

/-!
The model's answers' guarantees: a decider's answer is never replaced, a model's answer fills an
open query, nothing answered is asked, every outcome is counted, and an answer turns an undecided
verdict into a decided one while a failure leaves it undecided.
-/

namespace Rails.Atoms
open Rails Rails.Check Rails.Examples SpecTools.Model

theorem withAnswers_keeps (ctx : Ctx) (ans : List (Query × Bool)) {q : Query} {b : Bool}
    (h : ctx.answer q = some b) : (withAnswers ctx ans).answer q = some b := by
  simp [withAnswers, h]

theorem withAnswers_fills (ctx : Ctx) (ans : List (Query × Bool)) {q : Query} {b : Bool}
    (h : ctx.answer q = none) (hb : ans.lookup q = some b) : (withAnswers ctx ans).answer q = some b := by
  simp [withAnswers, h, hb]

/-- Only atoms that neither their decider nor the context answers are asked. -/
theorem openQueries_open (ctx : Ctx) (φ : Formula) {a : Atom} {i : Nat}
    (h : (a, i) ∈ openQueries ctx φ) : ctx.atomAnswer a i = none := by
  simp only [openQueries, List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨j, _, b, _, hq⟩ := h
  split at hq
  · rename_i hn
    cases hq
    simpa using hn
  · cases hq

def Collected.total (c : Collected) : Nat :=
  c.answers.length + c.refused + c.timedOut + c.exited + c.malformed

/-- Every outcome is counted, as an answer or as one kind of failure. -/
theorem collect_total (l : List (Query × Except Failure Outcome)) : (collect l).total = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨q, r⟩ := x
    simp only [Collected.total] at ih ⊢
    cases r with
    | ok o =>
      simp only [collect]
      split <;> simp <;> omega
    | error f => cases f <;> simp [collect] <;> omega

theorem collect_answer (q : Query) (o : Outcome) (b : Bool) (h : answerOf o.answer = some b) :
    (collect [(q, .ok o)]).answers = [(q, b)] := by
  simp [collect, h]

theorem collect_failure (q : Query) (f : Failure) : (collect [(q, .error f)]).answers = [] := by
  cases f <;> rfl

/-! On rule 97's trace, its atom left to a model: undecided, then decided by either answer. -/

def ctx97 : Ctx := Ctx.build (seq [.reply "proved"]) true fun _ => none

example : check Rules.noInventedProgress ctx97 = .undecided := by rw [check_eq]; decide
example : check Rules.noInventedProgress
    (withAnswers ctx97 [(.atom "inventsProgress" 0, false)]) = .kept := by rw [check_eq]; decide
example : check Rules.noInventedProgress
    (withAnswers ctx97 [(.atom "inventsProgress" 0, true)]) = .broken := by rw [check_eq]; decide
/-- A failed question gives no answer, so the verdict stays undecided. -/
example : check Rules.noInventedProgress
    (withAnswers ctx97 (collect [(.atom "inventsProgress" 0, .error (.timedOut "m" 10))]).answers) =
    .undecided := by rw [check_eq]; decide
/-- The open queries of rule 97's trace: its one atom at its one position. -/
example : (openQueries ctx97 Rules.noInventedProgress.formula).map (fun (a, i) => (a.name, i)) =
    [("inventsProgress", 0)] := by decide

end Rails.Atoms
