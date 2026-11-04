import Rails.Logic

/-!
The evaluator is sound: a kept verdict means the formula holds, a broken one that it fails, under
every reading of the questions that agrees with the answers given. An undecided verdict claims
nothing.
-/

namespace Rails
open Tri Formula

namespace Tri
@[simp] theorem not_kept (t : Tri) : t.not = kept ↔ t = broken := by cases t <;> decide
@[simp] theorem not_broken (t : Tri) : t.not = broken ↔ t = kept := by cases t <;> decide
@[simp] theorem and_kept (a b : Tri) : a.and b = kept ↔ a = kept ∧ b = kept := by
  cases a <;> cases b <;> decide
@[simp] theorem and_broken (a b : Tri) : a.and b = broken ↔ a = broken ∨ b = broken := by
  cases a <;> cases b <;> decide
@[simp] theorem or_kept (a b : Tri) : a.or b = kept ↔ a = kept ∨ b = kept := by
  cases a <;> cases b <;> decide
@[simp] theorem or_broken (a b : Tri) : a.or b = broken ↔ a = broken ∧ b = broken := by
  cases a <;> cases b <;> decide
@[simp] theorem ofBool_kept (b : Bool) : ofBool b = kept ↔ b = true := by cases b <;> decide
@[simp] theorem ofBool_broken (b : Bool) : ofBool b = broken ↔ b = false := by cases b <;> decide
end Tri

@[simp] theorem anyT_kept {α} (l : List α) (g : α → Tri) :
    anyT l g = kept ↔ ∃ x ∈ l, g x = kept := by
  induction l with
  | nil => simp [anyT]
  | cons x xs ih => simp only [anyT, List.foldr_cons] at *; simp [ih]

@[simp] theorem anyT_broken {α} (l : List α) (g : α → Tri) :
    anyT l g = broken ↔ ∀ x ∈ l, g x = broken := by
  induction l with
  | nil => simp [anyT]
  | cons x xs ih => simp only [anyT, List.foldr_cons] at *; simp [ih]

@[simp] theorem allT_kept {α} (l : List α) (g : α → Tri) :
    allT l g = kept ↔ ∀ x ∈ l, g x = kept := by
  induction l with
  | nil => simp [allT]
  | cons x xs ih => simp only [allT, List.foldr_cons] at *; simp [ih]

@[simp] theorem allT_broken {α} (l : List α) (g : α → Tri) :
    allT l g = broken ↔ ∃ x ∈ l, g x = broken := by
  induction l with
  | nil => simp [allT]
  | cons x xs ih => simp only [allT, List.foldr_cons] at *; simp [ih]

theorem eval_sound (ctx : Ctx) (val : Query → Bool) (agrees : Agrees ctx val) :
    ∀ (φ : Formula) (anchor i : Nat),
      (eval ctx anchor i φ = .kept → Holds ctx val anchor i φ) ∧
      (eval ctx anchor i φ = .broken → ¬ Holds ctx val anchor i φ) := by
  intro φ
  induction φ with
  | ev p =>
    intro anchor i
    simp only [eval, Holds]
    cases hs : ctx.step? i with
    | none => simp
    | some s => simp
  | atom a =>
    intro anchor i
    simp only [eval, Holds]
    cases ha : ctx.answer (.atom a i) with
    | none => simp
    | some b =>
      have := agrees _ _ ha
      simp [this]
  | link l =>
    intro anchor i
    simp only [eval, Holds]
    cases ha : ctx.answer (.link l anchor i) with
    | none => simp
    | some b =>
      have := agrees _ _ ha
      simp [this]
  | sameMessage r =>
    intro anchor i
    simp only [eval, Holds, anyT_kept, anyT_broken, List.mem_range]
    constructor
    · rintro ⟨j, hj, hk⟩
      refine ⟨j, hj, ?_⟩
      cases hs : ctx.step? i <;> cases ht : ctx.step? j <;> simp_all
    · intro hb ⟨j, hj, s, t, hs, ht, hr⟩
      have := hb j hj
      simp_all
  | gapAtMost ms =>
    intro anchor i
    simp only [eval, Holds]
    cases hs : ctx.step? i <;> cases ht : ctx.step? (i + 1) <;> simp
  | not φ ih =>
    intro anchor i
    have := ih anchor i
    simp only [eval, Holds, Tri.not_kept, Tri.not_broken]
    exact ⟨fun h hφ => this.2 h hφ, fun h hn => hn (this.1 h)⟩
  | and φ ψ ihφ ihψ =>
    intro anchor i
    have a := ihφ anchor i
    have b := ihψ anchor i
    simp only [eval, Holds, Tri.and_kept, Tri.and_broken]
    exact ⟨fun ⟨h1, h2⟩ => ⟨a.1 h1, b.1 h2⟩,
      fun h ⟨h1, h2⟩ => h.elim (fun x => a.2 x h1) (fun x => b.2 x h2)⟩
  | or φ ψ ihφ ihψ =>
    intro anchor i
    have a := ihφ anchor i
    have b := ihψ anchor i
    simp only [eval, Holds, Tri.or_kept, Tri.or_broken]
    exact ⟨fun h => h.elim (fun x => .inl (a.1 x)) (fun x => .inr (b.1 x)),
      fun ⟨h1, h2⟩ h => h.elim (a.2 h1) (b.2 h2)⟩
  | once φ ih =>
    intro anchor i
    simp only [eval, Holds, anyT_kept, anyT_broken, List.mem_range]
    exact ⟨fun ⟨j, hj, hk⟩ => ⟨j, hj, (ih i j).1 hk⟩,
      fun hb ⟨j, hj, hh⟩ => (ih i j).2 (hb j hj) hh⟩
  | eventually φ ih =>
    intro anchor i
    simp only [eval, Holds]
    by_cases hf : (anyT ((List.range ctx.size).filter (i < ·)) fun j => eval ctx i j φ) = broken
    · by_cases hc : ctx.complete = true
      · simp only [hf, hc, beq_self_eq_true, Bool.not_true, Bool.and_false, Bool.false_eq_true,
          ite_false]
        simp only [anyT_broken, List.mem_filter, List.mem_range, decide_eq_true_eq] at hf
        exact ⟨fun h => absurd h (by decide), fun _ ⟨j, hj, hij, hh⟩ => (ih i j).2 (hf j ⟨hj, hij⟩) hh⟩
      · simp [hf, hc]
    · have : ((anyT ((List.range ctx.size).filter (i < ·)) fun j => eval ctx i j φ) == broken) =
          false := by
        simpa using hf
      simp only [this, Bool.false_and, Bool.false_eq_true, ite_false, anyT_kept, anyT_broken,
        List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨fun ⟨j, ⟨hj, hij⟩, hk⟩ => ⟨j, hj, hij, (ih i j).1 hk⟩,
        fun hb ⟨j, hj, hij, hh⟩ => (ih i j).2 (hb j ⟨hj, hij⟩) hh⟩
  | since φ χ ihφ ihχ =>
    intro anchor i
    simp only [eval, Holds, anyT_kept, anyT_broken, List.mem_range, Tri.and_kept, Tri.and_broken,
      allT_kept, allT_broken, List.mem_filter, decide_eq_true_eq, Tri.not_kept, Tri.not_broken]
    constructor
    · rintro ⟨j, hj, hφ, hall⟩
      exact ⟨j, hj, (ihφ i j).1 hφ, fun k hk hjk => (ihχ i k).2 (hall k ⟨hk, hjk⟩)⟩
    · intro hb ⟨j, hj, hφ, hnone⟩
      rcases hb j hj with h | ⟨k, ⟨hk, hjk⟩, hχ⟩
      · exact (ihφ i j).2 h hφ
      · exact hnone k hk hjk ((ihχ i k).1 hχ)

/-- A rule's verdict over a whole trace is sound in the same sense. -/
theorem evalAlways_sound (ctx : Ctx) (val : Query → Bool) (agrees : Agrees ctx val) (φ : Formula) :
    (evalAlways ctx φ = .kept → ∀ i, i < ctx.size → Holds ctx val i i φ) ∧
    (evalAlways ctx φ = .broken → ∃ i, i < ctx.size ∧ ¬ Holds ctx val i i φ) := by
  simp only [evalAlways, allT_kept, allT_broken, List.mem_range]
  exact ⟨fun h i hi => (eval_sound ctx val agrees φ i i).1 (h i hi),
    fun ⟨i, hi, hb⟩ => ⟨i, hi, (eval_sound ctx val agrees φ i i).2 hb⟩⟩

end Rails
