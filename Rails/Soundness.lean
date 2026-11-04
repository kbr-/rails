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
    simp only [eval, Holds, Ctx.atomAnswer]
    cases hd : ctx.decided a i with
    | some b => simp
    | none =>
      cases ha : ctx.answer (.atom a.name i) with
      | none => simp
      | some b =>
        have := agrees _ _ ha
        simp [this]
  | link l =>
    intro anchor i
    simp only [eval, Holds]
    cases ha : ctx.answer (.link l.name anchor i) with
    | none => simp
    | some b =>
      have := agrees _ _ ha
      simp [this]
  | sameMessage r =>
    intro anchor i
    simp only [eval, Holds, anyT_kept, anyT_broken]
    constructor
    · rintro ⟨j, hj, hk⟩
      refine ⟨j, hj, ?_⟩
      cases hs : ctx.step? i <;> cases ht : ctx.step? j <;> simp_all
    · intro hb ⟨j, hj, s, t, hs, ht, hr⟩
      have := hb j hj
      simp_all
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
    have mem : ∀ j, j ∈ List.range' (i + 1) (ctx.size - (i + 1)) ↔ j < ctx.size ∧ i < j := by
      intro j; simp only [List.mem_range'_1]; omega
    simp only [eval, Holds]
    generalize hF : (anyT (List.range' (i + 1) (ctx.size - (i + 1))) fun j => eval ctx i j φ) = F
    have hk : F = kept → ∃ j, j < ctx.size ∧ i < j ∧ Holds ctx val i j φ := by
      intro h
      rw [← hF, anyT_kept] at h
      obtain ⟨j, hj, hk⟩ := h
      exact ⟨j, ((mem j).mp hj).1, ((mem j).mp hj).2, (ih i j).1 hk⟩
    have hb : F = broken → ¬ ∃ j, j < ctx.size ∧ i < j ∧ Holds ctx val i j φ := by
      intro h ⟨x, hx, hix, hh⟩
      rw [← hF, anyT_broken] at h
      exact (ih i x).2 (h x ((mem x).mpr ⟨hx, hix⟩)) hh
    by_cases hc : ctx.complete = true
    · simp only [hc, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false]
      exact ⟨hk, hb⟩
    · by_cases hfb : F = broken
      · subst hfb
        simp [hc]
      · have : (F == broken) = false := by cases F <;> simp_all
        simp only [this, Bool.false_and, Bool.false_eq_true, ite_false]
        exact ⟨hk, hb⟩
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
  | before φ χ ihφ ihχ =>
    intro anchor i
    have mem : ∀ j, j ∈ List.range' (i + 1) (ctx.size - (i + 1)) ↔ j < ctx.size ∧ i < j := by
      intro j; simp only [List.mem_range'_1]; omega
    simp only [eval, Holds]
    generalize hF : (anyT (List.range' (i + 1) (ctx.size - (i + 1))) fun j =>
      (eval ctx i j φ).and (allT ((List.range' (i + 1) (ctx.size - (i + 1))).filter (· < j))
        fun k => (eval ctx i k χ).not)) = F
    have hk : F = kept → ∃ j, j < ctx.size ∧ i < j ∧ Holds ctx val i j φ ∧
        ∀ k, i < k → k < j → ¬ Holds ctx val i k χ := by
      intro h
      rw [← hF, anyT_kept] at h
      obtain ⟨j, hj, hk⟩ := h
      simp only [Tri.and_kept, allT_kept, List.mem_filter, decide_eq_true_eq, Tri.not_kept] at hk
      refine ⟨j, ((mem j).mp hj).1, ((mem j).mp hj).2, (ihφ i j).1 hk.1, ?_⟩
      intro k hik hkj
      have hkm : k ∈ List.range' (i + 1) (ctx.size - (i + 1)) :=
        (mem k).mpr ⟨by have := ((mem j).mp hj).1; omega, hik⟩
      exact (ihχ i k).2 (hk.2 k ⟨hkm, hkj⟩)
    have hb : F = broken → ¬ ∃ j, j < ctx.size ∧ i < j ∧ Holds ctx val i j φ ∧
        ∀ k, i < k → k < j → ¬ Holds ctx val i k χ := by
      intro h ⟨x, hx, hix, hφ, hnone⟩
      rw [← hF, anyT_broken] at h
      have hxb := h x ((mem x).mpr ⟨hx, hix⟩)
      simp only [Tri.and_broken, allT_broken, List.mem_filter, decide_eq_true_eq,
        Tri.not_broken] at hxb
      rcases hxb with hb1 | ⟨k, ⟨hkm, hkx⟩, hχ⟩
      · exact (ihφ i x).2 hb1 hφ
      · exact hnone k ((mem k).mp hkm).2 hkx ((ihχ i k).1 hχ)
    by_cases hc : ctx.complete = true
    · simp only [hc, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false]
      exact ⟨hk, hb⟩
    · by_cases hfb : F = broken
      · subst hfb
        simp [hc]
      · have : (F == broken) = false := by cases F <;> simp_all
        simp only [this, Bool.false_and, Bool.false_eq_true, ite_false]
        exact ⟨hk, hb⟩
  | within ms φ ih =>
    intro anchor i
    have mem : ∀ j, j ∈ List.range' (i + 1) (ctx.size - (i + 1)) ↔ j < ctx.size ∧ i < j := by
      intro j; simp only [List.mem_range'_1]; omega
    simp only [eval, Holds]
    generalize hF : (anyT (List.range' (i + 1) (ctx.size - (i + 1))) fun j =>
      match ctx.step? i, ctx.step? j with
      | some s, some t => (eval ctx i j φ).and (ofBool (decide (t.time ≤ s.time + ms)))
      | _, _ => broken) = F
    have hk : F = kept → ∃ j, j < ctx.size ∧ i < j ∧ Holds ctx val i j φ ∧
        ∃ s t, ctx.step? i = some s ∧ ctx.step? j = some t ∧ t.time ≤ s.time + ms := by
      intro h
      rw [← hF, anyT_kept] at h
      obtain ⟨j, hj, hk⟩ := h
      cases hs : ctx.step? i <;> cases ht : ctx.step? j <;> simp only [hs, ht] at hk
      · simp at hk
      · simp at hk
      · simp at hk
      · simp only [Tri.and_kept, Tri.ofBool_kept, decide_eq_true_eq] at hk
        exact ⟨j, ((mem j).mp hj).1, ((mem j).mp hj).2, (ih i j).1 hk.1, _, _, rfl, ht, hk.2⟩
    have hb : F = broken → ¬ ∃ j, j < ctx.size ∧ i < j ∧ Holds ctx val i j φ ∧
        ∃ s t, ctx.step? i = some s ∧ ctx.step? j = some t ∧ t.time ≤ s.time + ms := by
      intro h ⟨x, hx, hix, hφ, s, t, hs, ht, htime⟩
      rw [← hF, anyT_broken] at h
      have hxb := h x ((mem x).mpr ⟨hx, hix⟩)
      simp only [hs, ht, Tri.and_broken, Tri.ofBool_broken, decide_eq_false_iff_not] at hxb
      rcases hxb with hb1 | hb2
      · exact (ih i x).2 hb1 hφ
      · exact hb2 htime
    by_cases hc : ctx.complete = true
    · simp only [hc, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false]
      exact ⟨hk, hb⟩
    · by_cases hfb : F = broken
      · subst hfb
        simp [hc]
      · have : (F == broken) = false := by cases F <;> simp_all
        simp only [this, Bool.false_and, Bool.false_eq_true, ite_false]
        exact ⟨hk, hb⟩

/-- A rule's verdict over a whole trace is sound in the same sense. -/
theorem evalAlways_sound (ctx : Ctx) (val : Query → Bool) (agrees : Agrees ctx val) (φ : Formula) :
    (evalAlways ctx φ = .kept → ∀ i, i < ctx.size → Holds ctx val i i φ) ∧
    (evalAlways ctx φ = .broken → ∃ i, i < ctx.size ∧ ¬ Holds ctx val i i φ) := by
  simp only [evalAlways, allT_kept, allT_broken, List.mem_range]
  exact ⟨fun h i hi => (eval_sound ctx val agrees φ i i).1 (h i hi),
    fun ⟨i, hi, hb⟩ => ⟨i, hi, (eval_sound ctx val agrees φ i i).2 hb⟩⟩

end Rails
