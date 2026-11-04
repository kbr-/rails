import Rails.Soundness

/-!
A fast evaluator for rules: `eval` at every position costs quadratic time for `once` and cubic for
`since`. For a formula without links, whose value at a position doesn't depend on the anchor, each
subformula's values at all positions are computed once, `once` and `since` by one scan each; the
result is proved equal to `evalAlways` (`evalAlwaysFast_eq`), so `eval_sound` covers it.
-/

namespace Rails
open Tri Formula

/-- A formula with no link: its value at a position is the same whatever the anchor. -/
def linkFree : Formula → Bool
  | link _ => false
  | .not φ | once φ | eventually φ => linkFree φ
  | .and φ ψ | .or φ ψ | since φ ψ => linkFree φ && linkFree ψ
  | _ => true

namespace Tri
theorem or_assoc (a b c : Tri) : (a.or b).or c = a.or (b.or c) := by
  cases a <;> cases b <;> cases c <;> rfl
theorem or_broken_id (a : Tri) : a.or broken = a := by cases a <;> rfl
theorem broken_or_id (a : Tri) : broken.or a = a := by cases a <;> rfl
theorem and_kept_id (a : Tri) : a.and kept = a := by cases a <;> rfl
theorem kept_and_id (a : Tri) : kept.and a = a := by cases a <;> rfl
theorem and_assoc (a b c : Tri) : (a.and b).and c = a.and (b.and c) := by
  cases a <;> cases b <;> cases c <;> rfl
theorem or_and_distrib (a b c : Tri) : (a.or b).and c = (a.and c).or (b.and c) := by
  cases a <;> cases b <;> cases c <;> rfl
theorem broken_and (c : Tri) : broken.and c = broken := by cases c <;> rfl
end Tri

theorem anyT_snoc {α} (l : List α) (x : α) (g : α → Tri) :
    anyT (l ++ [x]) g = (anyT l g).or (g x) := by
  induction l with
  | nil => show (g x).or broken = broken.or (g x); rw [Tri.or_broken_id, Tri.broken_or_id]
  | cons y ys ih =>
    show (g y).or (anyT (ys ++ [x]) g) = ((g y).or (anyT ys g)).or (g x)
    rw [ih, Tri.or_assoc]

theorem allT_snoc {α} (l : List α) (x : α) (g : α → Tri) :
    allT (l ++ [x]) g = (allT l g).and (g x) := by
  induction l with
  | nil => show (g x).and kept = kept.and (g x); rw [Tri.and_kept_id, Tri.kept_and_id]
  | cons y ys ih =>
    show (g y).and (allT (ys ++ [x]) g) = ((g y).and (allT ys g)).and (g x)
    rw [ih, Tri.and_assoc]

theorem anyT_congr {α} {l : List α} {g h : α → Tri} (e : ∀ x ∈ l, g x = h x) :
    anyT l g = anyT l h := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    show (g y).or (anyT ys g) = (h y).or (anyT ys h)
    rw [e y (by simp), ih fun x hx => e x (by simp [hx])]

theorem allT_congr {α} {l : List α} {g h : α → Tri} (e : ∀ x ∈ l, g x = h x) :
    allT l g = allT l h := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    show (g y).and (allT ys g) = (h y).and (allT ys h)
    rw [e y (by simp), ih fun x hx => e x (by simp [hx])]

theorem anyT_and_right {α} (l : List α) (g : α → Tri) (c : Tri) :
    anyT l (fun x => (g x).and c) = (anyT l g).and c := by
  induction l with
  | nil => show broken = broken.and c; rw [Tri.broken_and]
  | cons y ys ih =>
    show ((g y).and c).or (anyT ys fun x => (g x).and c) = ((g y).or (anyT ys g)).and c
    rw [ih, Tri.or_and_distrib]

/-- The state after `i` steps of a scan. -/
def iter (step : Tri → Nat → Tri) (init : Tri) : Nat → Tri
  | 0 => init
  | i + 1 => step (iter step init i) i

def scanAux (step : Tri → Nat → Tri) : Nat → Nat → Tri → Array Tri → Array Tri
  | 0, _, _, acc => acc
  | k + 1, i, s, acc => scanAux step k (i + 1) (step s i) (acc.push s)

/-- `iter step init i` for each `i < n`, computed in one pass. -/
def scan (n : Nat) (step : Tri → Nat → Tri) (init : Tri) : Array Tri := scanAux step n 0 init #[]

theorem scanAux_size (step : Tri → Nat → Tri) (k i : Nat) (s : Tri) (acc : Array Tri) :
    (scanAux step k i s acc).size = acc.size + k := by
  induction k generalizing i s acc with
  | zero => rfl
  | succ k ih => simp only [scanAux, ih, Array.size_push]; omega

theorem scan_size (n : Nat) (step : Tri → Nat → Tri) (init : Tri) : (scan n step init).size = n := by
  simp [scan, scanAux_size]

theorem scanAux_prefix (step : Tri → Nat → Tri) (k i : Nat) (s : Tri) (acc : Array Tri)
    (j : Nat) (hj : j < acc.size) :
    (scanAux step k i s acc).getD j .undecided = acc.getD j .undecided := by
  induction k generalizing i s acc with
  | zero => rfl
  | succ k ih =>
    simp only [scanAux]
    rw [ih _ _ _ (by simp; omega)]
    simp [Array.getD, Array.getElem_push, hj, Nat.lt_succ_of_lt hj]

/-- The state after `m` steps from state `s` at index `i`. -/
def iterFrom (step : Tri → Nat → Tri) : Tri → Nat → Nat → Tri
  | s, _, 0 => s
  | s, i, m + 1 => iterFrom step (step s i) (i + 1) m

theorem scanAux_get (step : Tri → Nat → Tri) (k i : Nat) (s : Tri) (acc : Array Tri) (m : Nat)
    (hm : m < k) :
    (scanAux step k i s acc).getD (acc.size + m) .undecided = iterFrom step s i m := by
  induction k generalizing i s acc m with
  | zero => omega
  | succ k ih =>
    simp only [scanAux]
    cases m with
    | zero =>
      rw [scanAux_prefix _ _ _ _ _ _ (by simp)]
      simp [Array.getD, iterFrom]
    | succ m =>
      have := ih (i + 1) (step s i) (acc.push s) m (by omega)
      simp only [Array.size_push] at this
      rw [show acc.size + (m + 1) = acc.size + 1 + m by omega, this]
      rfl

theorem iterFrom_iter (step : Tri → Nat → Tri) (init : Tri) (i m : Nat) :
    iterFrom step (iter step init i) i m = iter step init (i + m) := by
  induction m generalizing i with
  | zero => rfl
  | succ m ih =>
    show iterFrom step (iter step init (i + 1)) (i + 1) m = iter step init (i + (m + 1))
    rw [ih]
    congr 1
    omega

theorem scan_get (n : Nat) (step : Tri → Nat → Tri) (init : Tri) (i : Nat) (h : i < n) :
    (scan n step init).getD i .undecided = iter step init i := by
  have hs := scanAux_get step n 0 init #[] i h
  simp only [Array.size_empty, Nat.zero_add] at hs
  have hi := iterFrom_iter step init 0 i
  simp only [Nat.zero_add] at hi
  rw [scan, hs]
  exact hi

/-- `once` as a scan: the values of `v` before `i`, or-ed. -/
theorem iter_once (v : Nat → Tri) (i : Nat) :
    iter (fun s j => s.or (v j)) broken i = anyT (List.range i) v := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show (iter (fun s j => s.or (v j)) broken i).or (v i) = anyT (List.range (i + 1)) v
    rw [ih, List.range_succ, anyT_snoc]

/-- `since` as a scan: the state at `i + 1` is `p i`, or the state at `i` with `c i` not holding. -/
theorem iter_since (p c : Nat → Tri) (i : Nat) :
    iter (fun s j => (s.and (c j).not).or (p j)) broken i =
      anyT (List.range i) (fun j => (p j).and
        (allT ((List.range i).filter (j < ·)) fun k => (c k).not)) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show ((iter (fun s j => (s.and (c j).not).or (p j)) broken i).and (c i).not).or (p i) = _
    rw [ih, List.range_succ, anyT_snoc]
    have hlast : allT ((List.range i ++ [i]).filter (i < ·)) (fun k => (c k).not) = kept := by
      have : (List.range i ++ [i]).filter (i < ·) = [] := by
        rw [List.filter_eq_nil_iff]; intro a ha
        simp only [List.mem_append, List.mem_range, List.mem_singleton] at ha
        simp only [decide_eq_true_eq]; omega
      rw [this]; rfl
    rw [hlast, Tri.and_kept_id]
    congr 1
    rw [← anyT_and_right]
    apply anyT_congr
    intro j hj
    have hji : j < i := List.mem_range.mp hj
    have hf : (List.range i ++ [i]).filter (j < ·) = (List.range i).filter (j < ·) ++ [i] := by
      simp [List.filter_append, hji]
    rw [hf, allT_snoc, Tri.and_assoc]

/-- `eventually` as a backward scan: after `k` steps, the values at the last `k` positions, or-ed. -/
theorem iter_eventually (v : Nat → Tri) (n k : Nat) (hk : k ≤ n) :
    iter (fun s m => (v (n - 1 - m)).or s) broken k = anyT (List.range' (n - k) k) v := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (v (n - 1 - k)).or (iter (fun s m => (v (n - 1 - m)).or s) broken k) = _
    rw [ih (by omega)]
    have : List.range' (n - (k + 1)) (k + 1) = (n - 1 - k) :: List.range' (n - k) k := by
      rw [List.range'_succ, show n - (k + 1) + 1 = n - k by omega,
        show n - (k + 1) = n - 1 - k by omega]
    rw [this]
    rfl

/-- The values of a formula at every position, each subformula's computed once; exact for a
link-free formula (`vals_getD`). -/
def vals (ctx : Ctx) : Formula → Array Tri
  | .not φ => (vals ctx φ).map Tri.not
  | .and φ ψ =>
    let a := vals ctx φ
    let b := vals ctx ψ
    Array.ofFn (n := ctx.size) fun i => (a.getD i .undecided).and (b.getD i .undecided)
  | .or φ ψ =>
    let a := vals ctx φ
    let b := vals ctx ψ
    Array.ofFn (n := ctx.size) fun i => (a.getD i .undecided).or (b.getD i .undecided)
  | once φ =>
    let a := vals ctx φ
    scan ctx.size (fun s j => s.or (a.getD j .undecided)) broken
  | since φ χ =>
    let a := vals ctx φ
    let b := vals ctx χ
    scan ctx.size (fun s j => (s.and (b.getD j .undecided).not).or (a.getD j .undecided)) broken
  | eventually φ =>
    let a := vals ctx φ
    let n := ctx.size
    let r := scan n (fun s m => (a.getD (n - 1 - m) .undecided).or s) broken
    Array.ofFn (n := n) fun i =>
      let found := r.getD (n - 1 - i) .undecided
      if found == .broken && !ctx.complete then .undecided else found
  | φ => Array.ofFn (n := ctx.size) fun i => eval ctx 0 i φ

theorem vals_size (ctx : Ctx) (φ : Formula) : (vals ctx φ).size = ctx.size := by
  induction φ with
  | not φ ih => simp [vals, ih]
  | once φ ih => simp [vals, scan_size]
  | since φ χ _ _ => simp [vals, scan_size]
  | eventually φ _ => simp [vals]
  | _ => simp [vals]

/-- A link-free formula's value doesn't depend on the anchor. -/
theorem eval_anchor (ctx : Ctx) (φ : Formula) (h : linkFree φ = true) (a b i : Nat) :
    eval ctx a i φ = eval ctx b i φ := by
  induction φ generalizing i with
  | link l => simp [linkFree] at h
  | not φ ih => simp only [eval]; rw [ih (by simpa [linkFree] using h)]
  | and φ ψ ihφ ihψ =>
    simp only [linkFree, Bool.and_eq_true] at h
    simp only [eval]; rw [ihφ h.1, ihψ h.2]
  | or φ ψ ihφ ihψ =>
    simp only [linkFree, Bool.and_eq_true] at h
    simp only [eval]; rw [ihφ h.1, ihψ h.2]
  | _ => rfl

theorem getD_ofFn {n : Nat} (f : Fin n → Tri) (i : Nat) (h : i < n) :
    (Array.ofFn f).getD i .undecided = f ⟨i, h⟩ := by
  simp [Array.getD, h]

theorem vals_getD (ctx : Ctx) (φ : Formula) (h : linkFree φ = true) (i : Nat) (hi : i < ctx.size) :
    (vals ctx φ).getD i .undecided = eval ctx 0 i φ := by
  induction φ generalizing i with
  | link l => simp [linkFree] at h
  | not φ ih =>
    have hφ : linkFree φ = true := by simpa [linkFree] using h
    have hs : i < (vals ctx φ).size := by rw [vals_size]; exact hi
    have hmap : ((vals ctx φ).map Tri.not).getD i .undecided =
        ((vals ctx φ).getD i .undecided).not := by
      simp [Array.getD, hs]
    simp only [vals]
    rw [hmap, ih hφ i hi]
    rfl
  | and φ ψ ihφ ihψ =>
    simp only [linkFree, Bool.and_eq_true] at h
    simp only [vals]
    rw [getD_ofFn _ _ hi, ihφ h.1 i hi, ihψ h.2 i hi]
    rfl
  | or φ ψ ihφ ihψ =>
    simp only [linkFree, Bool.and_eq_true] at h
    simp only [vals]
    rw [getD_ofFn _ _ hi, ihφ h.1 i hi, ihψ h.2 i hi]
    rfl
  | once φ ih =>
    have hφ : linkFree φ = true := by simpa [linkFree] using h
    simp only [vals]
    rw [scan_get _ _ _ _ hi, iter_once]
    simp only [eval]
    apply anyT_congr
    intro j hj
    have hj' : j < ctx.size := by have := List.mem_range.mp hj; omega
    rw [ih hφ j hj', eval_anchor ctx φ hφ 0 i]
  | since φ χ ihφ ihχ =>
    simp only [linkFree, Bool.and_eq_true] at h
    simp only [vals]
    rw [scan_get _ _ _ _ hi]
    rw [iter_since (fun j => (vals ctx φ).getD j .undecided) (fun j => (vals ctx χ).getD j .undecided)]
    simp only [eval]
    apply anyT_congr
    intro j hj
    have hj' : j < ctx.size := by have := List.mem_range.mp hj; omega
    rw [ihφ h.1 j hj', eval_anchor ctx φ h.1 0 i]
    congr 1
    apply allT_congr
    intro k hk
    have hk' : k < ctx.size := by
      have := List.mem_range.mp (List.mem_filter.mp hk).1; omega
    rw [ihχ h.2 k hk', eval_anchor ctx χ h.2 0 i]
  | eventually φ ih =>
    have hφ : linkFree φ = true := by simpa [linkFree] using h
    simp only [vals]
    rw [getD_ofFn _ _ hi]
    simp only
    rw [scan_get ctx.size _ _ (ctx.size - 1 - i) (by omega),
      iter_eventually (fun j => (vals ctx φ).getD j .undecided) ctx.size (ctx.size - 1 - i)
        (by omega)]
    have hr : List.range' (ctx.size - (ctx.size - 1 - i)) (ctx.size - 1 - i) =
        List.range' (i + 1) (ctx.size - (i + 1)) := by
      congr 1 <;> omega
    rw [hr]
    have hany : (anyT (List.range' (i + 1) (ctx.size - (i + 1))) fun j =>
        (vals ctx φ).getD j .undecided) =
        anyT (List.range' (i + 1) (ctx.size - (i + 1))) fun j => eval ctx i j φ := by
      apply anyT_congr
      intro j hj
      have hj' : j < ctx.size := by have := List.mem_range'_1.mp hj; omega
      rw [ih hφ j hj', eval_anchor ctx φ hφ 0 i]
    rw [hany]
    rfl
  | _ => simp [vals, getD_ofFn _ _ hi]

/-- `eval`, skipping the second operand of a conjunction whose first is broken and of a disjunction
whose first is kept. -/
def evalLazy (ctx : Ctx) (anchor i : Nat) : Formula → Tri
  | .not φ => (evalLazy ctx anchor i φ).not
  | .and φ ψ => match evalLazy ctx anchor i φ with
    | .broken => .broken
    | x => x.and (evalLazy ctx anchor i ψ)
  | .or φ ψ => match evalLazy ctx anchor i φ with
    | .kept => .kept
    | x => x.or (evalLazy ctx anchor i ψ)
  | once φ => anyT (List.range i) fun j => evalLazy ctx i j φ
  | eventually φ =>
    let found := anyT (List.range' (i + 1) (ctx.size - (i + 1))) fun j => evalLazy ctx i j φ
    if found == broken && !ctx.complete then undecided else found
  | since φ χ => anyT (List.range i) fun j =>
    (evalLazy ctx i j φ).and
      (allT ((List.range i).filter (j < ·)) fun k => (evalLazy ctx i k χ).not)
  | φ => eval ctx anchor i φ

theorem evalLazy_eq (ctx : Ctx) (φ : Formula) (a i : Nat) : evalLazy ctx a i φ = eval ctx a i φ := by
  induction φ generalizing a i with
  | not φ ih => simp only [evalLazy, eval, ih]
  | and φ ψ ihφ ihψ =>
    simp only [evalLazy, eval, ihφ, ihψ]
    split <;> rename_i h <;> simp_all [Tri.and]
  | or φ ψ ihφ ihψ =>
    simp only [evalLazy, eval, ihφ, ihψ]
    split <;> rename_i h <;> simp_all [Tri.or]
  | once φ ih => simp only [evalLazy, eval, ih]
  | eventually φ ih => simp only [evalLazy, eval, ih]
  | since φ χ ihφ ihχ => simp only [evalLazy, eval, ihφ, ihχ]
  | _ => rfl

/-- A rule's verdict, through `vals` when its formula has no link. -/
def evalAlwaysFast (ctx : Ctx) (φ : Formula) : Tri :=
  if linkFree φ then
    let v := vals ctx φ
    allT (List.range ctx.size) fun i => v.getD i .undecided
  else allT (List.range ctx.size) fun i => evalLazy ctx i i φ

theorem evalAlwaysFast_eq (ctx : Ctx) (φ : Formula) : evalAlwaysFast ctx φ = evalAlways ctx φ := by
  unfold evalAlwaysFast evalAlways
  split
  · rename_i h
    apply allT_congr
    intro i hi
    rw [vals_getD ctx φ h i (List.mem_range.mp hi), eval_anchor ctx φ h 0 i]
  · apply allT_congr
    intro i _
    exact evalLazy_eq ctx φ i i

end Rails
