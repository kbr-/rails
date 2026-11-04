import Rails.Label

/-!
The window's guarantees: the model never reads a refusal, so no hook's verdict reaches it; and the
window ends before the refused step.
-/

namespace Rails.Label
open Rails

/-- No step the model reads is a refusal. -/
theorem window_no_refusal (steps : Array Step) (i : Nat) :
    ∀ s ∈ window steps i, isRefusal s.event = false := by
  intro s hs
  simp only [window, List.mem_filter] at hs
  simpa using hs.2

/-- The window holds at most the steps between its start and the refused step. -/
theorem window_length_le (steps : Array Step) (i : Nat) :
    (window steps i).length ≤ i - windowStart steps i := by
  unfold window
  exact Nat.le_trans (List.length_filter_le _ _) (List.length_take_le _ _)

/-- Witness: a refusal naming a check is a candidate, another refusal isn't. -/
example : names ["stop_checks:result"] (.refusal "Stop" "x [stop_checks:result: refusal 3]") = true := by
  decide
example : names ["stop_checks:result"] (.refusal "Stop" "x [stop_checks:judge: refusal 3]") = false := by
  decide

end Rails.Label
