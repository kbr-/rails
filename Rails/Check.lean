import Rails.Fast
import Rails.Rules

/-!
The checker: every rule on a trace, its mechanical atoms answered by `Atom.decide` and the rest by
whatever oracle is given (none, until a model answers them), each verdict kept, broken or undecided.
-/

namespace Rails.Check
open Rails Rules

/-- A rule's verdict on a context, computed by the fast evaluator. -/
def check (r : Rule) (ctx : Ctx) : Tri := evalAlwaysFast ctx r.formula

/-- The checker's verdict is the rule's (so `evalAlways_sound` holds of it). -/
theorem check_eq (r : Rule) (ctx : Ctx) : check r ctx = r.verdict ctx :=
  evalAlwaysFast_eq ctx r.formula

/-- Verdict counts for each rule. -/
structure Counts where
  kept : Nat := 0
  broken : Nat := 0
  undecided : Nat := 0
  deriving Repr, Inhabited

def Counts.add (a b : Counts) : Counts :=
  ⟨a.kept + b.kept, a.broken + b.broken, a.undecided + b.undecided⟩

def Counts.of : Tri → Counts
  | .kept => ⟨1, 0, 0⟩
  | .broken => ⟨0, 1, 0⟩
  | .undecided => ⟨0, 0, 1⟩

/-- Every rule's verdict on a session's steps, the session complete, with `oracle`'s answers. -/
def checkSession (steps : Array Step) (complete : Bool) (oracle : Query → Option Bool) :
    List Counts :=
  let ctx := Ctx.build steps complete oracle
  Rules.all.map fun r => Counts.of (check r ctx)

end Rails.Check
