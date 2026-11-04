import Rails.Logic

/-!
A module's predicates and relations, each checked against its sample events in a theorem of its
own. The kernel's memory grows with one declaration's evaluation and is let go between declarations
(task lean-build-memory: Range3's 66 predicates checked as one theorem peaked at 3059248 KiB, as one
theorem each at 854844 KiB), so a list's check is assembled from its elements' theorems by
rewriting, and the kernel never evaluates the whole list at once.

`wellFormedPreds preds [p, q]` defines `preds : List Pred := [p, q]`, the theorems
`p_wellFormed : p.wellFormed = true` and `q_wellFormed`, each by `decide +kernel`, and
`preds_wellFormed : preds.all Pred.wellFormed = true` from them. A predicate whose sample its test
refuses fails its own theorem, which names it. `wellFormedRels` is the same for relations.
-/

namespace Rails
open Lean

/-- Each element's theorem `x_wellFormed`, and the list's `NAME_wellFormed` from them. -/
private def wellFormedName (n : Name) : Name := n.appendAfter "_wellFormed"

syntax (name := wellFormedPredsCmd) "wellFormedPreds " ident " [" ident,* "]" : command
syntax (name := wellFormedRelsCmd) "wellFormedRels " ident " [" ident,* "]" : command

macro_rules
  | `(wellFormedPreds $name [$ps,*]) => do
    let elems := ps.getElems
    let thmIds := elems.map fun p => mkIdent (wellFormedName p.getId)
    let thms ← (elems.zip thmIds).mapM fun (p, t) =>
      `(command| theorem $t : Pred.wellFormed $p = true := by decide +kernel)
    let listThm := mkIdent (wellFormedName name.getId)
    let defn ← `(command| def $name : List Pred := [$ps,*])
    let whole ← `(command| theorem $listThm : List.all $name Pred.wellFormed = true := by
      simp only [$name:ident, List.all_cons, List.all_nil, Bool.and_true, $[$thmIds:ident],*])
    return mkNullNode (#[defn] ++ thms ++ #[whole])
  | `(wellFormedRels $name [$rs,*]) => do
    let elems := rs.getElems
    let thmIds := elems.map fun r => mkIdent (wellFormedName r.getId)
    let thms ← (elems.zip thmIds).mapM fun (r, t) =>
      `(command| theorem $t : Rel.wellFormed $r = true := by decide +kernel)
    let listThm := mkIdent (wellFormedName name.getId)
    let defn ← `(command| def $name : List Rel := [$rs,*])
    let whole ← `(command| theorem $listThm : List.all $name Rel.wellFormed = true := by
      simp only [$name:ident, List.all_cons, List.all_nil, Bool.and_true, $[$thmIds:ident],*])
    return mkNullNode (#[defn] ++ thms ++ #[whole])

end Rails
