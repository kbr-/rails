import Rails.Logic
import Std.Data.HashMap
import Std.Data.HashSet

/-!
Measures of a ruleset, for the model's review and the atoms' merge: how many atoms, links,
predicates and relations it names, how many rules use each, which atoms share a question, which
formula constructors and shapes occur. Pure, over any list of formulas with their rule numbers.
-/

namespace Rails.Measures
open Rails

/-- The constructors a formula uses, with repeats. -/
def constructors : Formula → List String
  | .ev _ => ["ev"]
  | .atom _ => ["atom"]
  | .link _ => ["link"]
  | .sameMessage _ => ["sameMessage"]
  | .gapAtMost _ => ["gapAtMost"]
  | .not φ => "not" :: constructors φ
  | .and φ ψ => "and" :: (constructors φ ++ constructors ψ)
  | .or φ ψ => "or" :: (constructors φ ++ constructors ψ)
  | .once φ => "once" :: constructors φ
  | .eventually φ => "eventually" :: constructors φ
  | .since φ ψ => "since" :: (constructors φ ++ constructors ψ)

/-- A formula that is one judgement of one event: `never (ev p ∧ₗ atom a)` or `never (atom a)`. -/
def isOneJudgement : Formula → Bool
  | .not (.and (.ev _) (.atom _)) | .not (.atom _) => true
  | _ => false

/-- A formula with no temporal operator (no `once`, `eventually`, `since`, `gapAtMost`). -/
def isStatic (φ : Formula) : Bool :=
  !(constructors φ).any (fun c => c == "once" || c == "eventually" || c == "since" || c == "gapAtMost")

/-- Each key with how many times it occurs, most frequent first. -/
def tally (keys : List String) : List (String × Nat) :=
  let distinct := keys.eraseDups
  (distinct.map fun k => (k, keys.count k)).mergeSort fun a b => a.2 > b.2

/-- A question's normal form for comparing: lower case, letters and digits only. -/
def normalize (q : String) : String := String.ofList ((q.toList.map Char.toLower).filter Char.isAlphanum)

/-- Each key with the distinct values it occurs with, in one pass: each value is normalized once and
compared within its key only, so the cost grows with the list, where a filter per key grows with
its square. -/
def groupDistinct (pairs : List (String × String)) : Std.HashMap String (Std.HashSet String) :=
  pairs.foldl (init := {}) fun m (k, v) => m.insert k ((m.getD k {}).insert v)

/-- The keys of a grouping holding more than one distinct value, sorted. -/
def keysWithSeveral (m : Std.HashMap String (Std.HashSet String)) : List String :=
  ((m.toList.filter fun (_, vs) => vs.size > 1).map (·.1)).mergeSort (· ≤ ·)

/-- An atom's kind as a string, for grouping. -/
def kindKey (a : Atom) : String := reprStr a.on

/-- Atoms whose questions are equal once normalized, each group by its names. -/
def sameQuestion (atoms : List Atom) : List (List String) :=
  let m := groupDistinct (atoms.map fun a => (normalize a.question, a.name))
  (keysWithSeveral m).map fun q => ((m.getD q {}).toList.mergeSort (· ≤ ·))

/-- Atoms of one name with different questions or kinds: a clash the merge must resolve. -/
def nameClashes (atoms : List Atom) : List String :=
  keysWithSeveral (groupDistinct (atoms.map fun a => (a.name, normalize a.question ++ "|" ++ kindKey a)))

/-- Links of one name with different questions: answers are keyed by name, so such links would share
one answer. -/
def linkClashes (links : List Link) : List String :=
  keysWithSeveral (groupDistinct (links.map fun l => (l.name, normalize l.question)))

end Rails.Measures
