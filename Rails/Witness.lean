import Rails.Fast

/-!
The witness search behind `rails-witness`: whether a rule both keeps and breaks on some trace of a
generated family, so that no formula is constant. A rule's family is built from its own alphabet (a
neutral event, one event of each kind its atoms are about, its predicates' and relations'
representatives): every trace of at most three steps over the alphabet, in three layouts (one
message; one message per step; one per step, five minutes apart, so a time bound can break), under
every assignment of true and false to the rule's atoms and links by name, the same at every
position. Pure; the executable prints what it finds.
-/

namespace Rails.Witness
open Rails

/-- An event of each kind, for atoms about that kind. -/
def kindEvent : Kind → Event
  | .user => .user "u"
  | .reply => .reply "r"
  | .thinking => .thinking "t"
  | .call => bash "ls"
  | .result => .result "c" "out"
  | .refusal => .refusal "hook" "no"
  | .edit => edit "f"
  | .read => read "f"
  | .push => bash "git push origin b"
  | .publish => bash "gh pr create --fill"
  | .any => .thinking "t"

/-- The rule's alphabet, each event once. -/
def alphabet (φ : Formula) : List Event :=
  (([Event.thinking "t"] ++ φ.atoms.map (fun (a : Atom) => kindEvent a.on) ++
    φ.preds.flatMap (fun (p : Pred) => p.samples) ++
    φ.rels.flatMap (fun (r : Rel) => r.samples.flatMap fun (a, b) => [a, b])) : List Event).eraseDups

/-- Every list of at most `n` events over the alphabet, the empty one excluded. -/
def sequences (al : List Event) : Nat → List (List Event)
  | 0 => []
  | n + 1 => al.map ([·]) ++ (sequences al n).flatMap fun s => al.map (· :: s)

/-- A trace in one of the three layouts. -/
def layout (es : List Event) : Nat → Array Step
  | 0 => (es.map fun e => { event := e, message := 0, time := 0 }).toArray
  | 1 => (es.zipIdx.map fun (e, i) => { event := e, message := i, time := i * 1000 }).toArray
  | _ => (es.zipIdx.map fun (e, i) => { event := e, message := i, time := i * 300000 }).toArray

/-- The names the rule's questions are keyed by: its atoms' and links' names, each once. -/
def questionNames (φ : Formula) : List String :=
  (φ.atoms.map (·.name) ++ φ.links.map (·.name)).eraseDups

/-- Every assignment of truth values to the names, as an oracle; above `limit` names, all-true,
all-false and each name alone true and alone false. -/
def assignments (names : List String) (limit : Nat := 10) : List (Query → Option Bool) :=
  let key : Query → String := fun | .atom n _ => n | .link n _ _ => n
  if names.length ≤ limit then
    (List.range (2 ^ names.length)).map fun m q =>
      (names.idxOf? (key q)).map fun k => (m >>> k) % 2 == 1
  else
    let one (t : String) (b : Bool) : Query → Option Bool := fun q =>
      if names.contains (key q) then some (if key q == t then b else !b) else none
    [fun _ => some true, fun _ => some false] ++ names.flatMap fun t => [one t true, one t false]

/-- How many traces the rule's whole family holds. -/
def familySize (φ : Formula) (steps : Nat := 3) : Nat := (sequences (alphabet φ) steps).length * 3

structure Found where
  kept : Bool := false
  broken : Bool := false
  traces : Nat := 0
  sampled : Bool := false
  deriving Repr, Inhabited

/-- Search the family until the rule has both verdicts, or the family is exhausted. -/
def search (φ : Formula) (steps : Nat := 3) : Found := Id.run do
  let names := questionNames φ
  let oracles := assignments names
  let mut f : Found := { sampled := names.length > 10 }
  for es in sequences (alphabet φ) steps do
    for l in [0, 1, 2] do
      let tr := layout es l
      f := { f with traces := f.traces + 1 }
      for o in oracles do
        match evalAlwaysFast (Ctx.build tr true o) φ with
        | .kept => f := { f with kept := true }
        | .broken => f := { f with broken := true }
        | .undecided => pure ()
      if f.kept && f.broken then return f
  return f

end Rails.Witness
