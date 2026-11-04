import Rails.Witness
import Rails.Ruleset.All

/-!
`rails-witness`: every rule's witness search over the whole ruleset (`Ruleset.allRules`) (`Rails.Witness.search`), printing each rule with no
kept or no broken verdict over its family, the families' sizes, and the time taken. Exit 1 when a
rule lacks a witness. `rails-witness --control` adds a constant formula, which must be listed.
-/

open Rails Rails.Witness Rails.Rules Formula

/-- A constant formula as a control: `ev p ∨ₗ ¬ₗ ev p` holds at every position. -/
def constantRule : Rule :=
  { number := 0, keyword := .must, domain := .discipline,
    formula := ev Ruleset.reply ∨ₗ ¬ₗ ev Ruleset.reply }

def main (args : List String) : IO UInt32 := do
  let rules := if args.contains "--control" then Ruleset.allRules ++ [constantRule]
    else Ruleset.allRules
  let start ← IO.monoMsNow
  let tasks ← rules.mapM fun r => IO.asTask (pure (r, search r.formula, familySize r.formula))
  let mut lacking := 0
  let mut traces := 0
  let mut family := 0
  let mut sampled := 0
  for t in tasks do
    let (r, f, size) ← IO.ofExcept t.get
    traces := traces + f.traces
    family := family + size
    if f.sampled then sampled := sampled + 1
    if !(f.kept && f.broken) then
      lacking := lacking + 1
      IO.println s!"{r.number}: {if f.kept then "" else "never kept"}{if !f.kept && !f.broken then ", " else ""}{if f.broken then "" else "never broken"} over {f.traces} traces"
  IO.println s!"{rules.length} rules, {lacking} lacking a witness, {traces} traces tried of \
    {family} in the families, {sampled} with sampled assignments, in {(← IO.monoMsNow) - start} ms"
  return if lacking == 0 then 0 else 1
