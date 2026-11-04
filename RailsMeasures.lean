import Rails.Measures
import Rails.Ruleset.All

/-!
`rails-measures`: the ruleset's measures (`Rails.Measures`) printed for the review: counts of
atoms, links, predicates and relations; how many rules use each atom and how many atoms one rule
alone uses; atoms sharing a question and names with two questions; the formula constructors by
use; the rules that are one judgement of one event, and those with no temporal operator.
-/

open Rails Rails.Measures Rails.Rules

def main (_ : List String) : IO UInt32 := do
  let rules := Ruleset.allRules
  let atomsPerRule := rules.map fun r => (r.formula.atoms.map (·.name)).eraseDups
  let atomUses := tally (atomsPerRule.flatten)
  let allAtoms := rules.flatMap (·.formula.atoms)
  let linkNames := (rules.flatMap fun r => (r.formula.links.map (·.name)).eraseDups)
  let predNames := (rules.flatMap fun r => (r.formula.preds.map (·.name)).eraseDups)
  let relNames := (rules.flatMap fun r => (r.formula.rels.map (·.name)).eraseDups)
  IO.println s!"rules {rules.length}"
  IO.println s!"atoms {atomUses.length}, used by one rule only {(atomUses.filter (·.2 == 1)).length}"
  IO.println s!"links {linkNames.eraseDups.length}, predicates {predNames.eraseDups.length}, relations {relNames.eraseDups.length}"
  IO.println s!"atoms sharing a question: {sameQuestion allAtoms}"
  IO.println s!"names with two questions or kinds: {nameClashes allAtoms}"
  IO.println s!"link names with two questions: {linkClashes (rules.flatMap (·.formula.links))}"
  IO.println s!"atom uses (top 15): {atomUses.take 15}"
  IO.println s!"predicate uses (top 15): {(tally predNames).take 15}"
  IO.println s!"constructors by use: {tally (rules.flatMap (·.formula |> constructors))}"
  IO.println s!"rules that are one judgement of one event: {(rules.filter (isOneJudgement ·.formula)).length}"
  IO.println s!"rules with no temporal operator: {(rules.filter (isStatic ·.formula)).length}"
  IO.println s!"rules by keyword: {tally (rules.map fun r => reprStr r.keyword)}"
  return 0
