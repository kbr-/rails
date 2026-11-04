import Rails.Ruleset.Range1
import Rails.Ruleset.Range2
import Rails.Ruleset.Range3
import Rails.Ruleset.Range4
import Rails.Ruleset.Range5
import Rails.Ruleset.Range6
import Rails.Ruleset.Range7
import Rails.Ruleset.Range8
import Rails.Ruleset.Range9
import Rails.Ruleset.Range10
import Rails.Measures

/-!
The whole ruleset: the sample's rules (`Rails.Rules.all`) and every range's, and the MAY rules'
numbers; `coverage` proves that together they are the rules 1 to 1403 of
`tasks/agents-on-rails/RULES.md`, each once.
-/

namespace Rails.Ruleset
open Rails Rules

def allRules : List Rule :=
  Rules.all ++ Range1.rules ++ Range2.rules ++ Range3.rules ++ Range4.rules ++ Range5.rules ++
    Range6.rules ++ Range7.rules ++ Range8.rules ++ Range9.rules ++ Range10.rules

/-- The MAY rules, stated as theorems: the sample's 9 and 1293 in `Rails.Examples`, the others in
their ranges. -/
def allPermissions : List Nat :=
  [9, 1293] ++ Range1.permissions ++ Range2.permissions ++ Range3.permissions ++
    Range4.permissions ++ Range5.permissions ++ Range6.permissions ++ Range7.permissions ++
    Range8.permissions ++ Range9.permissions ++ Range10.permissions

/-- The numbers of every formula rule and every MAY rule. -/
def allNumbers : List Nat := allRules.map (·.number) ++ allPermissions

/-- Every rule 1 to 1403 has exactly one formula or permission, and nothing else is numbered: each
number occurs once and the list holds 1403. A fact about generated data, so it trusts compiled
evaluation (`native_decide`): the kernel's evaluation of the 1403 rules ran out of memory. -/
theorem coverage :
    ((List.range' 1 1403).all fun n => allNumbers.count n == 1) && allNumbers.length == 1403 := by
  native_decide

/-- Every atom and every link the rules name. -/
def allAtoms : List Atom := allRules.flatMap (·.formula.atoms)
def allLinks : List Link := allRules.flatMap (·.formula.links)

/-- No name carries two questions: a model's answers are keyed by name (`Query.atom`,
`Query.link`), so two atoms or two links sharing a name would share one answer to different
questions. And no two atoms ask one question under two names. Over generated data, so by
`native_decide`, as `coverage`. -/
theorem namesKeyAnswers :
    Measures.nameClashes allAtoms = [] ∧ Measures.linkClashes allLinks = [] ∧
      Measures.sameQuestion allAtoms = [] := by
  native_decide

/-- A rule's text's keywords, from the table generated from RULES.md. -/
def textKeywords (n : Nat) : List RuleTextParse.Keyword :=
  ((RuleText.entries.find? (·.number == n)).map (·.keywords)).getD []

/-- The rules whose SHOULD clause only restates the alternative their MUST clause leaves, so an
exception to it would excuse nothing: 719, "You MUST NOT load the growing record or index
wholesale; you SHOULD use targeted source passages." -/
def shouldRestatesMust : List Nat := [719]

/-- A rule names the exception `justified` exactly when its text holds a SHOULD or SHOULD NOT,
outside `shouldRestatesMust`: the keyword and the formula can't disagree. Read from the text's
keywords, not the rule's first one, since a MUST rule may carry a SHOULD clause (rule 1302). Over
generated data, by `native_decide`. -/
theorem exceptionsMatchKeywords :
    allRules.all (fun r =>
      shouldRestatesMust.contains r.number ||
        (r.formula.atoms.any (·.name == "justified")) ==
          ((textKeywords r.number).contains .should ||
            (textKeywords r.number).contains .shouldNot)) =
      true := by
  native_decide

end Rails.Ruleset
