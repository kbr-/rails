import Rails.RuleText

/-!
The generated table against RULES.md: every rule 1 to 1403, in order, and the keywords of rules
read in the file by hand (1 a MUST NOT, 9 a MAY, 657 a MUST then a MUST).

These are facts about generated data, proved by `native_decide`, which trusts the compiled
evaluation (the axiom `Lean.ofReduceBool`): the kernel's own evaluation of the 1403 entries ran out
of memory (5.84 GiB of RAM and 1.42 GiB of swap after 46 s), and the elaborator's exceeds its
recursion depth. No theorem about the rules' logic rests on them.
-/

namespace Rails.RuleText
open Rails.RuleTextParse

theorem numbers : entries.toList.map (·.number) = List.range' 1 1403 := by native_decide

theorem r1_keywords : (entries[0]!).keywords.head? = some .mustNot := by native_decide
theorem r9_keywords : (entries[8]!).keywords = [.may] := by native_decide
theorem r657_keywords : (entries[656]!).keywords = [.must, .must] := by native_decide

end Rails.RuleText
