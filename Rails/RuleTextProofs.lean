import Rails.RuleTextParse

/-!
The keyword reader on the forms RULES.md uses: the two-word forms read as one, several keywords in
order, a keyword only as a whole word.
-/

namespace Rails.RuleTextParse

theorem kw_must_not : keywords "You MUST NOT push.".toList = [.mustNot] := by decide
theorem kw_should_not : keywords "You SHOULD NOT wait.".toList = [.shouldNot] := by decide
theorem kw_order : keywords "You MAY treat it so; you MUST treat the next as new.".toList =
    [.may, .must] := by decide
theorem kw_two_kinds : keywords "You MUST mark it, and its Prevention MUST say so.".toList =
    [.must, .must] := by decide
/-- A keyword is a whole word: not inside a longer word, nor followed by a letter. -/
theorem kw_whole_word : keywords "MUSTER SHOULDER MAYBE AMUST NOTE".toList = [] := by decide
/-- MUST followed by a word other than NOT is MUST. -/
theorem kw_must_note : keywords "You MUST NOTE it.".toList = [.must] := by decide
theorem kw_at_end : keywords "it MAY".toList = [.may] := by decide

/-- The sources are the last bracketed list, cut from the text; a bracket inside the text stays. -/
theorem sources_split : splitSources "You MUST x [a] y. [TP#One; AG#Two]  ".toList =
    ("You MUST x [a] y.".toList, some "TP#One; AG#Two".toList) := by decide
theorem no_sources : splitSources "You MUST x.".toList = ("You MUST x.".toList, none) := by decide
theorem source_codes : codes "TP#Where task state lives; AG#Task execution; ED#Autonomy".toList =
    ["TP", "AG", "ED"] := by decide

end Rails.RuleTextParse
