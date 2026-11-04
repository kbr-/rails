import Rails.Ledger

/-!
Every rule of the sample has a row in `Rails.Ledger.ledger`: the formula rows are `Rules.all` in its
order, and the MAY rows are rules 9 and 1293. Kept outside the ledger's namespace, since the audit
refuses a theorem there that no row claims.
-/

namespace Rails.LedgerCoverage
open Rails Ledger

theorem formula_rows_are_all : formulaRows.map (·.1.number) = Rules.all.map (·.number) := by
  decide

theorem may_rows : mayRows.map (·.1) = [9, 1293] := by decide

end Rails.LedgerCoverage
