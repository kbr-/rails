import Rails.Ledger

/-! The ledger's audit, and `gaps` when `SPEC_TOOLS_GAPS=MODEL` is set: run with
`lake env lean RailsLedger.lean`, outside the library so a build doesn't run them. -/

#eval SpecTools.Audit.run Rails.Ledger.ledger `Rails.Ledger

#eval show Lean.Elab.Command.CommandElabM Unit from do
  if let some model ← IO.getEnv "SPEC_TOOLS_GAPS" then
    SpecTools.Gaps.run Rails.Ledger.ledger Rails.Ledger.prose
      { harness := .claudeCode, model, dataGoesTo := "Anthropic" }
