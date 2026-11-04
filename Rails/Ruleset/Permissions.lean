import Rails.Ruleset.All

/-!
The MAY rules whose theorems in their ranges cover only their own range's rules, stated against the
rule each permission relaxes, wherever that rule is defined. Each theorem runs the permitted trace
with every question a model would be asked answered no (`Range10.keepsAll`): what it shows is that
the rule's mechanical parts (its event predicates, orders and counts) don't refuse the permitted
action; whether a model would answer one of its questions yes for that action is left to the model,
since the permission's content is often that judgement itself (rule 1297: narration that stops a
repeated mistake is no historical narration).
-/

namespace Rails.Ruleset.Permissions
open Rails Rules

/-- Rule 154 (MAY): asking the user to sign in in Firefox, then reading through `firefox_get.py`,
keeps rule 71 (no workflow-stopping prompt) and rule 677 (no wait past two minutes), the rules an
ask of the user meets. -/
theorem r154_ask_keeps_prompt_rules :
    Range10.keepsAll [noStoppingPrompt, noLongWait] Range2.firefoxSessionRead = true := by
  decide

/-- Rule 1072 (MAY): read-only checks combined in one command keep rule 72 (each state change a
command of its own). -/
theorem r1072_combined_reads_keep_one_change_per_command :
    Range10.keepsAll [Range1.oneStateChangePerCommand]
      (Examples.seq [bash "git status && git log --oneline -3 && ls"]) = true := by
  decide

/-- Rule 1297 (MAY): a regression test's comment naming its bug, and a commit message motivating the
approach against a rejected one, keep rule 963 (no historical narration in committed docs). -/
theorem r1297_narration_keeps_rule_963 :
    Range10.keepsAll [Range7.noHistoricalNarration] (Examples.seq
      [.call "e" "Edit" [("file_path", "tests/test_queue.py"),
        ("new_string", "# Regression: the queue dropped the last job when two workers finished at once.")],
       bash "git commit -m 'Use a lock-free queue: a mutex was rejected for its contention'"]) =
      true := by
  decide

/-- Rule 1304 (MAY): logging inside a function keeps rule 982 (effects in a thin outer layer). -/
theorem r1304_logging_keeps_pure_core :
    Range10.keepsAll [Range8.pureCore] (Examples.seq
      [.call "e" "Edit" [("file_path", "tools/solver.py"), ("new_string", "    log.debug(\"step %d\", i)")]]) =
      true := by
  decide

/-- Rule 1384 (MAY): a mutation spec using ISOLATE for an independent service fixture keeps rule 1167
(PATHS only to override the tool's discovery). -/
theorem r1384_isolate_keeps_rule_1167 :
    Range10.keepsAll [Range9.mutantTestSelection] (Examples.seq
      [.call "e" "Edit" [("file_path", "research/results/x/mutants/db_spec.py"),
        ("new_string", "ISOLATE = 'tests/db_fixture.py'")]]) = true := by
  decide

/-- Rule 1385 (MAY): a line-based REPL trial and an exact-column LSP trial keep rule 1185 (the lean-lsp
server, limits reported without it) and rule 467 (a REPL tactic copied into the file and rechecked). -/
theorem r1385_trials_keep_lean_rules :
    Range10.keepsAll [Range9.leanServerOrLimits, Range4.scratchTacticCopied] (Examples.seq
      [.call "r" "mcp__lean-lsp__lean_run_code" [("code", "example : 1 + 1 = 2 := rfl")],
       .call "g" "mcp__lean-lsp__lean_goal" [("file_path", "Rails/Logic.lean"), ("line", "40"),
        ("column", "5")]]) = true := by
  decide

end Rails.Ruleset.Permissions
