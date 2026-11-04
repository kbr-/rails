import Rails.Rules

/-!
For each rule, a trace keeping it and one breaking it, each verdict a theorem: a rule's statement
that couldn't tell the two apart fails to prove here.
-/

namespace Rails.Examples
open Rails Rules

def bash (c : String) : Event := .call "c" "Bash" [("command", c)]
def edit (p : String) : Event := .call "e" "Edit" [("file_path", p)]
def read (p : String) : Event := .call "r" "Read" [("file_path", p)]
def reviewer : Event := .call "a" "Agent" [("subagent_type", "medium-reviewer")]

/-- Events one per message, a second apart. -/
def seq (es : List Event) : Array Step :=
  (es.zipIdx.map fun (e, i) => { event := e, message := i, time := i * 1000 }).toArray

def run (r : Rule) (steps : Array Step) (answers : List (Query × Bool)) (complete := true) : Tri :=
  r.verdict (Ctx.build steps complete fun q => answers.lookup q)

open Query Atom Link

theorem r1_kept : run pushNeedsAuthorization (seq [.user "push it", bash "git push"])
    [(atom authorizesPush 0, true)] = .kept := by decide
theorem r1_broken : run pushNeedsAuthorization (seq [bash "git push"]) [] = .broken := by decide

theorem r23_kept : run runningStateNeedsAsk (seq [.user "restart it", bash "systemctl restart x"])
    [(atom changesRunningState 1, true), (atom asksForThisChange 0, true)] = .kept := by decide
theorem r23_broken : run runningStateNeedsAsk (seq [.user "why is it slow?", bash "systemctl restart x"])
    [(atom changesRunningState 1, true), (atom asksForThisChange 0, false)] = .broken := by decide

theorem r38_kept : run noAttribution (seq [bash "git commit -m fix"]) [] = .kept := by decide
theorem r38_broken : run noAttribution
    (seq [bash "git commit -m 'fix\n\nCo-Authored-By: Claude'"]) [] = .broken := by decide

theorem r56_kept : run exploreBeforeEditing
    (seq [.user "explain this", .reply "the plan", .user "go ahead", edit "a.lean"])
    [(atom exploratoryRequest 0, true), (atom confirmsPlan 2, true),
     (atom exploratoryRequest 2, false)] = .kept := by decide
theorem r56_broken : run exploreBeforeEditing (seq [.user "explain this", edit "a.lean"])
    [(atom exploratoryRequest 0, true)] = .broken := by decide

theorem r71_kept : run noStoppingPrompt (seq [bash "ls"]) [] = .kept := by decide
theorem r71_broken : run noStoppingPrompt (seq [.call "q" "AskUserQuestion" []])
    [(atom taskInProgress 0, true)] = .broken := by decide

theorem r97_kept : run noInventedProgress (seq [.reply "proved"]) [(atom inventsProgress 0, false)] =
    .kept := by decide
theorem r97_broken : run noInventedProgress (seq [.reply "proved"]) [(atom inventsProgress 0, true)] =
    .broken := by decide

theorem r838_kept : run readAfterWrite
    #[{ event := edit "f", message := 0, time := 0 }, { event := read "f", message := 1, time := 1 }]
    [] = .kept := by decide
theorem r838_broken : run readAfterWrite
    #[{ event := edit "f", message := 0, time := 0 }, { event := read "f", message := 0, time := 1 }]
    [] = .broken := by decide

theorem r7_kept : run blockedStepBecomesRequest
    (seq [.reply "this needs your push", bash "python3 tools/task_index.py request add x"])
    [(atom needsUserAction 0, true)] = .kept := by decide
theorem r7_broken : run blockedStepBecomesRequest (seq [.reply "this needs your push"])
    [(atom needsUserAction 0, true)] = .broken := by decide
/-- On a trace that may continue, the missing request is not yet a breach. -/
theorem r7_undecided : run blockedStepBecomesRequest (seq [.reply "this needs your push"])
    [(atom needsUserAction 0, true)] (complete := false) = .undecided := by decide

theorem r53_kept : run questionIsNoGoAhead (seq [.user "restart it", bash "systemctl restart x"])
    [(atom changesRunningState 1, true), (atom onlyAsks 0, false)] = .kept := by decide
theorem r53_broken : run questionIsNoGoAhead (seq [.user "is it down?", bash "systemctl restart x"])
    [(atom changesRunningState 1, true), (atom onlyAsks 0, true)] = .broken := by decide

theorem r110_kept : run passNeedsRun (seq [bash "lake test", .result "c" "PASS", .reply "tests pass"])
    [(atom claimsCheckPasses 2, true), (link runOfClaimedCheck 2 1, true)] = .kept := by decide
theorem r110_broken : run passNeedsRun (seq [.reply "tests pass"])
    [(atom claimsCheckPasses 0, true)] = .broken := by decide

theorem r170_kept : run checkAfterDeploy (seq [bash "git push", bash "curl health"])
    [(atom pushDeploys 0, true), (atom checksRunningSystem 1, true)] = .kept := by decide
theorem r170_broken : run checkAfterDeploy (seq [bash "git push"])
    [(atom pushDeploys 0, true)] = .broken := by decide

theorem r341_kept : run readClaimFirst (seq [read "notebook.html", .reply "by the lemma"])
    [(atom reliesOnClaim 1, true), (link readsReliedClaim 1 0, true)] = .kept := by decide
theorem r341_broken : run readClaimFirst (seq [.reply "by the lemma"])
    [(atom reliesOnClaim 0, true)] = .broken := by decide

theorem r383_kept : run invariantBeforeFix (seq [.reply "it restores: one key per path", edit "f"])
    [(atom isFix 1, true), (link statesFixedInvariant 1 0, true)] = .kept := by decide
theorem r383_broken : run invariantBeforeFix (seq [edit "f"]) [(atom isFix 0, true)] = .broken := by
  decide

theorem r420_kept : run exactFiniteField (seq [edit "rank.c"])
    [(atom floatingPointOverFiniteField 0, false)] = .kept := by decide
theorem r420_broken : run exactFiniteField (seq [edit "rank.c"])
    [(atom floatingPointOverFiniteField 0, true)] = .broken := by decide

theorem r605_kept : run oneReviewerPerRound (seq [reviewer]) [] = .kept := by decide
theorem r605_broken : run oneReviewerPerRound (seq [reviewer, reviewer])
    [(link sameRound 1 0, true), (atom justified 1, false)] = .broken := by decide

theorem r844_kept : run algebraSystemFirst (seq [.reply "Singular can do this?", edit "kernel.c"])
    [(atom writesKernel 1, true), (link weighsAlgebraSystems 1 0, true)] = .kept := by decide
theorem r844_broken : run algebraSystemFirst (seq [edit "kernel.c"])
    [(atom writesKernel 0, true), (atom justified 0, false)] = .broken := by decide

theorem r677_kept : run noLongWait (seq [.reply "which one?", bash "ls"])
    [(atom asksUserAndStops 0, true)] = .kept := by decide
theorem r677_broken : run noLongWait
    #[{ event := .reply "which one?", message := 0, time := 0 },
      { event := .user "the first", message := 1, time := 300000 }]
    [(atom asksUserAndStops 0, true), (atom nothingUnblocked 0, false), (atom justified 0, false)] =
    .broken := by decide

theorem r926_kept : run generalOverCases (seq [.reply "case n = 5 checked"])
    [(atom addsCaseToList 0, true), (atom generalClaimStated 0, true)] = .kept := by decide
theorem r926_broken : run generalOverCases (seq [.reply "case n = 5 checked"])
    [(atom addsCaseToList 0, true), (atom generalClaimStated 0, false), (atom justified 0, false)] =
    .broken := by decide

/-- Rule 1293 (MAY): after a plain branch push, which deploys nothing, no check of a running system
is owed. -/
theorem r1293_plain_push : run checkAfterDeploy (seq [bash "git push origin feature"])
    [(atom pushDeploys 0, false)] = .kept := by decide

/-- An atom a model must answer, left unanswered, leaves the verdict undecided. -/
theorem r97_unanswered : run noInventedProgress (seq [.reply "proved"]) [] = .undecided := by decide

/-- Rule 9 (MAY): adding a request breaks no rule, at any point, with nothing asked of a model. -/
theorem r9_request_always_allowed :
    Rules.all.all (fun r => run r (seq [bash "python3 tools/task_index.py request add x"]) [] ==
      .kept) = true := by decide

/-- The soundness theorem's hypothesis can hold: a context with no answers agrees with any reading. -/
example : Agrees (Ctx.build #[] true fun _ => none) (fun _ => true) := by
  intro q b h
  cases q <;> simp [Ctx.build] at h

end Rails.Examples
