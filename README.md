# rails

Rules for a coding agent as Lean statements over its session trace, checked by an evaluator proved
sound.

- `Rails/Trace.lean`: the trace, one step per event (a user's text, the agent's reply or thinking, a
  tool call and its result, a hook's refusal), with the message each belongs to and its time.
- `Rails/Logic.lean`: formulas over a trace (past and future operators, `since`, links between two
  positions), their meaning as propositions (`Holds`) and a three-valued evaluator (`eval`: kept,
  broken, undecided). Semantic atoms are questions; `Atom.decide` answers those the event's form
  settles, and a model answers the rest.
- `Rails/Soundness.lean`: `eval_sound`: a kept verdict means the formula holds, a broken one that it
  fails, under every reading of the questions agreeing with the answers given.
- `Rails/Rules.lean`: twenty rules sampled from the agents-on-rails consolidation.
- `Rails/Examples.lean`: for each rule, a theorem that its verdict is kept on a trace keeping it and
  broken on one breaking it; the two MAY rules as theorems that the rules allow what they permit.

## The sample

| Rule | Keyword | Domain | Atoms (mechanical decider) |
| --- | --- | --- | --- |
| 1 push needs authorization | MUST NOT | software engineering | `authorizesPush` (false off a user message) |
| 23 running state needs an ask | MUST NOT | discipline | `changesRunningState` (false off a call, and on a request add), `asksForThisChange` (false off a user message) |
| 38 no attribution | MUST NOT | software engineering | none |
| 56 explore before editing | MUST NOT | discipline | `exploratoryRequest`, `confirmsPlan` (false off a user message) |
| 71 no stopping prompt | MUST NOT | tasks | `taskInProgress` (none) |
| 97 no invented progress | MUST NOT | mathematics | `inventsProgress` (false off a reply) |
| 838 no read after write in one message | MUST NOT | software engineering | none |
| 7 a blocked step becomes a request | MUST | tasks | `needsUserAction` (false off a reply) |
| 53 a question is no go-ahead | MUST | discipline | `changesRunningState`, `onlyAsks` (false off a user message) |
| 110 a pass rests on its run | MUST | discipline | `claimsCheckPasses` (false off a reply), link `runOfClaimedCheck` (none) |
| 170 check after a deploy | MUST | software engineering | `pushDeploys` (false off a push), `checksRunningSystem` (false off a call) |
| 341 read a claim first | MUST | mathematics | `reliesOnClaim` (false off a reply), link `readsReliedClaim` (none) |
| 383 the invariant before the fix | MUST | discipline | `isFix` (false off an edit), link `statesFixedInvariant` (none) |
| 420 exact finite-field arithmetic | MUST | mathematics | `floatingPointOverFiniteField` (false off an edit) |
| 605 one reviewer per round | SHOULD | tasks | link `sameRound` (none), `justified` (none) |
| 844 an algebra system first | SHOULD | mathematics | `writesKernel` (false off an edit), link `weighsAlgebraSystems`, `justified` (none) |
| 677 no long wait | SHOULD NOT | tasks | `asksUserAndStops` (false off a reply), `nothingUnblocked`, `justified` (none) |
| 926 general claims over cases | SHOULD NOT | mathematics | `addsCaseToList` (false off a reply), `generalClaimStated`, `justified` (none) |
| 9 a request any time | MAY | tasks | theorem: a request add breaks none of the rules above |
| 1293 a plain push needs no system check | MAY | software engineering | theorem: rule 170 holds after a push that deploys nothing |

Rule numbers are those of `tasks/agents-on-rails/RULES.md` in the workspace that consolidated them.

## Checking

```
lake build
```

Every verdict and the soundness theorem are checked by the kernel; there are no tests, since nothing
here does I/O.
