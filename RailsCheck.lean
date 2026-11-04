import Rails.ExtractIO
import Rails.Check

/-!
`rails-check DATASET [VERDICTS-FILE]`: every rule on every session of a refusal dataset, its
semantic atoms unanswered (no model yet), printing each rule's sessions kept, broken and undecided
with the time it took, and the time per event. Each session's rules run as tasks of their own. With
a verdicts file, each session a rule doesn't keep is written there, one line each: the rule, its
verdict and the session's first part, for comparison with an independent count.
-/

open Rails Rails.Extract Rails.Check

def main (args : List String) : IO UInt32 := do
  match args with
  | root :: rest =>
    if rest.length > 1 then
      IO.eprintln "usage: rails-check DATASET-DIRECTORY [VERDICTS-FILE]"
      return 2
    let start ← IO.monoMsNow
    let (sessions, _) ← listSessions root
    let sessionTasks ← sessions.mapM fun session => IO.asTask do
      let (steps, s) ← readSession session
      let ctx := Ctx.build steps true fun _ => none
      let results ← Rules.all.mapM fun r => do
        let t0 ← IO.monoNanosNow
        let v ← IO.lazyPure fun _ => check r ctx
        let t1 ← IO.monoNanosNow
        return (Counts.of v, t1 - t0)
      return (session.headD "", s.events, results)
    let mut events := 0
    let mut totals : List (Counts × Nat) := Rules.all.map fun _ => ({}, 0)
    let mut verdicts : Array String := #[]
    for task in sessionTasks do
      let (name, n, results) ← IO.ofExcept task.get
      events := events + n
      totals := (totals.zip results).map fun ((a, ta), (b, tb)) => (a.add b, ta + tb)
      for (r, (c, _)) in Rules.all.zip results do
        if c.broken > 0 then verdicts := verdicts.push s!"{r.number} broken {name}"
        else if c.undecided > 0 then verdicts := verdicts.push s!"{r.number} undecided {name}"
    if let [file] := rest then
      IO.FS.writeFile file ("\n".intercalate verdicts.toList ++ "\n")
    let elapsed := (← IO.monoMsNow) - start
    IO.println s!"sessions {sessions.length}, events {events}, in {elapsed} ms wall \
      ({(elapsed * 1000000) / (max events 1)} ns per event, reading included)"
    IO.println "rule kept broken undecided cpu-ms"
    for (r, (c, ns)) in Rules.all.zip totals do
      IO.println s!"{r.number} {c.kept} {c.broken} {c.undecided} {ns / 1000000}"
    return 0
  | [] =>
    IO.eprintln "usage: rails-check DATASET-DIRECTORY [VERDICTS-FILE]"
    return 2
