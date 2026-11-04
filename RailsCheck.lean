import Rails.ExtractIO
import Rails.Check

/-!
`rails-check DATASET`: every rule on every session of a refusal dataset, its semantic atoms
unanswered (no model yet), printing each rule's sessions kept, broken and undecided with the time
it took, and the time per event. Each session's rules run as tasks of their own.
-/

open Rails Rails.Extract Rails.Check

def main (args : List String) : IO UInt32 := do
  match args with
  | [root] =>
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
      return (s.events, results)
    let mut events := 0
    let mut totals : List (Counts × Nat) := Rules.all.map fun _ => ({}, 0)
    for task in sessionTasks do
      let (n, results) ← IO.ofExcept task.get
      events := events + n
      totals := (totals.zip results).map fun ((a, ta), (b, tb)) => (a.add b, ta + tb)
    let elapsed := (← IO.monoMsNow) - start
    IO.println s!"sessions {sessions.length}, events {events}, in {elapsed} ms wall \
      ({(elapsed * 1000000) / (max events 1)} ns per event, reading included)"
    IO.println "rule kept broken undecided cpu-ms"
    for (r, (c, ns)) in Rules.all.zip totals do
      IO.println s!"{r.number} {c.kept} {c.broken} {c.undecided} {ns / 1000000}"
    return 0
  | _ =>
    IO.eprintln "usage: rails-check DATASET-DIRECTORY"
    return 2
