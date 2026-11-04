import Rails.ExtractIO

/-!
`rails-extract DATASET`: read every session of a refusal dataset and print what was read: the
sessions, the events, each kind of line not turned into an event, the position faults, the time it
took, and the latest time the dataset's manifest records.
-/

open Rails Rails.Extract Lean

def latestManifestTime (root : System.FilePath) : IO String := do
  let path := root / "manifest.json"
  unless ← path.pathExists do return "no manifest"
  match Json.parse (← IO.FS.readFile path) with
  | .ok (.obj kvs) =>
    let times := kvs.toList.filterMap fun ((_ : String), (v : Json)) =>
      (v.getObjValAs? String "at").toOption
    return (latest times).getD "none recorded"
  | _ => return "manifest unparsable"

def main (args : List String) : IO UInt32 := do
  match args with
  | [root] =>
    let start ← IO.monoMsNow
    let (sessions, skipped) ← listSessions root
    -- Sessions are independent: each is read in a task of its own, on Lean's thread pool.
    let tasks ← sessions.mapM fun session => IO.asTask (do return (← readSession session).2)
    let mut total : Summary := {}
    for task in tasks do
      total := total.add (← IO.ofExcept task.get)
    let parts := (sessions.map List.length).sum
    let elapsed := (← IO.monoMsNow) - start
    IO.println s!"sessions {sessions.length} in {parts} files, {skipped} other files skipped"
    IO.println s!"lines {total.lines}: events {total.events}, labels {total.labels}, \
      meta {total.metas}, unknown kind {total.unknownKind}, unknown record {total.unknownRecord}, \
      unparsable {total.unparsable}"
    IO.println s!"events untimed {total.untimed}; positions: gaps {total.gaps}, \
      repeats {total.repeats}, backwards {total.backwards}"
    IO.println s!"manifest latest {← latestManifestTime root}; read in {elapsed} ms"
    return 0
  | _ =>
    IO.eprintln "usage: rails-extract DATASET-DIRECTORY"
    return 2
