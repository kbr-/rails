import Rails.ExtractIO
import Rails.Label
import SpecTools.Model
import SpecTools.Synthetic

/-!
`rails-label DATASET CHECKS N SEED MODEL OUT`: draw N refusals by the comma-separated CHECKS from a
refusal dataset with SEED, ask a fresh Claude Code MODEL of each whether the turn before it broke
rule 110, and write each verdict to OUT/labels.jsonl (a private directory: it names sessions). The
standard output holds counts only: candidates, asked, broken, kept, failed, and the share of
answered labels agreeing with the hook that the rule was broken.
-/

open Rails Rails.Extract Rails.Label SpecTools.Model

def main (args : List String) : IO UInt32 := do
  match args with
  | [root, checks, n, seed, model, out] =>
    let some n := n.toNat? | IO.eprintln "N is a number"; return 2
    let some seed := seed.toNat? | IO.eprintln "SEED is a number"; return 2
    let checks := checks.splitOn ","
    let (sessions, _) ← listSessions root
    let found ← sessions.mapM fun session => IO.asTask do
      let (steps, _) ← readSession session
      return (candidates checks steps).map fun i => (session, i)
    let mut all : Array (List System.FilePath × Nat) := #[]
    for t in found do all := all ++ (← IO.ofExcept t.get).toArray
    let chosen := (SpecTools.Synthetic.pick seed all.size n).map fun k => all[k]!
    let backend : Backend := { harness := .claudeCode, model, dataGoesTo := "Anthropic" }
    IO.FS.createDirAll out
    let schema := Lean.Json.mkObj [("type", "object"),
      ("properties", Lean.Json.mkObj [("holds", Lean.Json.mkObj [("type", "boolean")])]),
      ("required", Lean.Json.arr #["holds"]), ("additionalProperties", false)]
    -- Five model calls at a time: each harness process holds its own memory.
    let width := 5
    let batches := (List.range ((chosen.length + width - 1) / width)).map fun b =>
      (chosen.drop (b * width)).take width
    let mut results : Array (String × Nat × Except Failure Outcome) := #[]
    for batch in batches do
      let jobs ← batch.mapM fun (session, i) => IO.asTask do
        let (steps, _) ← readSession session
        let question : Question := { prompt := prompt 60000 (window steps i), schema, timeoutMs := 180000 }
        let r ← ask liveRunner [backend] backend question (← IO.FS.createTempDir)
        return ((session.headD "").toString, i, r)
      for j in jobs do results := results.push (← IO.ofExcept j.get)
    let mut lines : Array String := #[]
    let mut broken := 0
    let mut kept := 0
    let mut failed := 0
    for (file, i, r) in results do
      match r with
      | .ok o => match o.answer.getObjValAs? Bool "holds" with
        | .ok b =>
          if b then broken := broken + 1 else kept := kept + 1
          lines := lines.push s!"\{\"file\": {file.quote}, \"position\": {i}, \"broken\": {b}}"
        | .error _ => failed := failed + 1
      | .error _ => failed := failed + 1
    IO.FS.writeFile (System.FilePath.mk out / "labels.jsonl") ("\n".intercalate lines.toList ++ "\n")
    let answered := broken + kept
    IO.println s!"candidates {all.size}, asked {chosen.length}, broken {broken}, kept {kept}, failed {failed}"
    IO.println s!"agreement with the hook (broken of answered): {broken}/{answered}"
    return 0
  | _ =>
    IO.eprintln "usage: rails-label DATASET CHECKS N SEED MODEL OUT"
    return 2
