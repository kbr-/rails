import Rails.ExtractIO

/-!
Tests of what reads files: a session split over two parts, with lines of every kind, written by
hand into a new directory. The pure core's properties are theorems (`Rails.ExtractProofs`).
-/

open Rails Rails.Extract

def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

def rec (turn : String) (position : Nat) (role kind body : String) : String :=
  s!"\{\"record\":\"turn_record\",\"turn\":\"{turn}\",\"position\":{position},\"data\":\{\"role\":\"{role}\",\"kind\":\"{kind}\",\"time\":\"2026-10-25T20:16:56.336Z\"{body}}}"

def main : IO UInt32 := do
  let dir := (← IO.FS.createTempDir) / "dataset" / "claude" / "ab"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "s1.jsonl") (String.intercalate "\n" [
    "{\"record\":\"meta\",\"data\":{}}",
    rec "t1" 0 "user" "text" ",\"text\":\"run it\"",
    rec "t1" 1 "assistant" "tool_call"
      ",\"call\":\"c1\",\"tool\":\"Bash\",\"input\":{\"command\":\"git push\",\"timeout\":5}",
    rec "t1" 2 "assistant" "tool_call" ",\"call\":\"c2\",\"tool\":\"Read\",\"input\":{}",
    rec "t1" 3 "tool" "tool_result" ",\"call\":\"c1\",\"output\":\"ok\",\"is_error\":true",
    "not json",
    rec "t1" 5 "robot" "beep" "",
    "{\"record\":\"example\",\"data\":{}}"] ++ "\n")
  IO.FS.writeFile (dir / "s1.2.jsonl") (rec "t1" 7 "hook" "refusal" ",\"hook\":\"h\",\"text\":\"no\"" ++
    "\n" ++ rec "t2" 0 "assistant" "text" ",\"text\":\"done\"" ++ "\n")
  IO.FS.writeFile (dir / "notes.txt") "not a session\n"
  let hidden := dir.parent.get!.parent.get! / ".git"
  IO.FS.createDirAll hidden
  IO.FS.writeFile (hidden / "x.jsonl") (rec "t9" 0 "user" "text" ",\"text\":\"inside .git\"" ++ "\n")
  let (sessions, skipped) ← listSessions (dir.parent.get!.parent.get!)
  ensure (sessions.length == 1) s!"{sessions.length} sessions, expected the two parts as one"
  ensure (skipped == 1) s!"{skipped} files skipped, expected notes.txt"
  let (steps, s) ← readSession sessions.head!
  ensure (s.lines == 10) s!"{s.lines} lines counted, expected 10"
  ensure (s.events == 6 && s.metas == 1 && s.labels == 1 && s.unparsable == 1 && s.unknownKind == 1)
    s!"counts {repr s}"
  -- t1 runs 0 1 2 3 (4 and 5 aren't events: 5 is the unknown kind) then 7 in part two: gaps 4, 5, 6.
  ensure (s.gaps == 3 && s.repeats == 0 && s.backwards == 0) s!"position faults {repr s}"
  ensure (steps.size == 6) s!"{steps.size} steps"
  ensure (steps.map (·.message) == #[0, 1, 1, 2, 3, 4])
    s!"messages {steps.map (·.message)}: the two calls are one message"
  ensure (steps[1]!.event == .call "c1" "Bash" [("command", "git push"), ("timeout", "5")])
    s!"call read as {repr steps[1]!.event}"
  ensure (steps[3]!.event == .result "c1" "ok" true) s!"result read as {repr steps[3]!.event}"
  ensure (steps[4]!.event == .refusal "h" "no") "the second part follows the first"
  ensure (steps[0]!.time == 1792959416336) s!"time {steps[0]!.time}"
  IO.println "PASS: extractor (parts, kinds, counts, faults, messages, fields, times)"
  return 0
