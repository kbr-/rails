import Lean.Data.Json
import Rails.Trace

/-!
The refusal dataset's session files into traces. A session file holds one JSON record per line:
`meta`, `turn_record` (an event at a `position`), and `example` and `correction` (labels). A session
longer than one file continues in `NAME.2.jsonl`, `NAME.3.jsonl` and so on.

The pure core classifies a line (`parseLine`), orders a session's events by position, groups the
agent's consecutive events into messages and counts every line it couldn't turn into an event
(`assemble`); the file reading is `Rails.ExtractIO`.
-/

namespace Rails.Extract
open Lean

/-- A string of decimal digits as a number; `none` for an empty list or any other character. -/
def digits : List Char → Option Nat
  | [] => none
  | c :: cs => cs.foldl (fun acc d => acc.bind fun n =>
      if d.isDigit then some (n * 10 + (d.toNat - '0'.toNat)) else none)
    (if c.isDigit then some (c.toNat - '0'.toNat) else none)

/-- Days from 1970-01-01 to a date of the proleptic Gregorian calendar, from year 1970 on. -/
def daysFromCivil (y m d : Nat) : Nat :=
  let y' := if m ≤ 2 then y - 1 else y
  let era := y' / 400
  let yoe := y' - era * 400
  let mp := if m > 2 then m - 3 else m + 9
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- Milliseconds since the epoch of a time written `YYYY-MM-DDTHH:MM:SS.mmmZ`, from 1970 on;
`none` for any other form or a field out of range. -/
def parseTime (s : String) : Option Nat :=
  match s.toList with
  | [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, 'T', h1, h2, ':', n1, n2, ':', s1, s2, '.',
     f1, f2, f3, 'Z'] => do
    let y ← digits [y1, y2, y3, y4]
    let m ← digits [m1, m2]
    let d ← digits [d1, d2]
    let h ← digits [h1, h2]
    let n ← digits [n1, n2]
    let sec ← digits [s1, s2]
    let f ← digits [f1, f2, f3]
    if 1970 ≤ y ∧ 1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d ∧ d ≤ 31 ∧ h < 24 ∧ n < 60 ∧ sec < 60 then
      some ((daysFromCivil y m d * 86400 + h * 3600 + n * 60 + sec) * 1000 + f)
    else none
  | _ => none

/-- What one line of a session file is. -/
inductive Line where
  /-- An event at its position; `agent` for the agent's own text, thinking and calls. -/
  | turn (turnId : String) (position : Nat) (agent : Bool) (event : Event) (time : Option Nat)
  | label
  | metadata
  /-- A `turn_record` of a role and kind the trace has no event for. -/
  | unknownKind (role kind : String)
  /-- A record of a type this reader doesn't know, or a `turn_record` without its position. -/
  | unknownRecord
  | unparsable
  deriving Inhabited

/-- A call's input as its fields, a string field as itself and any other value as its JSON. An input
that is a string (every Codex call's, its `exec` command text among them) is the field `input`. -/
def fields : Json → List (String × String)
  | .obj kvs => kvs.toList.map fun (k, v) => (k, match v with
      | .str s => s
      | other => other.compress)
  | .str s => [("input", s)]
  | _ => []

/-- A parsed record as a line of the trace. -/
def classify (j : Json) : Line :=
  match j.getObjValAs? String "record" with
  | .ok "turn_record" =>
    match j.getObjValAs? Nat "position", j.getObjVal? "data" with
    | .ok position, .ok data =>
      let str (key : String) : String := (data.getObjValAs? String key).toOption.getD ""
      let time := parseTime (str "time")
      let input := (data.getObjVal? "input").toOption.getD .null
      let failed := (data.getObjValAs? Bool "is_error").toOption.getD false
      let tid := (j.getObjValAs? String "turn").toOption.getD ""
      match str "role", str "kind" with
      | "user", "text" => .turn tid position false (.user (str "text")) time
      | "assistant", "text" => .turn tid position true (.reply (str "text")) time
      | "assistant", "thinking" => .turn tid position true (.thinking (str "text")) time
      | "assistant", "tool_call" =>
        .turn tid position true (.call (str "call") (str "tool") (fields input)) time
      | "tool", "tool_result" =>
        .turn tid position false (.result (str "call") (str "output") failed) time
      | "hook", "refusal" => .turn tid position false (.refusal (str "hook") (str "text")) time
      | role, kind => .unknownKind role kind
    | _, _ => .unknownRecord
  | .ok "example" | .ok "correction" => .label
  | .ok "meta" => .metadata
  | _ => .unknownRecord

def parseLine (line : String) : Line :=
  match Json.parse line with
  | .ok j => classify j
  | .error _ => .unparsable

/-- What a session's lines held. -/
structure Summary where
  lines : Nat := 0
  events : Nat := 0
  labels : Nat := 0
  metas : Nat := 0
  unknownKind : Nat := 0
  unknownRecord : Nat := 0
  unparsable : Nat := 0
  /-- Events whose time didn't parse; their step's time is 0. -/
  untimed : Nat := 0
  /-- Positions missing in a turn: before its first event (expected 0, or one past the same turn's
  previous run) and between its events. -/
  gaps : Nat := 0
  /-- Events sharing a position with the event before them in their turn. -/
  repeats : Nat := 0
  /-- Events at a position below the one before them in their turn. -/
  backwards : Nat := 0
  deriving Repr, DecidableEq, Inhabited

def Summary.add (a b : Summary) : Summary where
  lines := a.lines + b.lines
  events := a.events + b.events
  labels := a.labels + b.labels
  metas := a.metas + b.metas
  unknownKind := a.unknownKind + b.unknownKind
  unknownRecord := a.unknownRecord + b.unknownRecord
  unparsable := a.unparsable + b.unparsable
  untimed := a.untimed + b.untimed
  gaps := a.gaps + b.gaps
  repeats := a.repeats + b.repeats
  backwards := a.backwards + b.backwards

/-- The counts of each kind of line. -/
def tally : List Line → Summary
  | [] => {}
  | l :: ls =>
    let s := tally ls
    let s := { s with lines := s.lines + 1 }
    match l with
    | .turn _ _ _ _ time =>
      let u := s.untimed + (if time.isSome then 0 else 1)
      { s with events := s.events + 1, untimed := u }
    | .label => { s with labels := s.labels + 1 }
    | .metadata => { s with metas := s.metas + 1 }
    | .unknownKind .. => { s with unknownKind := s.unknownKind + 1 }
    | .unknownRecord => { s with unknownRecord := s.unknownRecord + 1 }
    | .unparsable => { s with unparsable := s.unparsable + 1 }

/-- An event with its turn and position: (turn, position, agent, event, time). -/
abbrev Rec := String × Nat × Bool × Event × Option Nat

/-- A session's events, in file order. -/
def turns : List Line → List Rec
  | [] => []
  | .turn tid p a e t :: ls => (tid, p, a, e, t) :: turns ls
  | _ :: ls => turns ls

/-- The events in runs of one turn each, in their order. -/
def runs : List Rec → List (List Rec)
  | [] => []
  | r :: rs =>
    match runs rs with
    | (s :: g) :: gs => if s.1 = r.1 then (r :: s :: g) :: gs else [r] :: (s :: g) :: gs
    | gs => [r] :: gs

/-- Gaps, repeats and steps back from position `q` to the next one, `p`. -/
def stepFaults (q p : Nat) : Nat × Nat × Nat :=
  if p = q then (0, 1, 0) else if p < q then (0, 0, 1) else (p - q - 1, 0, 0)

def addFaults (a b : Nat × Nat × Nat) : Nat × Nat × Nat := (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

/-- The faults along a run's positions; `prev` is the position before its first (`none`: the
first is expected at 0). -/
def runFaults : Option Nat → List Nat → Nat × Nat × Nat
  | _, [] => (0, 0, 0)
  | prev, p :: ps =>
    let here := match prev with
      | none => (p, 0, 0)
      | some q => stepFaults q p
    addFaults here (runFaults (some p) ps)

/-- The faults of every run; a run of a turn seen before continues from its last position. -/
def sessionFaults : List (String × Nat) → List (List Rec) → Nat × Nat × Nat
  | _, [] => (0, 0, 0)
  | last, [] :: gs => sessionFaults last gs
  | last, (s :: g) :: gs =>
    let ps := (s :: g).map (·.2.1)
    let f := runFaults (last.lookup s.1) ps
    addFaults f (sessionFaults ((s.1, ps.getLast?.getD 0) :: last) gs)

/-- Message numbers: the agent's consecutive events share one, every other event has its own. -/
def messages : Option Bool → Nat → List Bool → List Nat
  | _, _, [] => []
  | prev, n, a :: as =>
    let m := match prev with
      | none => n
      | some p => if p && a then n else n + 1
    m :: messages (some a) m as

/-- A session's lines as its trace and their summary. -/
def assemble (lines : List Line) : Array Step × Summary :=
  let gs := (runs (turns lines)).map fun g => g.mergeSort (fun x y => x.2.1 ≤ y.2.1)
  let ts := gs.flatten
  let msgs := messages none 0 (ts.map (·.2.2.1))
  let steps := (ts.zip msgs).map fun ((_, _, _, e, t), m) =>
    ({ event := e, message := m, time := t.getD 0 } : Step)
  let (gaps, repeats, backwards) := sessionFaults [] gs
  (steps.toArray, { tally lines with gaps, repeats, backwards })

/-- The latest of some ISO 8601 times of one zone and form, which order as strings; `none` for no
time. -/
def latest : List String → Option String
  | [] => none
  | t :: ts => match latest ts with
    | none => some t
    | some u => some (if t < u then u else t)

/-- A directory the reader walks: not a hidden one (such as `.git`). -/
def walked (name : String) : Bool := !name.startsWith "."

/-! A session's file parts. -/

private def stripSuffix (suffix : List Char) (s : List Char) : Option (List Char) :=
  let rs := s.reverse
  if hasPrefix suffix.reverse rs then some (rs.drop suffix.length).reverse else none

/-- A session file's name as its session and part number: `NAME.jsonl` is part 1, `NAME.N.jsonl`
part `N`. `none` for a name that isn't a session file. -/
def partOf (name : String) : Option (String × Nat) :=
  match stripSuffix ".jsonl".toList name.toList with
  | none => none
  | some stem =>
    let rs := stem.reverse
    let num := (rs.takeWhile Char.isDigit).reverse
    let whole := some (String.ofList stem, 1)
    match rs.dropWhile Char.isDigit, digits num with
    | '.' :: base, some n => if 2 ≤ n then some (String.ofList base.reverse, n) else whole
    | _, _ => whole

end Rails.Extract
