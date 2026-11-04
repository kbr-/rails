import SpecTools.Model
import Rails.Check

/-!
Atoms answered by a model, through lean-specification-tools' model interface. The pure core lists
the atom queries the deciders leave open (`openQueries`), writes each one's question (`prompt`),
reads the model's outcomes (`collect`) and adds the answers to a context (`withAnswers`); `askAll`
only runs the questions.
-/

namespace Rails.Atoms
open Rails Lean SpecTools.Model

/-- The atoms of a formula at the positions where neither their decider nor the context answers
them, each once. The formula's atoms are `Formula.atoms`'s, the one recursion over formulas that
lists them, so an operator added to `Formula` reaches the queries. -/
def openQueries (ctx : Ctx) (φ : Formula) : List (Atom × Nat) :=
  let atoms := φ.atoms.eraseDups
  (List.range ctx.size).flatMap fun i =>
    atoms.filterMap fun a => if (ctx.atomAnswer a i).isNone then some (a, i) else none

/-- An event as the text a question about it is asked over. -/
def eventText : Event → String
  | .user t => s!"A message from the user:\n{t}"
  | .reply t => s!"A reply of the agent:\n{t}"
  | .thinking t => s!"The agent's thinking:\n{t}"
  | .call _ tool input =>
    s!"A tool call of the agent, to {tool}, with input:\n" ++
      String.intercalate "\n" (input.map fun (k, v) => s!"{k}: {v}")
  | .result _ output failed => s!"A tool's result ({if failed then "failed" else "succeeded"}):\n{output}"
  | .refusal hook t => s!"A refusal by the hook {hook}:\n{t}"

/-- The answer's schema: one required boolean, nothing else. -/
def answerSchema : Json :=
  Json.mkObj [("type", "object"), ("properties", Json.mkObj [("holds", Json.mkObj [("type", "boolean")])]),
    ("required", Json.arr #["holds"]), ("additionalProperties", false)]

/-- The room left for the event's text in a prompt. -/
def textBudget : Nat := maxPromptBytes / 2

/-- The question for an atom at a position, or none where the position has no step. -/
def prompt (ctx : Ctx) : Atom × Nat → Option String
  | (a, i) => (ctx.step? i).map fun s =>
    let text := eventText s.event
    let text := if text.utf8ByteSize ≤ textBudget then text else String.ofList (text.toList.take textBudget)
    s!"Answer about one event of a coding agent's session, with holds true or false.\n\nQuestion: {a.question}\n\n{text}"

/-- What the model's outcomes gave: the answers, and the failures by kind. -/
structure Collected where
  answers : List (Query × Bool) := []
  refused : Nat := 0
  timedOut : Nat := 0
  exited : Nat := 0
  malformed : Nat := 0
  deriving Inhabited

def answerOf (j : Json) : Option Bool := (j.getObjValAs? Bool "holds").toOption

/-- The answers and failures of a list of outcomes. -/
def collect : List (Query × Except Failure Outcome) → Collected
  | [] => {}
  | (q, r) :: rest =>
    let c := collect rest
    match r with
    | .ok o => match answerOf o.answer with
      | some b => { c with answers := (q, b) :: c.answers }
      | none => { c with malformed := c.malformed + 1 }
    | .error (.refused ..) => { c with refused := c.refused + 1 }
    | .error (.timedOut ..) => { c with timedOut := c.timedOut + 1 }
    | .error (.exited ..) => { c with exited := c.exited + 1 }
    | .error (.malformed ..) => { c with malformed := c.malformed + 1 }

/-- A context with the model's answers added where its deciders gave none. -/
def withAnswers (ctx : Ctx) (answers : List (Query × Bool)) : Ctx :=
  { ctx with answer := fun q => (ctx.answer q).or (answers.lookup q) }

/-- Ask every open atom query of `φ`, one question each; `scratch` gets a directory per question. -/
def askAll (runner : Runner) (allowed : List Backend) (backend : Backend) (ctx : Ctx)
    (φ : Formula) (scratch : System.FilePath) (timeoutMs : Nat) : IO Collected := do
  let mut outcomes : Array (Query × Except Failure Outcome) := #[]
  let mut n := 0
  for (a, i) in openQueries ctx φ do
    match prompt ctx (a, i) with
    | none => pure ()
    | some p =>
      let dir := scratch / s!"q{n}"
      n := n + 1
      IO.FS.createDirAll dir
      let r ← ask runner allowed backend { prompt := p, schema := answerSchema, timeoutMs } dir
      outcomes := outcomes.push (.atom a.name i, r)
  return collect outcomes.toList

end Rails.Atoms
