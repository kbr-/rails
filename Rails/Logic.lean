import Rails.Trace

/-!
The rules' logic: formulas over a trace, evaluated at a position to one of three values (kept,
broken, undecided), and their meaning as propositions. The evaluator's soundness theorem
(`eval_sound`) says that whenever it returns kept or broken, the formula holds or fails under every
reading of the atoms consistent with the answers given; so a rule built from these formulas needs no
proof of its own checker.

An atom is a question about one position (`Atom`), a link a question about two (`Link`): whether a
sentence claims something, whether a result is the run a claim cites. Each is answered by a
mechanical decider where one exists and otherwise by a model; one left unanswered makes what depends
on it undecided. A liveness formula (`eventually`) is undecided on a trace that may continue.
-/

namespace Rails

/-- The kind of event an atom is about: one of the event's forms, or among calls an edit, a read, a
push or a publish, or any event. -/
inductive Kind where
  | user | reply | thinking | call | result | refusal | edit | read | push | publish | any
  deriving Repr, DecidableEq

def isCall : Event → Bool
  | .call .. => true
  | _ => false

def isThinking : Event → Bool
  | .thinking _ => true
  | _ => false

def isResult : Event → Bool
  | .result .. => true
  | _ => false

def isRefusalEvent : Event → Bool
  | .refusal .. => true
  | _ => false

def Kind.holds : Kind → Event → Bool
  | .user, e => isUser e
  | .reply, e => isReply e
  | .thinking, e => isThinking e
  | .call, e => isCall e
  | .result, e => isResult e
  | .refusal, e => isRefusalEvent e
  | .edit, e => isEdit e
  | .read, e => isRead e
  | .push, e => isPush e
  | .publish, e => isPublish e
  | .any, _ => true

/-- A question about one event, asked of a model: its name (the atom's identity in answers and
listings), the question, and the kind of event it is about. -/
structure Atom where
  name : String
  question : String
  on : Kind
  deriving Repr, DecidableEq

/-- A question about an event and the anchor a formula refers it back to. -/
structure Link where
  name : String
  question : String
  deriving Repr, DecidableEq

/-- An event predicate a formula names: its name, its test, and representative events, on each of
which the test holds, from which `rails-witness` builds its traces. -/
structure Pred where
  name : String
  test : Event → Bool
  samples : List Event

/-- A relation between two steps of one message, with representative pairs on which it holds. -/
structure Rel where
  name : String
  test : Step → Step → Bool
  samples : List (Event × Event)

/-- Every representative of a predicate passes its test, and it has one. -/
def Pred.wellFormed (p : Pred) : Bool := !p.samples.isEmpty && p.samples.all p.test

def Rel.wellFormed (r : Rel) : Bool :=
  !r.samples.isEmpty && r.samples.all fun (a, b) =>
    r.test { event := a, message := 0, time := 0 } { event := b, message := 0, time := 0 }

/-- An atom's answer where the event's form decides it: false at an event of another kind than the
atom is about; `none` leaves it to a model. -/
def Atom.decide (a : Atom) (e : Event) : Option Bool := if a.on.holds e then none else some false

/-- A question about the trace: an atom at a position, or a link from an anchor to a position. -/
inductive Query where
  /-- The atom of that name at a position: answers are keyed by name, so comparing two queries
  compares short names, never the questions' text. -/
  | atom (name : String) (at_ : Nat)
  | link (name : String) (anchor at_ : Nat)
  deriving Repr, DecidableEq

inductive Tri where
  | kept | broken | undecided
  deriving Repr, DecidableEq

namespace Tri
def not : Tri → Tri
  | kept => broken | broken => kept | undecided => undecided
def and : Tri → Tri → Tri
  | broken, _ => broken | _, broken => broken | kept, kept => kept | _, _ => undecided
def or : Tri → Tri → Tri
  | kept, _ => kept | _, kept => kept | broken, broken => broken | _, _ => undecided
def ofBool (b : Bool) : Tri := if b then kept else broken
end Tri

/-- Kleene disjunction and conjunction over a list. -/
def anyT {α} (l : List α) (g : α → Tri) : Tri := l.foldr (fun x acc => (g x).or acc) .broken
def allT {α} (l : List α) (g : α → Tri) : Tri := l.foldr (fun x acc => (g x).and acc) .kept

inductive Formula where
  | ev (p : Pred)
  | atom (a : Atom)
  | link (l : Link)
  | sameMessage (r : Rel)
  | not (φ : Formula)
  | and (φ ψ : Formula)
  | or (φ ψ : Formula)
  | once (φ : Formula)
  | eventually (φ : Formula)
  | since (φ χ : Formula)
  /-- φ at a later position, with no χ strictly between: `since`'s mirror, a future bounded by an
  event ("in the same turn": before the next user message). -/
  | before (φ χ : Formula)
  /-- φ at a later position whose time is at most `ms` after this one's (a deadline). -/
  | within (ms : Nat) (φ : Formula)

namespace Formula
def implies (φ ψ : Formula) : Formula := .or (.not φ) ψ
def never (φ : Formula) : Formula := .not φ

/-- What a formula names: its atoms, links, event predicates and relations, with repeats. -/
def atoms : Formula → List Atom
  | atom a => [a]
  | .not φ | once φ | eventually φ | within _ φ => atoms φ
  | .and φ ψ | .or φ ψ | since φ ψ | before φ ψ => atoms φ ++ atoms ψ
  | _ => []

def links : Formula → List Link
  | link l => [l]
  | .not φ | once φ | eventually φ | within _ φ => links φ
  | .and φ ψ | .or φ ψ | since φ ψ | before φ ψ => links φ ++ links ψ
  | _ => []

def preds : Formula → List Pred
  | ev p => [p]
  | .not φ | once φ | eventually φ | within _ φ => preds φ
  | .and φ ψ | .or φ ψ | since φ ψ | before φ ψ => preds φ ++ preds ψ
  | _ => []

def rels : Formula → List Rel
  | sameMessage r => [r]
  | .not φ | once φ | eventually φ | within _ φ => rels φ
  | .and φ ψ | .or φ ψ | since φ ψ | before φ ψ => rels φ ++ rels ψ
  | _ => []
end Formula

prefix:40 "¬ₗ " => Formula.not
infixr:35 " ∧ₗ " => Formula.and
infixr:30 " ∨ₗ " => Formula.or
infixr:25 " ⟹ " => Formula.implies

/-- A trace, whether it is complete, the answers to its questions, and each position's message
peers: the positions of the contiguous run of steps sharing its message number. -/
structure Ctx where
  steps : Array Step
  complete : Bool
  answer : Query → Option Bool
  peers : Nat → List Nat

namespace Ctx
def size (ctx : Ctx) : Nat := ctx.steps.size
def step? (ctx : Ctx) (i : Nat) : Option Step := ctx.steps[i]?

private def sameMsg (steps : Array Step) (i j : Nat) : Bool :=
  (steps[i]?.map (·.message)) == (steps[j]?.map (·.message)) && (steps[i]?).isSome

/-- The first position of the run of equal message numbers ending at `i`. Structural, so the
kernel evaluates it. -/
def runStart (steps : Array Step) : Nat → Nat
  | 0 => 0
  | i + 1 => if sameMsg steps i (i + 1) then runStart steps i else i + 1

/-- One past the last position of the run of equal message numbers from `i`, looking at most
`fuel` positions ahead. -/
def runEnd (steps : Array Step) : Nat → Nat → Nat
  | 0, i => i + 1
  | fuel + 1, i => if sameMsg steps i (i + 1) then runEnd steps fuel (i + 1) else i + 1

/-- A context whose questions `oracle` (a model's answers) answers; an atom's mechanical decider
is applied where the formula is evaluated (`Ctx.atomAnswer`). -/
def build (steps : Array Step) (complete : Bool) (oracle : Query → Option Bool) : Ctx :=
  { steps
    complete
    answer := oracle
    peers := fun i =>
      if i < steps.size then
        let a := runStart steps i
        List.range' a (runEnd steps steps.size i - a)
      else [] }

/-- The atom's answer the event's kind decides, if it does. -/
def decided (ctx : Ctx) (a : Atom) (i : Nat) : Option Bool := (ctx.step? i).bind (a.decide ·.event)

/-- The atom's answer: its decider's, else the context's. -/
def atomAnswer (ctx : Ctx) (a : Atom) (i : Nat) : Option Bool :=
  (ctx.decided a i).or (ctx.answer (.atom a.name i))
end Ctx

open Formula Tri

/-- The formula's value at position `i`, with `anchor` the position a link refers back to. -/
def eval (ctx : Ctx) (anchor i : Nat) : Formula → Tri
  | ev p => match ctx.step? i with
    | some s => ofBool (p.test s.event)
    | none => broken
  | atom a => match ctx.atomAnswer a i with
    | some b => ofBool b
    | none => undecided
  | link l => match ctx.answer (.link l.name anchor i) with
    | some b => ofBool b
    | none => undecided
  | sameMessage r => anyT (ctx.peers i) fun j =>
    match ctx.step? i, ctx.step? j with
    | some s, some t => ofBool (j != i && s.message == t.message && r.test s t)
    | _, _ => broken
  | .not φ => (eval ctx anchor i φ).not
  | .and φ ψ => (eval ctx anchor i φ).and (eval ctx anchor i ψ)
  | .or φ ψ => (eval ctx anchor i φ).or (eval ctx anchor i ψ)
  | once φ => anyT (List.range i) fun j => eval ctx i j φ
  | eventually φ =>
    let found := anyT (List.range' (i + 1) (ctx.size - (i + 1))) fun j => eval ctx i j φ
    if found == broken && !ctx.complete then undecided else found
  | since φ χ => anyT (List.range i) fun j =>
    (eval ctx i j φ).and (allT ((List.range i).filter (j < ·)) fun k => (eval ctx i k χ).not)
  | before φ χ =>
    let later := List.range' (i + 1) (ctx.size - (i + 1))
    let found := anyT later fun j =>
      (eval ctx i j φ).and (allT (later.filter (· < j)) fun k => (eval ctx i k χ).not)
    if found == broken && !ctx.complete then undecided else found
  | within ms φ =>
    let later := List.range' (i + 1) (ctx.size - (i + 1))
    let found := anyT later fun j =>
      match ctx.step? i, ctx.step? j with
      | some s, some t => (eval ctx i j φ).and (ofBool (decide (t.time ≤ s.time + ms)))
      | _, _ => broken
    if found == broken && !ctx.complete then undecided else found

/-- The formula's meaning at position `i` under a reading `val` of every question. -/
def Holds (ctx : Ctx) (val : Query → Bool) (anchor i : Nat) : Formula → Prop
  | ev p => ∃ s, ctx.step? i = some s ∧ p.test s.event = true
  | atom a => (ctx.decided a i).getD (val (.atom a.name i)) = true
  | link l => val (.link l.name anchor i) = true
  | sameMessage r => ∃ j ∈ ctx.peers i, ∃ s t, ctx.step? i = some s ∧ ctx.step? j = some t ∧
      (j != i && s.message == t.message && r.test s t) = true
  | .not φ => ¬ Holds ctx val anchor i φ
  | .and φ ψ => Holds ctx val anchor i φ ∧ Holds ctx val anchor i ψ
  | .or φ ψ => Holds ctx val anchor i φ ∨ Holds ctx val anchor i ψ
  | once φ => ∃ j, j < i ∧ Holds ctx val i j φ
  | eventually φ => ∃ j, j < ctx.size ∧ i < j ∧ Holds ctx val i j φ
  | since φ χ => ∃ j, j < i ∧ Holds ctx val i j φ ∧ ∀ k, k < i → j < k → ¬ Holds ctx val i k χ
  | before φ χ => ∃ j, j < ctx.size ∧ i < j ∧ Holds ctx val i j φ ∧
      ∀ k, i < k → k < j → ¬ Holds ctx val i k χ
  | within ms φ => ∃ j, j < ctx.size ∧ i < j ∧ Holds ctx val i j φ ∧
      ∃ s t, ctx.step? i = some s ∧ ctx.step? j = some t ∧ t.time ≤ s.time + ms

/-- A reading agrees with the answers given. -/
def Agrees (ctx : Ctx) (val : Query → Bool) : Prop := ∀ q b, ctx.answer q = some b → val q = b

/-- A rule's verdict: its formula at every position, each its own anchor. -/
def evalAlways (ctx : Ctx) (φ : Formula) : Tri := allT (List.range ctx.size) fun i => eval ctx i i φ

end Rails
