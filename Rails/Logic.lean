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

inductive Atom where
  | authorizesPush | asksForThisChange | changesRunningState | exploratoryRequest | confirmsPlan
  | taskInProgress | inventsProgress | needsUserAction | onlyAsks | claimsCheckPasses | pushDeploys
  | checksRunningSystem | reliesOnClaim | isFix | floatingPointOverFiniteField | writesKernel
  | asksUserAndStops | nothingUnblocked | addsCaseToList | generalClaimStated | justified
  | grantCoversPush
  deriving Repr, DecidableEq

inductive Link where
  | runOfClaimedCheck | readsReliedClaim | statesFixedInvariant | sameRound | weighsAlgebraSystems
  deriving Repr, DecidableEq

private def onUser (e : Event) : Option Bool := if isUser e then none else some false
private def onReply (e : Event) : Option Bool := if isReply e then none else some false
private def onEdit (e : Event) : Option Bool := if isEdit e then none else some false

/-- An atom's answer where the event's form decides it: an atom about the user's words is false at
any other event, one about a reply false at any other, and so on. `none` leaves it to a model. -/
def Atom.decide : Atom → Event → Option Bool
  | .authorizesPush, e | .asksForThisChange, e | .exploratoryRequest, e | .confirmsPlan, e
  | .onlyAsks, e => onUser e
  | .inventsProgress, e | .needsUserAction, e | .claimsCheckPasses, e | .reliesOnClaim, e
  | .asksUserAndStops, e | .addsCaseToList, e => onReply e
  | .isFix, e | .floatingPointOverFiniteField, e | .writesKernel, e => onEdit e
  | .pushDeploys, e | .grantCoversPush, e => if isPush e then none else some false
  | .changesRunningState, e => match e with
    | .call _ _ _ => if isRequestAdd e then some false else none
    | _ => some false
  | .checksRunningSystem, e => match e with
    | .call _ _ _ => none
    | _ => some false
  | .taskInProgress, _ | .nothingUnblocked, _ | .generalClaimStated, _ | .justified, _ => none

/-- A question about the trace: an atom at a position, or a link from an anchor to a position. -/
inductive Query where
  | atom (a : Atom) (at_ : Nat)
  | link (l : Link) (anchor at_ : Nat)
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
  | ev (p : Event → Bool)
  | atom (a : Atom)
  | link (l : Link)
  | sameMessage (r : Step → Step → Bool)
  | gapAtMost (ms : Nat)
  | not (φ : Formula)
  | and (φ ψ : Formula)
  | or (φ ψ : Formula)
  | once (φ : Formula)
  | eventually (φ : Formula)
  | since (φ χ : Formula)

namespace Formula
def implies (φ ψ : Formula) : Formula := .or (.not φ) ψ
def never (φ : Formula) : Formula := .not φ
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

/-- A context answering each atom by its mechanical decider first and by `oracle` (a model's
answers) otherwise. -/
def build (steps : Array Step) (complete : Bool) (oracle : Query → Option Bool) : Ctx :=
  { steps
    complete
    answer := fun q => match q with
      | .atom a i => match steps[i]? with
        | some s => (Atom.decide a s.event).or (oracle q)
        | none => oracle q
      | .link .. => oracle q
    peers := fun i =>
      if i < steps.size then
        let a := runStart steps i
        List.range' a (runEnd steps steps.size i - a)
      else [] }
end Ctx

open Formula Tri

/-- The formula's value at position `i`, with `anchor` the position a link refers back to. -/
def eval (ctx : Ctx) (anchor i : Nat) : Formula → Tri
  | ev p => match ctx.step? i with
    | some s => ofBool (p s.event)
    | none => broken
  | atom a => match ctx.answer (.atom a i) with
    | some b => ofBool b
    | none => undecided
  | link l => match ctx.answer (.link l anchor i) with
    | some b => ofBool b
    | none => undecided
  | sameMessage r => anyT (ctx.peers i) fun j =>
    match ctx.step? i, ctx.step? j with
    | some s, some t => ofBool (j != i && s.message == t.message && r s t)
    | _, _ => broken
  | gapAtMost ms => match ctx.step? i, ctx.step? (i + 1) with
    | some s, some t => ofBool (decide (t.time ≤ s.time + ms))
    | _, _ => undecided
  | .not φ => (eval ctx anchor i φ).not
  | .and φ ψ => (eval ctx anchor i φ).and (eval ctx anchor i ψ)
  | .or φ ψ => (eval ctx anchor i φ).or (eval ctx anchor i ψ)
  | once φ => anyT (List.range i) fun j => eval ctx i j φ
  | eventually φ =>
    let found := anyT (List.range' (i + 1) (ctx.size - (i + 1))) fun j => eval ctx i j φ
    if found == broken && !ctx.complete then undecided else found
  | since φ χ => anyT (List.range i) fun j =>
    (eval ctx i j φ).and (allT ((List.range i).filter (j < ·)) fun k => (eval ctx i k χ).not)

/-- The formula's meaning at position `i` under a reading `val` of every question. -/
def Holds (ctx : Ctx) (val : Query → Bool) (anchor i : Nat) : Formula → Prop
  | ev p => ∃ s, ctx.step? i = some s ∧ p s.event = true
  | atom a => val (.atom a i) = true
  | link l => val (.link l anchor i) = true
  | sameMessage r => ∃ j ∈ ctx.peers i, ∃ s t, ctx.step? i = some s ∧ ctx.step? j = some t ∧
      (j != i && s.message == t.message && r s t) = true
  | gapAtMost ms => ∃ s t, ctx.step? i = some s ∧ ctx.step? (i + 1) = some t ∧ t.time ≤ s.time + ms
  | .not φ => ¬ Holds ctx val anchor i φ
  | .and φ ψ => Holds ctx val anchor i φ ∧ Holds ctx val anchor i ψ
  | .or φ ψ => Holds ctx val anchor i φ ∨ Holds ctx val anchor i ψ
  | once φ => ∃ j, j < i ∧ Holds ctx val i j φ
  | eventually φ => ∃ j, j < ctx.size ∧ i < j ∧ Holds ctx val i j φ
  | since φ χ => ∃ j, j < i ∧ Holds ctx val i j φ ∧ ∀ k, k < i → j < k → ¬ Holds ctx val i k χ

/-- A reading agrees with the answers given. -/
def Agrees (ctx : Ctx) (val : Query → Bool) : Prop := ∀ q b, ctx.answer q = some b → val q = b

/-- A rule's verdict: its formula at every position, each its own anchor. -/
def evalAlways (ctx : Ctx) (φ : Formula) : Tri := allT (List.range ctx.size) fun i => eval ctx i i φ

end Rails
