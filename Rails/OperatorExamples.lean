import Rails.Rules

/-!
For each of `before` and `within`, a trace where a formula using it is kept and one where it is
broken, each a theorem: an operator whose evaluation couldn't tell the two apart fails to prove
here. On a complete trace; an incomplete one leaves a broken verdict undecided, as `eventually`
does.
-/

namespace Rails.OperatorExamples
open Rails Formula Rules

private def userP : Pred := ⟨"user", isUser, [.user "x"]⟩
private def replyP : Pred := ⟨"reply", isReply, [.reply "y"]⟩
private def callP : Pred := ⟨"call", isCall, [bash "ls"]⟩

/-- Every user message gets a reply before the next user message. -/
def replyInTurn : Formula := ev userP ⟹ before (ev replyP) (ev userP)

private def at0 (es : List Event) : Array Step :=
  (es.zipIdx.map fun (e, i) => ({ event := e, message := i, time := i * 60000 } : Step)).toArray

theorem before_kept :
    evalAlways (Ctx.build (at0 [.user "a", .reply "r", .user "b", .reply "s"]) true fun _ => none)
      replyInTurn = .kept := by decide

theorem before_broken :
    evalAlways (Ctx.build (at0 [.user "a", .user "b", .reply "s"]) true fun _ => none)
      replyInTurn = .broken := by decide

/-- On an incomplete trace, a user message with no reply yet leaves the verdict open. -/
theorem before_open :
    evalAlways (Ctx.build (at0 [.user "a"]) false fun _ => none) replyInTurn = .undecided := by
  decide

/-- Every user message gets a call within two minutes (steps are a minute apart in `at0`). -/
def callWithinTwoMinutes : Formula := ev userP ⟹ within 120000 (ev callP)

theorem within_kept :
    evalAlways (Ctx.build (at0 [.user "a", .reply "r", bash "ls"]) true fun _ => none)
      callWithinTwoMinutes = .kept := by decide

theorem within_broken :
    evalAlways (Ctx.build (at0 [.user "a", .reply "r", .reply "q", bash "ls"]) true fun _ => none)
      callWithinTwoMinutes = .broken := by decide

end Rails.OperatorExamples
