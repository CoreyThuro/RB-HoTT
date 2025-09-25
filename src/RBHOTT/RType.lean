import RBHOTT.Res
import RBHOTT.CoreLang

namespace RBHOTT
open CoreLang

/-- Resource-typed judgments with a synthesized **bound** `b` on small-step cost. -/
inductive hasRType : Ctx → ResCtx → Tm → Ty → Nat → Prop where
  | r_var {Γ R A} (i : Nat) :
      List.get? Γ i = some A →
      hasRType Γ R (Tm.var i) A 0
  | r_unit {Γ R} :
      hasRType Γ R Tm.unit Ty.unit 0
  | r_zero {Γ R} :
      hasRType Γ R Tm.zero Ty.nat 0
  | r_succ {Γ R t b} :
      hasRType Γ R t Ty.nat b →
      hasRType Γ R (Tm.succ t) Ty.nat b
  | r_lam {Γ R A B t b} :
      hasRType (A :: Γ) R t B b →
      hasRType Γ R (Tm.lam A t) (Ty.arr A B) b
  | r_app {Γ R f a A B bf ba} :
      hasRType Γ R f (Ty.arr A B) bf →
      hasRType Γ R a A ba →
      hasRType Γ R (Tm.app f a) B (bf + ba + 1)
  | r_pair {Γ R A B a b ba bb} :
      hasRType Γ R a A ba →
      hasRType Γ R b B bb →
      hasRType Γ R (Tm.pair a b) (Ty.prod A B) (ba + bb)
  | r_fst {Γ R A B p bp} :
      hasRType Γ R p (Ty.prod A B) bp →
      hasRType Γ R (Tm.fst p) A bp
  | r_snd {Γ R A B p bp} :
      hasRType Γ R p (Ty.prod A B) bp →
      hasRType Γ R (Tm.snd p) B bp

namespace hasRType

open hasRType CoreLang

/-- Bound for the concrete example `t_idsucc` is 1. -/
theorem idsucc_bound (Γ := ([] : Ctx)) (R : ResCtx) :
  hasRType Γ R Examples.t_idsucc Ty.nat 1 := by
  -- t_idsucc = (λx:Nat. succ x) (succ zero)
  -- bound = bf + ba + 1 where:
  -- bf = bound of λx. succ x  = bound of (succ (var 0)) under (Nat :: Γ) = 0
  -- ba = bound of (succ zero) = 0
  -- total = 1
  have bf : hasRType [Ty.nat] R (Tm.succ (Tm.var 0)) Ty.nat 0 := by
    apply r_succ
    apply r_var (i:=0)
    simp
  have f : hasRType [] R (Tm.lam Ty.nat (Tm.succ (Tm.var 0))) (Ty.arr Ty.nat Ty.nat) 0 := by
    apply r_lam
    simpa using bf
  have a : hasRType [] R (Tm.succ Tm.zero) Ty.nat 0 := by
    apply r_succ
    exact r_zero
  simpa [Examples.t_idsucc] using r_app (f:=Tm.lam _ _) (a:=Tm.succ Tm.zero) (A:=Ty.nat) (B:=Ty.nat) f a

/-- Soundness-on-example: the 1-step evaluation lemma agrees with the synthesized bound. -/
theorem idsucc_sound (R : ResCtx) :
  ∃ v, CoreLang.Steps 1 Examples.t_idsucc v ∧ CoreLang.Val v := by
  -- This is exactly `eval_idsucc` from `CoreLang.Examples`.
  simpa using Examples.eval_idsucc

end hasRType
end RBHOTT
