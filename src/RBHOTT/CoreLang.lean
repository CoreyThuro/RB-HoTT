namespace RBHOTT

inductive Ty where
  | unit : Ty
  | nat  : Ty
  | arr  : Ty → Ty → Ty
  | prod : Ty → Ty → Ty
  deriving DecidableEq, Repr

open Ty

inductive Tm where
  | var  : Nat → Tm
  | unit : Tm
  | zero : Tm
  | succ : Tm → Tm
  | lam  : Ty → Tm → Tm
  | app  : Tm → Tm → Tm
  | pair : Tm → Tm → Tm
  | fst  : Tm → Tm
  | snd  : Tm → Tm
  deriving Repr, DecidableEq

open Tm
abbrev Ctx := List Ty

inductive hasType : Ctx → Tm → Ty → Prop where
  | t_var {Γ A} (i : Nat) :
      List.get? Γ i = some A → hasType Γ (var i) A
  | t_unit {Γ} :
      hasType Γ unit Ty.unit
  | t_zero {Γ} :
      hasType Γ zero Ty.nat
  | t_succ {Γ} {t} :
      hasType Γ t Ty.nat → hasType Γ (succ t) Ty.nat
  | t_lam {Γ A B t} :
      hasType (A :: Γ) t B → hasType Γ (lam A t) (arr A B)
  | t_app {Γ f a A B} :
      hasType Γ f (arr A B) → hasType Γ a A → hasType Γ (app f a) B
  | t_pair {Γ A B a b} :
      hasType Γ a A → hasType Γ b B → hasType Γ (pair a b) (prod A B)
  | t_fst {Γ A B p} :
      hasType Γ p (prod A B) → hasType Γ (fst p) A
  | t_snd {Γ A B p} :
      hasType Γ p (prod A B) → hasType Γ (snd p) B

inductive Val : Tm → Prop where
  | v_unit : Val unit
  | v_zero : Val zero
  | v_succ {t} : Val t → Val (succ t)
  | v_lam {A t} : Val (lam A t)
  | v_pair {a b} : Val a → Val b → Val (pair a b)

def lift (k : Nat) (d : Nat) : Tm → Tm
  | var i   => if i < d then var i else var (i + k)
  | unit    => unit
  | zero    => zero
  | succ t  => succ (lift k d t)
  | lam A t => lam A (lift k (d+1) t)
  | app f a => app (lift k d f) (lift k d a)
  | pair a b => pair (lift k d a) (lift k d b)
  | fst p   => fst (lift k d p)
  | snd p   => snd (lift k d p)

def subst (j : Nat) (s : Tm) : Tm → Tm
  | var i   => if i = j then s else if i > j then var (i - 1) else var i
  | unit    => unit
  | zero    => zero
  | succ t  => succ (subst j s t)
  | lam A t => lam A (subst (j+1) (lift 1 0 s) t)
  | app f a => app (subst j s f) (subst j s a)
  | pair a b => pair (subst j s a) (subst j s b)
  | fst p   => fst (subst j s p)
  | snd p   => snd (subst j s p)

inductive Step : Tm → Tm → Prop where
  | β {A t v} : Val v → Step (app (lam A t) v) (subst 0 v t)
  | ξ_app₁ {f f' a} : Step f f' → Step (app f a) (app f' a)
  | ξ_app₂ {f a a'} : Val f → Step a a' → Step (app f a) (app f a')
  | ξ_succ {t t'}   : Step t t' → Step (succ t) (succ t')
  | ξ_pair₁ {a a' b}: Step a a' → Step (pair a b) (pair a' b)
  | ξ_pair₂ {a b b'}: Val a → Step b b' → Step (pair a b) (pair a b')
  | fst_pair {a b}  : Step (fst (pair a b)) a
  | snd_pair {a b}  : Step (snd (pair a b)) b

inductive Steps : Nat → Tm → Tm → Prop where
  | refl (t) : Steps 0 t t
  | trans {k t u v} : Step t u → Steps k u v → Steps (Nat.succ k) t v

namespace Examples
open hasType Val Step Steps

def t_idsucc : Tm := app (lam Ty.nat (succ (var 0))) (succ zero)

theorem t_idsucc_closed_hasType :
  hasType [] t_idsucc Ty.nat := by
  apply hasType.t_app
  · apply hasType.t_lam
    apply hasType.t_succ
    apply hasType.t_var
    simp
  · apply hasType.t_succ
    exact hasType.t_zero

theorem eval_idsucc :
  ∃ k v, Steps k t_idsucc v ∧ Val v := by
  refine ⟨1, succ (succ zero), ?_, ?_⟩
  ·
    have v_arg : Val (succ zero) := Val.v_succ Val.v_zero
    have step1 : Step t_idsucc (succ (subst 0 (succ zero) (var 0))) := by
      exact Step.β (A:=Ty.nat) (t:=succ (var 0)) (v:=succ zero) v_arg
    have : subst 0 (succ zero) (var 0) = succ zero := by
      simp [subst]
    simpa [t_idsucc, this] using Steps.trans step1 (Steps.refl _)
  · exact Val.v_succ (Val.v_succ Val.v_zero)

end Examples

end RBHOTT
