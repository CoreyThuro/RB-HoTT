import RBHOTT.Res
namespace RBHOTT

structure FeasibleNat (R : ResCtx) where
  val   : Nat
  bound : Nat
  h     : val ≤ bound
deriving Repr, DecidableEq

namespace FeasibleNat
variable {R : ResCtx}

def fadd (x y : FeasibleNat R) : FeasibleNat R :=
  { val := x.val + y.val
  , bound := x.bound + y.bound
  , h := Nat.add_le_add x.h y.h }

infixl:65 " ⊕ₙ " => fadd

@[simp] theorem val_fadd (x y : FeasibleNat R) :
  (x ⊕ₙ y).val = x.val + y.val := rfl

@[simp] theorem bound_fadd (x y : FeasibleNat R) :
  (x ⊕ₙ y).bound = x.bound + y.bound := rfl

theorem fadd_comm (x y : FeasibleNat R) :
  (x ⊕ₙ y).val = (y ⊕ₙ x).val := by
  simp [fadd, Nat.add_comm]

def widen {R S : ResCtx} (h : R ≤ S) (x : FeasibleNat R) : FeasibleNat S :=
  { val := x.val, bound := x.bound, h := x.h }

end FeasibleNat
end RBHOTT
