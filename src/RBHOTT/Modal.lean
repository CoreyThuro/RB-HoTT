import RBHOTT.Res
namespace RBHOTT

/-- A lightweight "availability" modality at resource `R`.
    This is a *skeleton*: we model ◻_R A as just `A` with an explicit wrapper,
    plus monotonicity along `R ≤ S`. Later, add invariants or graded laws. -/
structure Avail (R : ResCtx) (A : Type u) where
  val : A
deriving Repr

namespace Avail

variable {A : Type u} {R S : ResCtx}

/-- Eliminate ◻_R: from availability we can use the value. -/
def elim (x : Avail R A) : A := x.val

/-- Introduce ◻_R: pack a value as available under `R`. -/
def intro (a : A) : Avail R A := { val := a }

/-- Monotonicity along `R ≤ S`: availability at `R` implies availability at any *larger* budget `S`. -/
def widen (h : R ≤ S) (x : Avail R A) : Avail S A :=
  { val := x.val }

end Avail

end RBHOTT
