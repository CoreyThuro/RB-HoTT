import RBHOTT.Res
namespace RBHOTT

/-- A thin "category" on ResCtx: a morphism `R ⟶ S` is a proof that `R ≤ S`. -/
def Hom (R S : ResCtx) : Prop := R ≤ S

namespace Hom
theorem id (R : ResCtx) : Hom R R := le_refl R
theorem comp {R S T : ResCtx} (h₁ : Hom R S) (h₂ : Hom S T) : Hom R T := by
  -- Pointwise transitivity
  rcases h₁ with ⟨h1t, h1m, h1d⟩
  rcases h₂ with ⟨h2t, h2m, h2d⟩
  exact And.intro (Nat.le_trans h1t h2t) (And.intro (Nat.le_trans h1m h2m) (Nat.le_trans h1d h2d))
end Hom

/-- A tiny presheaf on the Res category.
    We keep laws as equalities of functions to stay lightweight. -/
structure Presheaf where
  obj : ResCtx → Type
  res : {R S : ResCtx} → Hom S R → obj R → obj S
  id  : ∀ R, res (R:=R) (S:=R) (Hom.id R) = (fun x => x)
  comp : ∀ {R S T} (h₁ : Hom T S) (h₂ : Hom S R),
    res (R:=R) (S:=T) (Hom.comp h₁ h₂) = (fun x => res (R:=S) (S:=T) h₁ (res (R:=R) (S:=S) h₂ x))

/-- Example presheaf: feasible naturals bounded by time. 
    At budget `R`, the fiber is `{n // n ≤ R.time}`.
    Restriction along `h : Hom S R` clamps by `Nat.min` to ensure feasibility. -/
def FeasibleNatPsh : Presheaf where
  obj R := { n : Nat // n ≤ R.time }
  res {R} {S} (h : Hom S R) (x) :=
    -- Restrict by clamping to S.time
    ⟨Nat.min x.val S.time, by
      have : Nat.min x.val S.time ≤ S.time := Nat.min_le_right _ _
      exact this⟩
  id R := by
    -- res (id) = id: min n R.time = n because n ≤ R.time
    funext x
    have hx : x.val ≤ R.time := x.property
    have : Nat.min x.val R.time = x.val := Nat.min_eq_left hx
    simp [this]
  comp {R} {S} {T} h₁ h₂ := by
    -- Two clamps compose to a single clamp: min (min n T.time) S.time = min n T.time
    -- since T ≤ S ≤ R implies T.time ≤ S.time
    funext x
    simp

end RBHOTT
