import RBHOTT.Res

namespace RBHOTT

/-!
# Feasibility Modality as Graded Comonad

The feasibility modality `□_R A` (read "Box R A") represents values of type `A`
that are available within resource budget `R`. This is formalized as a **graded comonad**
(interior operator) indexed by resource contexts.

## Key Properties (from paper §3.4):

1. **Counit (ε)**: `□_R A → A` - extraction/elimination
2. **Comultiplication (δ)**: `□_{R₁⊕R₂} A → □_{R₁} □_{R₂} A` - resource splitting
3. **Monotonicity**: `R ≤ S ⇒ □_R A → □_S A` - weakening to larger budget
4. **Cost-aware boxing**: Introduction requires cost witness (NO free `A → □_R A`)

## Presheaf Semantics (§4):

Under the shift model, `(□_R A)(S) := A(S⊕R)`.
The counit arises from `S ≤ S⊕R`, and comultiplication from associativity of `⊕`.

-/

/-- The feasibility modality □_R as a type wrapper.
    Values of type `Box R A` are witnesses that `A` is computable within budget `R`.

    This is a **graded comonad** (interior operator), NOT a monad. -/
structure Box (R : ResCtx) (A : Type u) where
  val : A
  deriving Repr

namespace Box

variable {R S R₁ R₂ : ResCtx} {A B : Type u}

/-! ## Comonad Structure -/

/-- **Counit (ε)**: Extract the value from the box.
    This corresponds to "using" a feasible value. -/
def counit : Box R A → A := fun b => b.val

/-- **Comultiplication (δ)**: Split resources compositionally.
    If `A` is feasible at budget `R₁⊕R₂`, then we can view it as
    "feasible at R₁" nested inside "feasible at R₂". -/
def comult : Box (R₁ ⊕ R₂) A → Box R₁ (Box R₂ A) :=
  fun b => ⟨⟨b.val⟩⟩

/-- **Monotonicity (weakening)**: Lift to larger budget.
    If `A` is feasible at `R` and `R ≤ S`, then `A` is feasible at `S`. -/
def weaken (_ : R ≤ S) : Box R A → Box S A :=
  fun b => ⟨b.val⟩

/-! ## Introduction (Cost-Aware Boxing)

The paper emphasizes (§3.4, lines 157-161):
> "Promotion is NOT unconditional. If Γ ⊢_{R;b} t:A with b ≤ Time(R),
>  we may form box_R(t) : □_R A."

For now, we admit `box_intro` as an axiom. A full implementation would:
1. Define a `cost` function on terms (see Core/OpCost.lean)
2. Require proof that `cost t ≤ R.time`
3. Only then allow boxing

-/

/-- **Cost-aware introduction**: Box a value with cost witness.

    TODO: Once we have cost infrastructure (Core/OpCost.lean), replace axiom with:
    `def box_intro (t : A) (h : cost t ≤ R.time) : Box R A := ⟨t⟩`

    For now, this is axiomatized - in practice, introduction would require
    a proof that the value was constructed within budget.
-/
axiom box_intro : A → Box R A

/-! ## Basic Properties -/

@[simp]
theorem counit_val (b : Box R A) : counit b = b.val := rfl

@[simp]
theorem weaken_val (h : R ≤ S) (b : Box R A) : (weaken h b).val = b.val := rfl

theorem weaken_refl (b : Box R A) : weaken (le_refl R) b = b := by
  cases b
  rfl

theorem weaken_trans {R S T : ResCtx} (h1 : R ≤ S) (h2 : S ≤ T) (b : Box R A) :
    weaken h2 (weaken h1 b) = weaken (le_trans h1 h2) b := by
  cases b
  rfl

theorem comult_val (b : Box (R₁ ⊕ R₂) A) :
    (comult b).val.val = b.val := rfl

/-! ## Functoriality (Map) -/

/-- Map a function over a boxed value (functorial action). -/
def map (f : A → B) : Box R A → Box R B :=
  fun b => ⟨f b.val⟩

@[simp]
theorem map_val (f : A → B) (b : Box R A) : (map f b).val = f b.val := rfl

theorem map_id : map (R := R) (id : A → A) = id := by
  funext b
  cases b
  rfl

theorem map_comp (f : A → B) (g : B → C) :
    map (R := R) (g ∘ f) = map (R := R) g ∘ map (R := R) f := by
  funext b
  cases b
  rfl

/-! ## Product Preservation (Left-Exactness) -/

/-- Box preserves products (left-exact for finite limits). -/
def box_prod : Box R A × Box R B → Box R (A × B) :=
  fun (ba, bb) => ⟨(ba.val, bb.val)⟩

def unbox_prod : Box R (A × B) → Box R A × Box R B :=
  fun b => (⟨b.val.1⟩, ⟨b.val.2⟩)

theorem box_prod_unbox_prod : box_prod ∘ unbox_prod = (id : Box R (A × B) → Box R (A × B)) := by
  funext b
  cases b
  rfl

theorem unbox_prod_box_prod : unbox_prod ∘ box_prod = (id : Box R A × Box R B → Box R A × Box R B) := by
  funext ⟨ba, bb⟩
  cases ba
  cases bb
  rfl

/-! ## Resource Composition -/

/-- Combine two boxed values with resource composition.
    If `A` is feasible at `R₁` and `B` is feasible at `R₂`,
    then `A × B` is feasible at `R₁ ⊕ R₂`. -/
def box_add : Box R₁ A → Box R₂ B → Box (R₁ ⊕ R₂) (A × B) :=
  fun ba bb => ⟨(ba.val, bb.val)⟩

@[simp]
theorem box_add_val (ba : Box R₁ A) (bb : Box R₂ B) :
    (box_add ba bb).val = (ba.val, bb.val) := rfl

end Box

end RBHOTT
