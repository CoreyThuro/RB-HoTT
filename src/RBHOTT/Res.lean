namespace RBHOTT

/-- A minimal resource context with simple, additive budgets. -/
structure ResCtx where
  time   : Nat
  memory : Nat
  depth  : Nat
  deriving Repr, DecidableEq

/-- Pointwise ordering on resource contexts. -/
def ResCtx.le (R S : ResCtx) : Prop :=
  R.time ≤ S.time ∧ R.memory ≤ S.memory ∧ R.depth ≤ S.depth

instance : LE ResCtx where
  le := ResCtx.le

/-- A simple composition of resources (sequential composition).
    Time and memory add; depth takes the maximum. -/
def ResCtx.add (R S : ResCtx) : ResCtx :=
  { time := R.time + S.time
  , memory := R.memory + S.memory
  , depth := Nat.max R.depth S.depth }

infixl:65 " ⊕ " => ResCtx.add

@[simp] theorem le_refl (R : ResCtx) : R ≤ R := by
  exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

@[simp] theorem add_time   (R S : ResCtx) : (R ⊕ S).time   = R.time + S.time := rfl
@[simp] theorem add_memory (R S : ResCtx) : (R ⊕ S).memory = R.memory + S.memory := rfl
@[simp] theorem add_depth  (R S : ResCtx) : (R ⊕ S).depth  = Nat.max R.depth S.depth := rfl

end RBHOTT
