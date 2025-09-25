namespace RBHOTT

structure ResCtx where
  time   : Nat
  memory : Nat
  depth  : Nat
  deriving Repr, DecidableEq

def ResCtx.le (R S : ResCtx) : Prop :=
  R.time ≤ S.time ∧ R.memory ≤ S.memory ∧ R.depth ≤ S.depth

instance : LE ResCtx where
  le := ResCtx.le

def ResCtx.add (R S : ResCtx) : ResCtx :=
  { time := R.time + S.time
  , memory := R.memory + S.memory
  , depth := Nat.max R.depth S.depth }

infixl:65 "⊕ᵣ" => ResCtx.add

@[simp] theorem le_refl (R : ResCtx) : R ≤ R := by
  simp only [LE.le, ResCtx.le]
  exact And.intro (Nat.le_refl _) (And.intro (Nat.le_refl _) (Nat.le_refl _))

@[simp] theorem add_time   (R S : ResCtx) : (R ⊕ᵣ S).time   = R.time + S.time := rfl
@[simp] theorem add_memory (R S : ResCtx) : (R ⊕ᵣ S).memory = R.memory + S.memory := rfl
@[simp] theorem add_depth  (R S : ResCtx) : (R ⊕ᵣ S).depth  = Nat.max R.depth S.depth := rfl

/-- The zero resource context. -/
def ResCtx.zero : ResCtx := { time := 0, memory := 0, depth := 0 }

theorem add_assoc (A B C : ResCtx) :
    (A ⊕ᵣ B) ⊕ᵣ C = A ⊕ᵣ (B ⊕ᵣ C) := by
  cases A; cases B; cases C
  simp [ResCtx.add, Nat.add_assoc, Nat.max_assoc]

theorem add_comm (A B : ResCtx) : A ⊕ᵣ B = B ⊕ᵣ A := by
  cases A; cases B
  simp [ResCtx.add, Nat.add_comm, Nat.max_comm]

theorem add_zero (A : ResCtx) : A ⊕ᵣ ResCtx.zero = A := by
  cases A <;> simp [ResCtx.add, ResCtx.zero, Nat.max_eq_left]

theorem zero_add (A : ResCtx) : ResCtx.zero ⊕ᵣ A = A := by
  simpa [add_comm] using add_zero A

theorem le_add_left {A B C : ResCtx} (h : A ≤ B) : A ⊕ᵣ C ≤ B ⊕ᵣ C := by
  rcases h with ⟨ht, hm, hd⟩
  constructor
  · simp [ResCtx.add]; exact Nat.add_le_add_right ht _
  constructor
  · simp [ResCtx.add]; exact Nat.add_le_add_right hm _
  · simp [ResCtx.add]; sorry -- TODO: prove max monotonicity

theorem le_add_right {A B C : ResCtx} (h : A ≤ B) : C ⊕ᵣ A ≤ C ⊕ᵣ B := by
  simpa [add_comm] using le_add_left (A:=A) (B:=B) (C:=C) h

end RBHOTT
