theorem test : ∀ a b c : Nat, a ≤ b → Nat.max a c ≤ Nat.max b c := by intros; simp [Nat.le_max_iff]; sorry
