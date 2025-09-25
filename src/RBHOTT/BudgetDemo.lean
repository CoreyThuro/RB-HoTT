import RBHOTT.CoreLang
import RBHOTT.Budget
import RBHOTT.ProofCost

open RBHOTT

/-- A thin wrapper constant so we can attach budgets without touching originals. -/
theorem idsucc_exists_value_wrapper :
  ∃ k v, CoreLang.Steps k CoreLang.Examples.t_idsucc v ∧ CoreLang.Val v :=
by
  exact CoreLang.Examples.eval_idsucc

/-
Usage example (in a .lean file or via `lean --run` script):
  #rb_cost idsucc_exists_value_wrapper
  #rb_set_budget idsucc_exists_value_wrapper size 80
  #rb_check idsucc_exists_value_wrapper
-/
