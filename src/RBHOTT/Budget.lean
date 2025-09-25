import Lean
import RBHOTT.ProofCost
open Lean Meta Elab Command

namespace RBHOTT

/-- Store per-declaration budgets (currently just an upper bound on structural size).
    This lives in the environment so it survives across modules.
-/
structure Budget where
  size : Nat
deriving Repr, Inhabited

abbrev BudgetMap := NameMap Budget

initialize budgetsExt : SimplePersistentEnvExtension (Name × Budget) BudgetMap ←
  registerSimplePersistentEnvExtension {
    name          := `rbBudgets
    addEntryFn    := fun s (n,b) => s.insert n b
    addImportedFn := fun es => RBHOTT.mergeImportedBudgets es
  }

/-- Merge helper for imports. -/
def mergeImportedBudgets (es : Array BudgetMap) : BudgetMap :=
  es.foldl (init := {}) fun acc m =>
    m.foldl (fun acc n b => acc.insert n b) acc

/-- Set a budget for a constant name. -/
elab "#rb_set_budget" n:ident "size" s:num : command => do
  let name := n.getId
  let sz := s.getNat
  modifyEnv (budgetsExt.addEntry · (name, { size := sz }))
  logInfo m!"[RB] set budget for {name}: size ≤ {sz}"

/-- Check measured size against stored budget. -/
elab "#rb_check" n:ident : command => do
  let name := n.getId
  let env ← getEnv
  let some b := (budgetsExt.getState env).find? name
    | logError m!"No budget for {name}. Use `#rb_set_budget {n} size N`." ; return
  let ci ← getConstInfo name
  match ci.value? with
  | none => logError m!"{name} has no value (axiom/opaque)."
  | some val =>
      let c := ProofCost.countExpr val
      if c.size ≤ b.size then
        logInfo m!"[RB] OK: {name} cost size {c.size} ≤ budget {b.size}."
      else
        logError m!"[RB] FAIL: {name} cost size {c.size} exceeds budget {b.size}."

end RBHOTT
