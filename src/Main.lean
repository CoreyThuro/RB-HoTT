import RBHOTT.Res
import RBHOTT.Core
import RBHOTT.CoreLang
import RBHOTT.Modal
import RBHOTT.Semantics
import RBHOTT.RType

open RBHOTT

def main : IO Unit := do
  let R : ResCtx := { time := 10, memory := 2048, depth := 3 }
  let x : FeasibleNat R := { val := 2, bound := 5, h := by decide }
  let y : FeasibleNat R := { val := 3, bound := 7, h := by decide }
  let z := RBHOTT.FeasibleNat.fadd x y
  IO.println s!"ResCtx R = {R}"
  IO.println s!"FeasibleNat demo: x={x}, y={y} -> z.val={z.val}, z.bound={z.bound}"
  IO.println "STLC demo term t_idsucc = (λx:Nat. succ x) (succ 0)"
  IO.println "Bound synthesis: hasRType [] R t_idsucc Nat 1 (see RBHOTT.RType.idsucc_bound)"
  IO.println "Semantics scaffold: RBHOTT.Semantics.FeasibleNatPsh (presheaf over ResCtx)"
  let a := Avail.intro (A := Nat) (R := R) 42
  let a' := Avail.widen (by exact le_refl R) a
  IO.println s!"RB modality demo: Avail R Nat with value {a'.val}"


/-
RB budget instrumentation:
  #rb_cost idsucc_exists_value_wrapper
  #rb_set_budget idsucc_exists_value_wrapper size 80
  #rb_check idsucc_exists_value_wrapper
-/
