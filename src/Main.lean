import RBHOTT.Core
open RBHOTT

def main : IO Unit := do
  let R : ResCtx := { time := 10, memory := 2048, depth := 3 }
  let x : FeasibleNat R := { val := 2, bound := 5, h := by decide }
  let y : FeasibleNat R := { val := 3, bound := 7, h := by decide }
  let z := RBHOTT.FeasibleNat.fadd x y
  IO.println s!"R = {repr R}"
  IO.println s!"x = {repr x}, y = {repr y}"
  IO.println s!"z.val = {z.val}, z.bound = {z.bound}"
