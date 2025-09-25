# RB-HOTT Design Notes (skeleton)

## Big picture
We model **resources** as a thin category on `ResCtx` (objects = budgets, morphisms = inclusions).
A **presheaf** over this category captures how data/proofs **restrict** when budgets shrink.

- `RBHOTT.Res` — resource algebra `(⊕, zero, ≤)`.
- `RBHOTT.Semantics` — `Hom`, `Presheaf`, and an example `FeasibleNatPsh`.
- `RBHOTT.Modal` — a lightweight `Avail R A` (◻_R A) with intro/elim and monotonicity.

## Why a presheaf?
Budget decreases correspond to *restriction maps*:
`res(h : S ≤ R) : F R → F S`.
Example: feasibility of naturals is preserved by **clamping** to `S.time`.

## Where we go next
- Replace the hand-rolled presheaf with one built from mathlib's category theory.
- Interpret the deep-embedded core (`RBHOTT.CoreLang`) into presheaves (or groupoids) to prove **soundness**.
- Extend `Avail` into a proper **graded (co)modal** operator that preserves Π/Σ/Id where expected.
