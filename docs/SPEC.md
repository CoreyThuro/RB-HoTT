# RB-HOTT Core Spec (v0)

## Resource layer
- Resource contexts `R : ResCtx` with fields `(time, memory, depth) ∈ ℕ³`
- Preorder `R ≤ S` defined pointwise.
- Monoid `(ResCtx, ⊕, zero)`:
  - `⊕` adds time+memory, depth = `max`.
  - Lemmas: associativity, commutativity, identities, monotonicity.

## Feasibility layer
- `FeasibleNat R` with witness `val ≤ bound`.
- Operations preserve feasibility; `widen : R ≤ S → FeasibleNat R → FeasibleNat S`.

## Core language (Phase A: STLC)
Types: `Unit | Nat | A → B | A × B`
Terms: variables (de Bruijn), unit, zero, succ, λ, application, pairs, fst, snd.
Judgments:
  - Typing `Γ ⊢ t : A`
  - Small-step `t → t'` and multistep with **cost** `Steps k t u`.

**Guarantees (current):**
  - Type system, values, substitution defined.
  - Demo theorem: `t_idsucc` reduces in finitely many steps to a value.

## Next steps toward RB HoTT
1. Relate `k` (cost) to `R.time`; admissibility lemma `k ≤ R.time`.
2. Resource-aware typing: `Γ ⊢^{R, b} t : A` and composition of `b`.
3. Type safety with costs (progress/preservation).
4. Dependent layer: Π/Σ and Id types with feasibility side-conditions.
5. Stratified universes `𝒰_R` and cumulative embeddings for `R ≤ S`.
6. Modal/graded rules: feasibility as comonad/monad; weakening along `R ≤ S`.


## New components in this release
- `RBHOTT.Modal` — ◻_R skeleton (`Avail`) with intro/elim and monotonicity `widen`.
- `RBHOTT.Semantics` — mini Res-category + Presheaf and example `FeasibleNatPsh`.
- `RBHOTT.RType` — resource-typed judgments with **bound composition** and an example proof:
  `idsucc_bound : hasRType [] R t_idsucc Nat 1`, aligning with `eval_idsucc`.
