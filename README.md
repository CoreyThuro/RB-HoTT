# RB-HOTT (workable skeleton++)

**Goal:** a resource-bounded take on HoTT with an incremental Lean 4 codebase.

## What works now
- Lean 4 package via Lake (toolchain 4.8.0).
- `RBHOTT.Res`: resource algebra `(⊕, zero, ≤)` with lemmas.
- `RBHOTT.Core`: `FeasibleNat R`, closed under addition, widening along `R ≤ S`.
- `RBHOTT.CoreLang`: small STLC with typing, values, substitution, small-step, and
  a demo theorem `eval_idsucc`.

## Build
```
lake build
lake exe rbhott
```

## Roadmap (minimal, achievable)
- [ ] Relate multistep cost `k` to a `ResCtx` time budget `R.time`.
- [ ] Add resource-typed judgments `Γ ⊢^{R,b} t : A`.
- [ ] Type safety (progress/preservation) for the resource fragment.
- [ ] Add Π/Σ/Id types with feasibility side conditions.
- [ ] Stratify universes `𝒰_R` and cumulative embeddings.
- [ ] CI: build + `lake test` once tests are added.

See `docs/SPEC.md` for details.


## New in this release
- `RBHOTT.Modal` (◻_R skeleton) with `intro`, `elim`, `widen`.
- `RBHOTT.Semantics` with a minimal Res-category and a Presheaf scaffold (`FeasibleNatPsh`).
- `RBHOTT.RType` with resource-typed judgments and a proved example bound.
- `docs/DESIGN.md` describes semantics direction and how presheaves fit the RB story.
