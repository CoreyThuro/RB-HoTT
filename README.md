# RB-HOTT (workable skeleton)

**Goal:** a *resource-bounded*, ultrafinitist take on Homotopy Type Theory with a concrete,
incrementally extensible Lean 4 codebase.

## What works now
- Lean 4 package via Lake (`lean-toolchain` pinned to 4.8.0).
- Core structures:
  - `ResCtx`: simple additive resource budgets with `≤` order.
  - `FeasibleNat R`: naturals with a bound witness; closed under addition.
- Executable `rbhott` that constructs a tiny example and prints it.
- `archive/` directory preserving all your original files unmodified.

## Quick start
1. Install Lean 4 via **elan** (Linux/Mac/Windows):  
   https://leanprover-community.github.io/get_started.html
2. Build:
   ```bash
   lake build
   lake exe rbhott
   ```
3. (Optional) Run the Python mock demo:
   ```bash
   python demo/feasible_demo.py
   ```

## Project layout
```
src/
  RBHOTT/
    Res.lean     -- resource context & order
    Core.lean    -- FeasibleNat and basic lemmas
  Main.lean      -- small IO demo
docs/
  INTRO.md
demo/
  feasible_demo.py
archive/
  ...            -- original materials from your ZIP
```

## Roadmap (minimal, achievable)
- [ ] Define a small-step operational semantics with a cost counter.
- [ ] Prove **type safety** (progress & preservation) in the core fragment.
- [ ] Implement **resource widening** lemmas along `R ≤ S`.
- [ ] Add graded modal rules (feasibility as a comonad/monad).
- [ ] Introduce simple path types and clarify which equalities are constructible under bounds.
- [ ] Add CI that runs `lake build` (see `.github/workflows/lean.yml`).

## License
`LICENSE-CHOOSE.txt` is a placeholder. Replace with MIT/Apache-2.0/etc. before publishing.
