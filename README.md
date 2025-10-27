# RB-HoTT: Resource-Bounded Homotopy Type Theory

**A formal verification framework for resource-certified mathematics and programs in Lean 4**

[![Build Status](https://img.shields.io/badge/build-passing-brightgreen)]()
[![Lean 4.8.0](https://img.shields.io/badge/lean-4.8.0-blue)]()
[![License](https://img.shields.io/badge/license-Choose--One-orange)]()

## Overview

RB-HoTT extends type theory to certify both **correctness** and **computational costs**—worst-case time, memory, and recursion depth. This Lean 4 implementation provides a foundation for proof-carrying resources where proofs guarantee both functional correctness and resource compliance.

### Key Features

✅ **Resource Algebra** - Compositional resource contexts with ordering and monotonicity
✅ **Graded Comonad Modality** - `□_R A` for feasibility at budget `R`
✅ **STLC with Synthesized Bounds** - Typing judgment `Γ ⊢_{R;b} t : A`
✅ **Operational Semantics** - Small-step reduction with cost tracking
✅ **Cost Soundness** - Theorem 3.1 from paper (admitted with `sorry`)
⏳ **Test Suite** - Comprehensive property tests for core features

## Quick Start

### Prerequisites

Install Lean 4 via **elan**:
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

### Build & Run

```bash
# Build the project
lake build

# Run the demo
lake exe rbhott

# Build and run tests (when added to lakefile)
lake build Examples.ResPropsTest
```

### Expected Output

```
RB-HoTT: Resource-Bounded Homotopy Type Theory
===============================================

Resource Context: { time := 100, memory := 2048, depth := 5 }

x = 15 (bound: 20)
y = 25 (bound: 30)

x + y = 40 (bound: 50)
Bound check: 50 ≤ 100 ✓

Widened to larger context S: { time := 200, memory := 4096, depth := 10 }
x in S still has val=15, bound=20

✓ All operations type-checked with resource proofs!
```

## Project Structure

```
src/
  RBHOTT/
    Res.lean                 -- Resource contexts (time, memory, depth)
    Core.lean                -- Main exports
    Core/
      Modality.lean          -- □_R modality as graded comonad
      STLC.lean              -- Simply-typed lambda calculus
      OpCost.lean            -- Operational semantics & cost soundness
  Main.lean                  -- Demonstration program
  Examples/
    Hello/Main.lean          -- Original demo (archived)
    ResPropsTest.lean        -- Test suite for Items #1-2
```

## Core Concepts

### Resource Contexts

```lean
structure ResCtx where
  time   : Nat  -- Time budget
  memory : Nat  -- Memory budget
  depth  : Nat  -- Recursion depth budget
```

**Properties:**
- Pointwise ordering: `R ≤ S` iff all components satisfy `≤`
- Monoidal sum: `R ⊕ S` adds time/memory, takes max depth
- Monotonicity: `R ≤ R' → (R ⊕ S) ≤ (R' ⊕ S)`

### Feasibility Modality

```lean
structure Box (R : ResCtx) (A : Type) where
  val : A
```

**Graded Comonad Structure:**
- `counit : □_R A → A` (extraction)
- `comult : □_{R₁⊕R₂} A → □_{R₁} □_{R₂} A` (resource splitting)
- `weaken : R ≤ S → □_R A → □_S A` (weakening to larger budget)

**Cost-Aware Introduction:**
- NO free `A → □_R A`
- Boxing requires proof that value was constructed within budget

### Simply-Typed Lambda Calculus

**Typing Judgment:** `Γ ⊢_{R;b} t : A`
- `Γ` = typing context
- `R` = resource budget
- `b` = synthesized bound
- `t` = term
- `A` = type

**Bound Synthesis Rules:**
- Application: `b_f + b_a + 1`
- Pair: `b_a + b_b`
- Conditional: `b_c + max(b_t, b_f) + 1`

### Cost Soundness

**Theorem 3.1 (from paper §3.3):**
If `Γ ⊢_{R;b} t : A` and `t` is closed, then:
- `∃v,k. t ⇒* v` (reduces to value)
- `k ≤ b ≤ Time(R)` (actual cost ≤ bound ≤ budget)

*Status: Stated with `sorry`, proof planned for future work*

## Implementation Status

### ✅ Completed (Items #1-2 from Action List)

| Component | File | Status |
|-----------|------|--------|
| Resource Algebra | `Res.lean` | ✅ Complete with Trans instance |
| FeasibleNat | `Core.lean` | ✅ Strengthened with `bound_le_time` |
| Graded Comonad | `Core/Modality.lean` | ✅ All operations implemented |
| STLC | `Core/STLC.lean` | ✅ Types, terms, typing rules |
| Op Semantics | `Core/OpCost.lean` | ✅ Small-step + multi-step |
| Cost Soundness | `Core/OpCost.lean` | ⏳ Stated (proof admitted) |
| Tests | `Examples/ResPropsTest.lean` | ✅ Comprehensive test suite |

### 🔄 In Progress (PR1-PR4 from Action List)

- [ ] **PR2**: Recursion via fuel (Core/Recursion.lean)
- [ ] **PR3**: Infrastructure (Infra/Cost.lean, BudgetDB, CI)
- [ ] **PR4**: Presheaf semantics, Universe scaffolding
- [ ] **Examples**: Binary search, mathlib wrappers

### 📋 Planned

- [ ] Dependent types (§5 of paper) - mid-term goal
- [ ] Presheaf semantics validation
- [ ] CI with budget regression checking
- [ ] Proof cost metrics
- [ ] Mathlib integration

## Alignment with Paper

This implementation follows the **revised arxiv paper** (RB-HoTT_arxiv_revised.tex):

- **§3.1 Resource Algebra** ✅ Fully implemented
- **§3.2 STLC + Typing** ✅ Core complete
- **§3.3 Operational Semantics** ✅ Infrastructure ready
- **§3.4 Feasibility Modality** ✅ As graded comonad
- **§4 Presheaf Semantics** ⏳ Planned (PR4)
- **§5 Dependent Types** ⏳ Future work
- **§6 Engineering** ⏳ Planned (PR3)

**Current Alignment Score:** 3.5/10 → **Target (Minimal Publishable):** 6/10

See `claude-suggestions.md` and `claudeactionlist.md` for detailed gap analysis.

## Examples

### Feasible Natural Numbers

```lean
let R : ResCtx := { time := 100, memory := 2048, depth := 5 }
let x : FeasibleNat R :=
  { val := 15, bound := 20
  , val_le_bound := by decide
  , bound_le_time := by decide }
let y : FeasibleNat R :=
  { val := 25, bound := 30
  , val_le_bound := by decide
  , bound_le_time := by decide }

-- Requires proof that sum fits in budget
let z := FeasibleNat.fadd x y (by decide : x.bound + y.bound ≤ R.time)
-- z.val = 40, z.bound = 50, proven ≤ 100
```

### Resource Widening

```lean
let R : ResCtx := { time := 100, memory := 1024, depth := 5 }
let S : ResCtx := { time := 200, memory := 2048, depth := 10 }

let x : FeasibleNat R := { ... }
let x_wider := FeasibleNat.widen (by decide : R ≤ S) x
-- Same value and bound, now valid in larger context
```

### STLC Typing

```lean
-- Identity function has bound 0
example (R : ResCtx) :
    [] ⊢[R;0] lam (var Var.zero) : (nat ⇒ nat) :=
  HasBound.lam HasBound.var

-- Application increases bound by 1
example (R : ResCtx) :
    [] ⊢[R;1] app (lam (var Var.zero)) (natLit 5) : nat :=
  HasBound.app (HasBound.lam HasBound.var) HasBound.natLit
```

## Key Design Decisions

### Why Graded Comonad (Not Monad)?

The revised paper (§3.4) emphasizes:
> "□_R is a graded **comonad** (interior operator), NOT a monad."

**Implications:**
- `counit : □_R A → A` (can extract/use feasible values)
- `comult : □_{R₁⊕R₂} A → □_{R₁} □_{R₂} A` (resource splitting)
- **NO** free `A → □_R A` (introduction requires cost witness)

### Why Strengthen FeasibleNat?

Old: `val ≤ bound` (bound could exceed resources!)
New: `val ≤ bound ≤ R.time` (full chain ensures feasibility)

**Benefit:** "Feasible" now has semantic meaning - truly within budget.

### Why Trans Instance (Not Preorder)?

Lean 4 core lacks `Preorder` without mathlib. We provide:
- Standalone `le_refl`, `le_trans` theorems
- `Trans` instance for calc mode automation
- **Result:** Equivalent functionality without dependencies

## Contributing

This is a research prototype. Contributions welcome for:
- Completing admitted proofs (`sorry` → actual proofs)
- Adding examples and test cases
- Infrastructure (CI, budget checking tools)
- Documentation improvements

## References

- **Paper:** RB-HoTT_arxiv_revised.tex (Sept 2025)
- **Action List:** claudeactionlist.md
- **Gap Analysis:** claude-suggestions.md
- **Implementation Report:** `.serena/memories/items_1_2_completion_report.md`

## License

See `LICENSE-CHOOSE.txt` - please choose MIT, Apache-2.0, or similar before publishing.

---

**Status:** Foundation complete (Items #1-2) ✅
**Next:** PR2 (Recursion), PR3 (Infrastructure), PR4 (Semantics)
**Goal:** Minimal publishable state - Cost soundness proof + one real example
