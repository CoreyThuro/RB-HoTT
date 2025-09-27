# RB‑HoTT — Corey Action List (Repo + Paper + Plan)

**Context:** This distills the latest repo snapshot review, the arXiv draft alignment, and Claude’s suggestions into a concrete, merge‑ready action list. Each item has (Why), (What), (Deliverable), and (Acceptance). Where useful, patches/snippets are included inline.

---

## 0) Triage / Meta
- [ ] **Pick license** (MIT or Apache‑2.0). *(Why: unblock release & CI badges.)*  
  **Deliverable:** `LICENSE` file.  
  **Acceptance:** CI runs on default branch; repo public‑ready.
- [ ] **Repo map in README** → mirror paper sections. *(Why: reviewers know where code lives.)*  
  **Deliverable:** README section mapping paper § to files.  
  **Acceptance:** Links resolve; `lake build` instructions present.

---

## 1) Resources: Give `ResCtx` a real order + monotone ⊕  
**Priority:** P0

**Why:** A `Preorder` over `ResCtx` and monotonicity lemmas make rewriting/automation possible and are prerequisites for modality semantics.

**What:**
- Add `Preorder` instance, `le_trans`, and `⊕` monotonicity in both arguments.

**Deliverable:** `src/RBHOTT/Res.lean` patch with:
```lean
structure ResCtx where
  time : Nat; memory : Nat; depth : Nat

def ResCtx.le (R S : ResCtx) : Prop :=
  R.time ≤ S.time ∧ R.memory ≤ S.memory ∧ R.depth ≤ S.depth
instance : LE ResCtx where le := ResCtx.le
instance : Preorder ResCtx where
  le := (· ≤ ·)
  le_refl := ⟨Nat.le_rfl, Nat.le_rfl, Nat.le_rfl⟩
  le_trans := by intro R S T h1 h2; exact ⟨Nat.le_trans h1.1 h2.1,
    Nat.le_trans h1.2.1 h2.2.1, Nat.le_trans h1.2.2 h2.2.2⟩

infixl:65 " ⊕ " => fun R S =>
  { time := R.time + S.time,
    memory := R.memory + S.memory,
    depth := Nat.max R.depth S.depth }

-- monotonicity lemmas
@[simp] theorem add_mono_left  {R R' S} : R ≤ R' → (R ⊕ S) ≤ (R' ⊕ S) := by
  intro h; exact ⟨Nat.add_le_add h.1 (Nat.le_rfl),
                 Nat.add_le_add h.2.1 (Nat.le_rfl),
                 by apply max_le_max; exact h.2.2; exact Nat.le_rfl⟩
@[simp] theorem add_mono_right {R S S'} : S ≤ S' → (R ⊕ S) ≤ (R ⊕ S') := by
  intro h; exact ⟨Nat.add_le_add (Nat.le_rfl) h.1,
                 Nat.add_le_add (Nat.le_rfl) h.2.1,
                 by apply max_le_max; exact Nat.le_rfl; exact h.2.2⟩
```

**Acceptance:** Builds; simp can use `Preorder`; tests in §7 pass.

---

## 2) Feasibility must reference the budget (time)  
**Priority:** P0

**Why:** Today `FeasibleNat` only proves `val ≤ bound`; it must assert the bound is **within the resource**: `bound ≤ R.time` (or directly `val ≤ R.time`). This makes “feasible” meaningful.

**What:** Strengthen certificate & add `widen`.

**Deliverable:** `src/RBHOTT/Core.lean` update:
```lean
structure FeasibleNat (R : ResCtx) where
  val   : Nat
  bound : Nat
  val_le_bound  : val ≤ bound
  bound_le_time : bound ≤ R.time

namespace FeasibleNat
  def widen {R S} (h : R ≤ S) (x : FeasibleNat R) : FeasibleNat S :=
    ⟨x.val, x.bound, x.val_le_bound, Nat.le_trans x.bound_le_time h.1⟩
end FeasibleNat
```

**Acceptance:** All existing examples compile; new tests in §7 confirm `widen` uses `R ≤ S`.

---

## 3) Small‑step + unit‑cost core (STLC)  
**Priority:** P1

**Why:** Needed to state and prove the cost‑soundness theorem that the paper claims.

**What:** New `RBHOTT/Cost.lean` with `Ty`, `Tm`, `Step`, `MultiStep`, `Value`, `subst`; later we’ll connect to RB typing.

**Deliverable:** Scaffold file with β‑step and context rules; `costOf` as a `ReflTransGen` counter. Minimal examples.

**Acceptance:** Compiles; example reduces `((λx.x) v)` in one step; unit tests in §7.

---

## 4) Add `Bool/if` with max‑bound rule  
**Priority:** P1

**Why:** Aligns with paper/Claude; exercises composition beyond pairs/app.

**What:** Extend syntax/semantics and RB typing rule: `b = b_c + max(b_t, b_f) + 1`.

**Deliverable:** `CoreLang` or `Cost.lean` extension + lemma `if_bound`.

**Acceptance:** Test: a closed conditional with equal branches synthesizes `b = b_c + b_branch + 1`; evaluation cost ≤ bound.

---

## 5) Recursion via **fuel** (prove `Depth(R)·b` as lemma)  
**Priority:** P1

**Why:** Safe, Lean‑friendly way to realize the recursion rule in the paper.

**What:** Implement a fuelled/well‑founded recursor `fixF`; prove: if each unfold costs ≤ `b` and `Depth(R)=d`, then total ≤ `d·b`.

**Deliverable:** `RBHOTT/Rec.lean` + theorem `fix_cost_mul_depth`.

**Acceptance:** Example recursive function (e.g., bounded iterate) checked against the lemma; no axioms.

---

## 6) Modality stubs + basic laws  
**Priority:** P2

**Why:** Paper lists □ monotonicity and simple left‑exact behavior; code should expose APIs/lemmas even if semantics are deferred.

**What:** New `RBHOTT/Modality.lean` with `Avail R A` skeleton and lemmas: `intro`, `widen`, product preservation.

**Deliverable:** Lemmas compile; comments point to presheaf model.

**Acceptance:** Simple examples use `widen` and product lemma.

---

## 7) Tests (doctest‑style + unit)  
**Priority:** P0

**Why:** Guardrails while we iterate.

**What:** `src/Examples/` with:
- `ResProps.lean` — tests for `Preorder`, `⊕` monotonicity.
- `FeasibleNatDemo.lean` — `widen` and simple sums gated by `bound` premises.
- `STLCDemo.lean` — β‑step and `if` example.

**Acceptance:** `lake build` runs all; CI green.

---

## 8) CI: add budget checking scaffolding  
**Priority:** P2

**Why:** Engineering story in paper—budget regressions should fail CI.

**What:** Add `RBHOTT/ProofCost.lean` (structural metrics) + `RBHOTT/Budget.lean` (persistent env ext) + `scripts/check_budgets.lean`. YAML job provided in paper.

**Deliverable:** Commands `#rb_cost`, `#rb_set_budget`, `#rb_check`; example wrapper budget.

**Acceptance:** CI job runs the script; repo contains one budgeted wrapper and passes.

---

## 9) Docs sync with arXiv draft  
**Priority:** P1

**Why:** Keep narrative and code aligned for reviewers.

**What:**
- Update `docs/` with: `COREY_BRIEF.md`, `COSTING.md`, and link to arXiv TeX.
- In paper, add **Remark (Implementing recursion safely)** and **Advanced modality rules** (already integrated in the latest TeX).

**Deliverable:** Docs present; anchors in README.

**Acceptance:** Cross‑refs resolve; paper statements correspond to code stubs.

---

## 10) Future (tracked as milestones)
- **Dependent core (Π/Σ/Id)** — compile‑only shell; proofs later.
- **Presheaf semantics** via mathlib CategoryTheory — optional dependency; start with Set‑valued presheaves and `FeasibleNat` example.
- **Universes `𝒰_R`** — design note + side‑condition predicate `complexity(R)`; implementation after dependent core.
- **Weighted ProofCost** — add `case_count` and α/β/γ/δ weights; emit JSON files under `cost/`.
- **Advanced topics** — probabilistic RB, coinductive rates, resource polymorphism.

---

## Suggested Branch Plan (3 short PRs first)
1. **feat/res‑order‑feasible** (Items 1,2,7): `Preorder`, tighten `FeasibleNat`, tests.  
2. **feat/stlc‑cost‑if** (Items 3,4,7): STLC + cost + `if` rule + tests.  
3. **feat/rec‑fuel‑lemma** (Item 5): fuelled `fix` + `Depth·b` lemma + example.  

Then: **feat/modality‑stubs** (Item 6) and **feat/budget‑ci** (Item 8).

---

## Language for PR descriptions (copy‑paste)
> This PR upgrades `ResCtx` to a `Preorder`, proves `⊕` monotonicity, and strengthens `FeasibleNat` so feasibility means `val ≤ bound ≤ R.time`. Adds doctests. No behavior changes elsewhere. Sets stage for modality semantics and CI budgets.

---

## Risks & Mitigations
- **Over‑promising on recursion:** We avoid a primitive `Depth·b` typing rule; instead we prove it from a fuelled recursor.  
- **Feasible additions:** Until we thread per‑subterm budgets, `FeasibleNat.fadd` should take a premise (`x.bound + y.bound ≤ R.time`) or operate in a larger `R'` (using `⊕` monotonicity) — call this out in docs.  
- **CI flakiness:** Keep ProofCost structural (kernel‑agnostic). Treat profiler timings as optional, non‑blocking metrics.

---

## Ownership & ETA (proposed)
- **Corey** — PR‑A (order/feasible) + tests.  
- **Mirco** — PR‑B (STLC + cost + if) + docs sync.  
- **ChatGPT assist** — PR‑C (recursion via fuel) draft + review notes.  
- **Later:** Modality stubs (Corey), Budget CI (Mirco).

---

## Appendix — Minimal test seeds
```lean
-- ResProps.lean
open RBHOTT
#eval let R := ⟨1,2,3⟩; let S := ⟨2,3,3⟩; decide (R ≤ S)

-- FeasibleNatDemo.lean
open RBHOTT
#eval let R := ⟨20,0,0⟩
      let x : FeasibleNat R := ⟨4,9, by decide, by decide⟩
      let y : FeasibleNat R := ⟨5,10,by decide, by decide⟩
      -- TODO: add fadd once premise wiring is in place
      ()
```

---

*End of action list.*

