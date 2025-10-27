# Claude Action List — RB‑HoTT Repo ↔ Article Alignment (Latest □ as Graded Comonad)

**Benchmark spec:** Latest revised article (□ is a graded *interior* operator/comonad with shift semantics).  
**Repo scanned:** RB-HoTT-main (Lean 4 skeleton with `ResCtx` and `FeasibleNat`).

---

## Objectives (What “done” looks like)
1) □ implemented as *graded comonad* (counit, comultiplication, monotonicity; no free `A → □_R A`; only cost-aware boxing).  
2) STLC with synthesized bounds (exact arithmetic for `app/pair/if`) and safe recursion via **fuel**; “depth·b” is a **lemma**.  
3) Operational cost (`t ⇓_k v`) and **cost soundness** theorem statement/proof.  
4) Presheaf semantics with **shift** interpretation `(□_R A)(S)=A(S⊕R)`; derive ε/δ.  
5) Resource‑indexed universes `𝒰_R` scaffold and feasible univalence *gated by budgets*.  
6) Infra: structural cost metrics, Budget DB, `lake exe check-budgets`, CI gate.  
7) Examples that match the paper: mathlib list wrappers and **Binary Search** running example.

---

## Immediate Priorities (Do these first)
- **P0. Modality core** — add `RBHOTT/Core/Modality.lean` with:
  - `structure Box (R : ResCtx) (A) := (val : A)`
  - `counit : Box R A → A`
  - `comult : Box (R₁ ⊕ R₂) A → Box R₁ (Box R₂ A)`
  - `weaken : R ≤ S → Box R A → Box S A`
  - `box_intro (t : A) (h : cost t ≤ R.time) : Box R A` (hook to cost infra later)
  - simp‑lemmas for ε/δ/monotonicity; **ban** any rule `A → □_R A`.
- **P1. STLC core** — add `RBHOTT/Core/STLC.lean`:
  - syntax for types/terms; judgment `Γ ⊢_{R;b} t : A` with exact rules:
    - `app`: `b = bf + ba + 1`
    - `pair`: `b = ba + bb`
    - `if`: `b = bc + max bt bf + 1`
  - small tactic or simp set for linear bound side‑conditions.
- **P2. Readme update** — document □ as interior/comonad; remove monad/closure phrasing.

---

## File Map (Paper → Repo)
| Paper Section | Repo Path | Action |
|---|---|---|
| §3 Resource algebra | `RBHOTT/Res.lean` | Ensure `⊕`, `≤`, commutative monoid laws, monotonicity lemmas. |
| §3 STLC + bounds | `RBHOTT/Core/STLC.lean` | Implement syntax + `Γ ⊢_{R;b} t : A` rules. |
| §3 Recursion (fuel) | `RBHOTT/Core/Recursion.lean` | Fueled/wf recursor; lemma `total ≤ Depth(R) * b`. |
| §3.3 Op cost | `RBHOTT/Core/OpCost.lean` | Small-step, `t ⇓_k v`; connect to soundness. |
| §4 □ comonad | `RBHOTT/Core/Modality.lean` | ε/δ/monotonicity + `box_intro` (no free intro). |
| §4 Semantics | `RBHOTT/Semantics/PresheafSet.lean` | Thin `(Res,≤)`; presheaves; **shift** for □. |
| §5 Universes | `RBHOTT/Core/Universe.lean` | `𝒰_R`, `complexity : ResCtx → Nat`, cumulativity. |
| §6 Infra (cost) | `RBHOTT/Infra/Cost.lean` | `nodes/lamDepth/apps/cases` + cost config. |
| §6 Budget DB | `RBHOTT/Infra/BudgetDB.lean` | Env extension Name↦Budget; APIs to compare. |
| §6 CI gate | `scripts/CheckBudgets.lean`, `.github/workflows/budget.yml` | `lake exe check-budgets`; fail on regressions. |
| Running example | `RBHOTT/Examples/BinarySearch.lean` | Match paper’s example + bound proof sketch. |
| mathlib wrappers | `RBHOTT/Examples/Lists.lean` | `length/append/map` + `*_bound` + budgets. |

---

## PR Plan (Sequenced)
**PR1: Core + □ + README**  
- Add `Core/Modality.lean`; polish `Res.lean`; move current `Main` to `Examples/Hello/`.  
- README section on □ = graded comonad & cost‑aware boxing.

**PR2: STLC + OpCost + Recursion (proof skeletons ok)**  
- `Core/STLC.lean`, `Core/OpCost.lean`, `Core/Recursion.lean`.  
- Two tiny tests for `app` and `if` arithmetic.

**PR3: Infra + CI + Lists**  
- `Infra/Cost.lean`, `Infra/BudgetDB.lean`, `scripts/CheckBudgets.lean`, workflow.  
- `Examples/Lists.lean` + recorded budgets + tests.

**PR4: Semantics + Universe + BinarySearch + Eval CSV**  
- `Semantics/PresheafSet.lean`, `Core/Universe.lean`, `Examples/BinarySearch.lean`.  
- Optional `bench/` harness exporting CSV for paper table.

---

## Specific Deltas for Existing Files
- **`RBHOTT/Res.lean`**: add/verify `⊕` monotonicity proofs; projection simp; helpers for `widen`.  
- **`RBHOTT/Core.lean`**: keep `FeasibleNat`; later relocate to `Core/Feasible.lean` to avoid naming collisions.  
- **`src/Main.lean`**: move under `Examples/Hello/Main.lean`; keep demo working; later print structural cost once Infra exists.  
- **`README.md`**: clarify □ semantics (interior/comonad), document `lake build`, `lake exe rbhott`, `lake exe check-budgets` (once implemented).

---

## Validation Checklist (Paper Parity)
- [ ] □ is **comonadic**, with ε/δ/monotone; **no** `A → □_R A`.  
- [ ] Boxing uses a **cost witness** (`box_intro`).  
- [ ] STLC rules: `app/pair/if` arithmetic exactly as in paper.  
- [ ] Recursion via **fuel**; `Depth(R)·b` appears only as a **lemma**.  
- [ ] Small-step op-cost + **cost soundness** present.  
- [ ] Presheaf **shift** semantics implemented; ε/δ derived.  
- [ ] `𝒰_R` scaffold + cumulativity; feasible univalence gated.  
- [ ] Infra/CI: budgets recorded; regression gate active.  
- [ ] `Lists.lean` and `BinarySearch.lean` compile and are budgeted.

---

## Open Questions / To Confirm on Next Pass
- Any lingering free rule `A → □_R A` in helpers? Must be removed.  
- Any plan to extend resources beyond `(time, mem, depth)` now? If yes, define the algebra extension points.  
- How “ultrafinitist” should `FeasibleNat` be in examples vs core? Document in README.

---

## Owner Assignments (suggested)
- **Core modality + STLC:** Corey  
- **OpCost + Recursion lemma:** Assistant/Corey pair-programming  
- **Infra + CI:** Assistant (scaffold) → Corey (tune)  
- **Examples + Docs:** Assistant drafts → Corey hardens

