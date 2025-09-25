# Attaching Costs to Proofs (RB-HOTT + mathlib)

This repo includes a **standard, kernel-agnostic** way to attach *structural costs* to proofs.

## What is measured
We compute a deterministic, structural metric on the proof term:
- `size`: total number of expression nodes
- `apps`: number of applications
- `lambdas`: number of binders (lambda/forall)
- `lets`: number of `letE` nodes
- `maxDepth`: maximum nesting depth

See: `RBHOTT.ProofCost`.

## Commands
- `#rb_cost Foo` — print cost metrics and JSON for theorem `Foo`.
- `#rb_set_budget Foo size N` — record a budget (upper bound) for `Foo`.
- `#rb_check Foo` — verify measured size ≤ recorded budget.

Budgets are stored in a persistent env extension (`rbBudgets`), so they persist across modules.

## How to budget **mathlib** theorems
You typically don't edit mathlib. Instead:
- Create a **wrapper theorem** that simply `exact` the mathlib constant.
- Attach a budget to the *wrapper*.

Example:
```lean
-- in RBHOTT/BudgetDemo.lean
theorem my_wrapper : A := by
  exact Mathlib.Some.deepTheorem

#rb_cost my_wrapper
#rb_set_budget my_wrapper size 10000
#rb_check my_wrapper
```

## CI integration
Add a job that:
1. Builds the project,
2. Executes a `.lean` script with `#rb_check` lines for declarations you care about.

If a change increases the proof term size beyond the recorded budget, the CI fails —
giving you **proof-carrying resources** for mathlib-powered developments.

## Roadmap
- Add **timing and memory** from the elaborator profiler as *separate* (non-structural) annotations.
- Emit a JSON file per declaration under `cost/` for archival.
- Provide a linter that enforces "every exported theorem has a budget."
