# Beginner's Guide: Items #1 & #2 Implementation

**For**: Corey (assuming minimal Lean knowledge)
**Topic**: Line-by-line explanation of ResCtx ordering and FeasibleNat budget implementation

---

## Table of Contents
1. [Item #1: ResCtx Ordering](#item-1-resctx-ordering)
2. [Item #2: FeasibleNat Budget](#item-2-feasiblenat-budget)
3. [Key Concepts Glossary](#key-concepts-glossary)

---

## Item #1: ResCtx Ordering

### Background: What Are We Building?

We want to say that one resource context is "less than or equal to" another. For example:
- `R = {time: 10, memory: 5, depth: 3}`
- `S = {time: 15, memory: 8, depth: 3}`
- Then `R ≤ S` because all of R's resources fit within S's budget

We also want to prove that the `⊕` operator (which combines resources) respects this ordering.

---

### Lines 17-18: Reflexivity (`le_refl`)

```lean
@[simp] theorem le_refl (R : ResCtx) : R ≤ R := by
  exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
```

**Line-by-line breakdown:**

**`@[simp]`**
- This is an **attribute** that tells Lean's simplifier about this theorem
- When you use the `simp` tactic, Lean will automatically apply this theorem
- Think of it like marking a function as "inline" in C++ - it's a hint for automation

**`theorem le_refl`**
- We're declaring a new theorem named `le_refl`
- Theorems in Lean are just proven statements you can reuse
- The name follows convention: "le" = less-or-equal, "refl" = reflexive

**`(R : ResCtx)`**
- This is a **parameter**: R is any resource context
- The colon means "has type" - so "R has type ResCtx"
- This makes the theorem work for **any** resource context, not just specific ones

**`: R ≤ R`**
- This is what we're **proving** - the statement of the theorem
- It says "R is less than or equal to itself"
- This is called **reflexivity**: every value is ≤ to itself

**`:= by`**
- `by` starts **tactic mode** - a way to construct proofs interactively
- Everything after `by` is instructions for building the proof
- Alternative would be **term mode** where you write the proof directly

**`exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩`**

Breaking this down further:

- **`exact`** is a tactic that says "here's the complete proof"
- **`⟨a, b, c⟩`** is syntax for creating a **tuple** or **anonymous constructor**
  - In Lean, when you have `A ∧ B ∧ C` (A and B and C), the proof is a tuple
  - Remember: `R ≤ S` means `R.time ≤ S.time ∧ R.memory ≤ S.memory ∧ R.depth ≤ S.depth`
  - So we need to prove three things, giving three proofs in a tuple

- **`Nat.le_refl`** is a theorem from Lean's standard library
  - It proves that any natural number n ≤ n (reflexivity for natural numbers)
  - Type: `∀ n : Nat, n ≤ n`

- **`_`** (underscore) tells Lean to **infer** what goes here
  - Lean figures out we mean `R.time`, `R.memory`, and `R.depth`
  - So `Nat.le_refl _` becomes `Nat.le_refl R.time` (proving R.time ≤ R.time)

**What this proves:**
```
R.time ≤ R.time     (first component)
R.memory ≤ R.memory (second component)
R.depth ≤ R.depth   (third component)
∴ R ≤ R             (therefore, R ≤ R)
```

---

### Lines 20-24: Transitivity (`le_trans`)

```lean
theorem le_trans {R S T : ResCtx} : R ≤ S → S ≤ T → R ≤ T := by
  intro h1 h2
  exact ⟨Nat.le_trans h1.1 h2.1,
         Nat.le_trans h1.2.1 h2.2.1,
         Nat.le_trans h1.2.2 h2.2.2⟩
```

**Line 20: `theorem le_trans {R S T : ResCtx}`**

- **`{R S T : ResCtx}`** - curly braces mean **implicit parameters**
  - Lean will automatically figure out what R, S, T are from context
  - You don't have to write them explicitly when using the theorem
  - Without braces would be `(R S T : ResCtx)` - **explicit parameters**

**`: R ≤ S → S ≤ T → R ≤ T`**

- This is a **function type** (functions and theorems are the same in Lean!)
- Read `→` as "implies" or "given ... then ..."
- Full reading: "Given R ≤ S, and given S ≤ T, we can prove R ≤ T"
- This is **transitivity**: if R≤S and S≤T, then we can "skip the middle" to get R≤T

**Line 21: `intro h1 h2`**

- **`intro`** is a tactic that says "assume the hypotheses"
- It takes the things before the final `→` and gives them names
- `h1` is the proof of `R ≤ S`
- `h2` is the proof of `S ≤ T`
- After this line, we can use `h1` and `h2` in our proof

**Lines 22-24: The proof construction**

```lean
exact ⟨Nat.le_trans h1.1 h2.1,
       Nat.le_trans h1.2.1 h2.2.1,
       Nat.le_trans h1.2.2 h2.2.2⟩
```

Remember: each `≤` is actually three separate inequalities (time, memory, depth).

**Understanding field accessors:**

- `h1` is a proof of `R ≤ S`, which is really a tuple `⟨time_proof, memory_proof, depth_proof⟩`
- **`.1`** means "first component" = the time proof
  - So `h1.1` is the proof that `R.time ≤ S.time`
- **`.2`** means "second component" = BUT this is still a tuple!
  - `h1.2` is `⟨memory_proof, depth_proof⟩`
- **`.2.1`** means "second component, then first part" = memory proof
  - So `h1.2.1` is the proof that `R.memory ≤ S.memory`
- **`.2.2`** means "second component, then second part" = depth proof
  - So `h1.2.2` is the proof that `R.depth ≤ S.depth`

**`Nat.le_trans`** is transitivity for natural numbers:
- Type: `∀ {n m k : Nat}, n ≤ m → m ≤ k → n ≤ k`
- It chains two inequalities together

**Breaking down each component:**

1. **Time component:** `Nat.le_trans h1.1 h2.1`
   - `h1.1` proves `R.time ≤ S.time`
   - `h2.1` proves `S.time ≤ T.time`
   - Result: proves `R.time ≤ T.time`

2. **Memory component:** `Nat.le_trans h1.2.1 h2.2.1`
   - `h1.2.1` proves `R.memory ≤ S.memory`
   - `h2.2.1` proves `S.memory ≤ T.memory`
   - Result: proves `R.memory ≤ T.memory`

3. **Depth component:** `Nat.le_trans h1.2.2 h2.2.2`
   - `h1.2.2` proves `R.depth ≤ S.depth`
   - `h2.2.2` proves `S.depth ≤ T.depth`
   - Result: proves `R.depth ≤ T.depth`

Putting these three proofs in a tuple `⟨_, _, _⟩` gives us the proof of `R ≤ T`.

---

### Lines 27-28: Trans Instance (Enabling Calc Mode)

```lean
instance : Trans (α := ResCtx) (· ≤ ·) (· ≤ ·) (· ≤ ·) where
  trans := le_trans
```

**What is this doing?**

This is creating a **typeclass instance** that tells Lean how to chain `≤` operations.

**`instance`**
- Declares a typeclass instance (teaches Lean a new capability)
- No name needed - Lean finds it automatically when needed
- Like implementing an interface in Java/C#

**`: Trans`**
- `Trans` is a typeclass for **transitive relations**
- It's what powers Lean's `calc` mode (more on this below)

**`(α := ResCtx)`**
- Named parameter saying we're talking about `ResCtx` type
- The `α` is a type variable (like generics in Java: `<T>`)

**`(· ≤ ·) (· ≤ ·) (· ≤ ·)`**
- This is specifying which operations are transitive
- The `·` is a placeholder (like `_` but for operators)
- Reading: "the relation `≤`, combined with `≤`, gives us `≤`"
- In other words: `R ≤ S` and `S ≤ T` implies `R ≤ T`

**`where trans := le_trans`**
- The `Trans` typeclass requires a field called `trans`
- We're saying "use our `le_trans` theorem for this"
- This connects our manual theorem to Lean's automation

**Why is this important?**

Without this instance, you CAN'T write:
```lean
calc R ≤ S := h1
     _ ≤ T := h2
```

With this instance, you CAN write calc-style proofs, which are much more readable!

The `calc` mode is syntactic sugar that:
1. Looks for a `Trans` instance
2. Automatically applies `le_trans` for you
3. Makes proofs look like mathematical calculations

---

### Lines 43-66: Left Monotonicity (`add_mono_left`)

This is the most complex proof. We're proving that if `R ≤ R'`, then `(R ⊕ S) ≤ (R' ⊕ S)`.

In other words: adding the same resources to both sides preserves ordering.

```lean
@[simp] theorem add_mono_left {R R' S : ResCtx} : R ≤ R' → (R ⊕ S) ≤ (R' ⊕ S) := by
  intro h
  constructor
  · exact Nat.add_le_add h.1 (Nat.le_refl S.time)
  constructor
  · exact Nat.add_le_add h.2.1 (Nat.le_refl S.memory)
  · -- Need: (R ⊕ S).depth ≤ (R' ⊕ S).depth
    -- which is: max R.depth S.depth ≤ max R'.depth S.depth
    by_cases hc : R.depth ≤ S.depth
    · -- When R.depth ≤ S.depth: max becomes S.depth on both sides
      calc (R ⊕ S).depth
          = Nat.max R.depth S.depth := rfl
        _ = S.depth := Nat.max_eq_right hc
        _ ≤ Nat.max R'.depth S.depth := Nat.le_max_right _ _
        _ = (R' ⊕ S).depth := rfl
    · -- When R.depth > S.depth: max becomes R.depth and R'.depth
      have hlt : S.depth < R.depth := Nat.not_le.mp hc
      calc (R ⊕ S).depth
          = Nat.max R.depth S.depth := rfl
        _ = R.depth := Nat.max_eq_left (Nat.le_of_lt hlt)
        _ ≤ R'.depth := h.2.2
        _ ≤ Nat.max R'.depth S.depth := Nat.le_max_left _ _
        _ = (R' ⊕ S).depth := rfl
```

**Line 43: Function signature**
- Same structure as before: if `R ≤ R'`, then we get the ordering preservation

**Line 44: `intro h`**
- Assume we have a proof `h` that `R ≤ R'`
- Goal is now to prove `(R ⊕ S) ≤ (R' ⊕ S)`

**Line 45: `constructor`**
- This is a tactic for proving conjunctions (AND statements)
- Remember: `(R ⊕ S) ≤ (R' ⊕ S)` means three things:
  1. time ≤ time
  2. memory ≤ memory
  3. depth ≤ depth
- `constructor` says "I'll prove each part separately"
- After `constructor`, you get a **subgoal** for the first part

**Line 46: Proving time inequality**

```lean
· exact Nat.add_le_add h.1 (Nat.le_refl S.time)
```

- The `·` (bullet point) indicates this is proving the first subgoal
- Need to prove: `(R ⊕ S).time ≤ (R' ⊕ S).time`
- Which expands to: `R.time + S.time ≤ R'.time + S.time`

**`Nat.add_le_add`** is a theorem:
- Type: `∀ {a b c d}, a ≤ b → c ≤ d → a + c ≤ b + d`
- It says: if you have two inequalities, you can add them

We apply it with:
- `h.1` which proves `R.time ≤ R'.time`
- `Nat.le_refl S.time` which proves `S.time ≤ S.time`
- Result: `R.time + S.time ≤ R'.time + S.time` ✓

**Line 47: `constructor`**
- First subgoal done! Now we need to prove the remaining parts (memory AND depth)
- Another `constructor` to split memory and depth

**Line 48: Proving memory inequality**

```lean
· exact Nat.add_le_add h.2.1 (Nat.le_refl S.memory)
```

- Same logic as time, but for memory
- `h.2.1` is proof that `R.memory ≤ R'.memory`
- Result: `R.memory + S.memory ≤ R'.memory + S.memory` ✓

**Lines 49-66: Proving depth inequality (THE HARD PART)**

Why is depth hard? Because of `max`!

Recall: `(R ⊕ S).depth = max R.depth S.depth`

We need to prove: `max R.depth S.depth ≤ max R'.depth S.depth`

The problem: `max` behaves differently depending on which argument is bigger!
- If `R.depth ≤ S.depth`, then `max R.depth S.depth = S.depth`
- If `R.depth > S.depth`, then `max R.depth S.depth = R.depth`

So we split into cases!

**Line 51: `by_cases hc : R.depth ≤ S.depth`**

- **`by_cases`** is a tactic for case analysis (like if/else)
- It considers both possibilities: the condition is true OR false
- `hc` is the name for the hypothesis in each case

**Lines 52-57: Case 1 - When R.depth ≤ S.depth**

```lean
· -- When R.depth ≤ S.depth: max becomes S.depth on both sides
  calc (R ⊕ S).depth
      = Nat.max R.depth S.depth := rfl
    _ = S.depth := Nat.max_eq_right hc
    _ ≤ Nat.max R'.depth S.depth := Nat.le_max_right _ _
    _ = (R' ⊕ S).depth := rfl
```

**Understanding `calc` mode:**

`calc` is a special syntax for writing step-by-step proofs. Each line is:
```
expression₁ = expression₂ := justification
```

Let's trace through:

1. **`(R ⊕ S).depth = Nat.max R.depth S.depth := rfl`**
   - By definition of `⊕`, the depth is `max R.depth S.depth`
   - `rfl` means "reflexivity" - this is true by definition

2. **`_ = S.depth := Nat.max_eq_right hc`**
   - The `_` means "the previous expression"
   - `Nat.max_eq_right` is a theorem: if `a ≤ b` then `max a b = b`
   - We use `hc` which says `R.depth ≤ S.depth`
   - So `max R.depth S.depth = S.depth`

3. **`_ ≤ Nat.max R'.depth S.depth := Nat.le_max_right _ _`**
   - `Nat.le_max_right` says: `b ≤ max a b` (the right argument is always ≤ the max)
   - So `S.depth ≤ max R'.depth S.depth`
   - Note: This is `≤` not `=`, and that's fine! Calc mode handles mixed relations

4. **`_ = (R' ⊕ S).depth := rfl`**
   - By definition, `(R' ⊕ S).depth = max R'.depth S.depth`

**Putting it together:**
```
(R ⊕ S).depth
  = max R.depth S.depth    (definition)
  = S.depth                (because R.depth ≤ S.depth)
  ≤ max R'.depth S.depth   (S.depth is ≤ the max)
  = (R' ⊕ S).depth         (definition)
```
Therefore `(R ⊕ S).depth ≤ (R' ⊕ S).depth` ✓

**Lines 58-66: Case 2 - When R.depth > S.depth**

```lean
· -- When R.depth > S.depth: max becomes R.depth and R'.depth
  have hlt : S.depth < R.depth := Nat.not_le.mp hc
  calc (R ⊕ S).depth
      = Nat.max R.depth S.depth := rfl
    _ = R.depth := Nat.max_eq_left (Nat.le_of_lt hlt)
    _ ≤ R'.depth := h.2.2
    _ ≤ Nat.max R'.depth S.depth := Nat.le_max_left _ _
    _ = (R' ⊕ S).depth := rfl
```

**Line 59: `have hlt : S.depth < R.depth := Nat.not_le.mp hc`**

- **`have`** introduces a helper lemma we'll use in the proof
- We're in the else-branch, so `hc : ¬(R.depth ≤ S.depth)` (not-less-or-equal)
- `Nat.not_le.mp` converts "not ≤" into ">"
- Result: `hlt` proves `S.depth < R.depth`

**The calc proof (similar to case 1, but different):**

1. **`(R ⊕ S).depth = Nat.max R.depth S.depth := rfl`**
   - By definition

2. **`_ = R.depth := Nat.max_eq_left (Nat.le_of_lt hlt)`**
   - `Nat.max_eq_left` says: if `b ≤ a` then `max a b = a`
   - `Nat.le_of_lt hlt` converts `S.depth < R.depth` into `S.depth ≤ R.depth`
   - So `max R.depth S.depth = R.depth`

3. **`_ ≤ R'.depth := h.2.2`**
   - **KEY STEP**: We use our hypothesis!
   - `h.2.2` is the proof that `R.depth ≤ R'.depth` (from `R ≤ R'`)

4. **`_ ≤ Nat.max R'.depth S.depth := Nat.le_max_left _ _`**
   - `Nat.le_max_left` says: `a ≤ max a b` (the left argument is always ≤ the max)

5. **`_ = (R' ⊕ S).depth := rfl`**
   - By definition

**Putting it together:**
```
(R ⊕ S).depth
  = max R.depth S.depth    (definition)
  = R.depth                (because R.depth > S.depth)
  ≤ R'.depth               (from our hypothesis h)
  ≤ max R'.depth S.depth   (R'.depth is ≤ the max)
  = (R' ⊕ S).depth         (definition)
```
Therefore `(R ⊕ S).depth ≤ (R' ⊕ S).depth` ✓

**Both cases proved!** ✓✓✓

---

### Lines 67-89: Right Monotonicity (`add_mono_right`)

```lean
@[simp] theorem add_mono_right {R S S' : ResCtx} : S ≤ S' → (R ⊕ S) ≤ (R ⊕ S') := by
  -- Similar structure to add_mono_left
```

This is **exactly the same logic** as `add_mono_left`, but:
- We're changing the **right** argument instead of the left
- Instead of `R ≤ R'`, we have `S ≤ S'`
- Instead of proving `(R ⊕ S) ≤ (R' ⊕ S)`, we prove `(R ⊕ S) ≤ (R ⊕ S')`

The structure is identical:
1. Prove time with `Nat.add_le_add`
2. Prove memory with `Nat.add_le_add`
3. Case analysis on which depth is bigger
4. Use calc mode for explicit reasoning

I won't repeat the explanation since it's the same technique!

---

## Item #2: FeasibleNat Budget

### Background: What Are We Building?

A `FeasibleNat` is a natural number that comes with a **budget proof**: we can prove it doesn't exceed the available resources.

Before our changes:
- `val ≤ bound` (value is within its bound)
- But `bound` could be anything - even larger than `R.time`!

After our changes:
- `val ≤ bound ≤ R.time` (full chain of validity)
- Now "feasible" really means "possible within the resource budget"

---

### Lines 5-10: Strengthened Structure

```lean
structure FeasibleNat (R : ResCtx) where
  val   : Nat
  bound : Nat
  val_le_bound  : val ≤ bound
  bound_le_time : bound ≤ R.time
deriving Repr, DecidableEq
```

**Line 5: `structure FeasibleNat (R : ResCtx) where`**

- **`structure`** defines a new data type (like `struct` in C or `class` in Java)
- **`FeasibleNat`** is the name of our new type
- **`(R : ResCtx)`** is a **parameter** - every FeasibleNat is associated with a resource context
- This makes `FeasibleNat` a **dependent type**: the type depends on a value (R)
- **`where`** introduces the fields

**Line 6-8: Data fields**

```lean
val   : Nat
bound : Nat
```

- These are regular fields (like member variables)
- `val` is the actual number
- `bound` is an upper limit we're tracking

**Lines 9-10: Proof fields**

```lean
val_le_bound  : val ≤ bound
bound_le_time : bound ≤ R.time
```

- These are **propositions** (statements that must be proven)
- When you create a `FeasibleNat`, you must provide proofs!
- `val_le_bound` ensures the value doesn't exceed its bound
- `bound_le_time` ensures the bound doesn't exceed the resource budget (**NEW!**)

**Think of it like:**
```rust
struct FeasibleNat<R> {
    val: Nat,
    bound: Nat,
    // These are compile-time proofs!
    val_le_bound: Proof<val <= bound>,
    bound_le_time: Proof<bound <= R.time>
}
```

**Line 10: `deriving Repr, DecidableEq`**

- **`deriving`** automatically generates code for typeclasses
- **`Repr`** gives us nice printing (like `toString()`)
- **`DecidableEq`** gives us decidable equality checking (can test `x == y` computationally)

**Why DecidableEq works with proof fields:**

You might think: "How can we check equality of proofs?"

Answer: **Proof irrelevance** - in Lean, all proofs of the same proposition are considered equal!

So checking `FeasibleNat` equality only checks:
- `val == val'` ?
- `bound == bound'` ?

The proofs (`val_le_bound`, `bound_le_time`) are automatically equal if the data matches!

---

### Lines 18-24: Addition with Budget Check

```lean
def fadd (x y : FeasibleNat R) (h_sum : x.bound + y.bound ≤ R.time) : FeasibleNat R :=
  { val := x.val + y.val
  , bound := x.bound + y.bound
  , val_le_bound := Nat.add_le_add x.val_le_bound y.val_le_bound
  , bound_le_time := h_sum }
```

**Line 18: Function signature**

```lean
def fadd (x y : FeasibleNat R) (h_sum : x.bound + y.bound ≤ R.time) : FeasibleNat R
```

- **`def`** declares a function
- **`fadd`** = "feasible addition"
- **`(x y : FeasibleNat R)`** - two feasible numbers (in the same resource context R)
- **`(h_sum : x.bound + y.bound ≤ R.time)`** - **CRUCIAL**: a proof that adding the bounds fits in the budget!
- **`: FeasibleNat R`** - returns a feasible number in the same context

**Why the extra parameter `h_sum`?**

Without strengthening, we could add any two feasible numbers. But now:
- `x.bound ≤ R.time` (x's bound fits)
- `y.bound ≤ R.time` (y's bound fits)
- But `x.bound + y.bound` might exceed `R.time`!

Example:
- `R.time = 100`
- `x.bound = 80` (fits!)
- `y.bound = 80` (fits!)
- `x.bound + y.bound = 160` (DOESN'T FIT!)

So we require the caller to prove that the sum fits!

**Lines 19-23: Building the result**

```lean
{ val := x.val + y.val
, bound := x.bound + y.bound
, val_le_bound := Nat.add_le_add x.val_le_bound y.val_le_bound
, bound_le_time := h_sum }
```

This is **structure construction syntax**: `{ field := value, ... }`

**`val := x.val + y.val`**
- The result's value is the sum of the values
- Regular arithmetic

**`bound := x.bound + y.bound`**
- The result's bound is the sum of the bounds
- Also regular arithmetic

**`val_le_bound := Nat.add_le_add x.val_le_bound y.val_le_bound`**
- Need to prove: `(x.val + y.val) ≤ (x.bound + y.bound)`
- We have: `x.val ≤ x.bound` (from `x.val_le_bound`)
- We have: `y.val ≤ y.bound` (from `y.val_le_bound`)
- `Nat.add_le_add` combines them: if `a ≤ b` and `c ≤ d` then `a + c ≤ b + d`

**`bound_le_time := h_sum`**
- Need to prove: `(x.bound + y.bound) ≤ R.time`
- We have: `h_sum` which is exactly this proof!
- Just pass it through directly

---

### Lines 37-43: Widen Function

```lean
def widen {R S : ResCtx} (h : R ≤ S) (x : FeasibleNat R) : FeasibleNat S :=
  { val := x.val
  , bound := x.bound
  , val_le_bound := x.val_le_bound
  , bound_le_time := Nat.le_trans x.bound_le_time h.1 }
```

**What is `widen` doing?**

If you have:
- A feasible number in context R (small budget)
- A proof that R ≤ S (S has more resources)

Then you can "lift" the feasible number into context S!

**Intuition:**
- If you can afford something with $100, you can afford it with $150
- If a computation fits in 10ms, it fits in 20ms
- More resources = more possibilities

**Line 37: Function signature**

```lean
def widen {R S : ResCtx} (h : R ≤ S) (x : FeasibleNat R) : FeasibleNat S
```

- **`{R S : ResCtx}`** - two resource contexts (implicit parameters)
- **`(h : R ≤ S)`** - proof that R has fewer-or-equal resources than S
- **`(x : FeasibleNat R)`** - a feasible number in the **smaller** context
- **`: FeasibleNat S`** - returns a feasible number in the **larger** context

**Lines 38-42: Building the result**

**`val := x.val`**
- The value doesn't change - same number!

**`bound := x.bound`**
- The bound doesn't change either - same limit!

**`val_le_bound := x.val_le_bound`**
- Need to prove: `val ≤ bound`
- We have: `x.val_le_bound` (from the original)
- This inequality doesn't involve resources, so it's still valid!

**`bound_le_time := Nat.le_trans x.bound_le_time h.1`**
- Need to prove: `bound ≤ S.time` (fits in the NEW resource context)
- We have: `x.bound_le_time` which proves `bound ≤ R.time`
- We have: `h.1` which proves `R.time ≤ S.time` (recall `h : R ≤ S`)
- **`Nat.le_trans`** chains them: if `a ≤ b` and `b ≤ c` then `a ≤ c`
- Result: `bound ≤ R.time ≤ S.time`, so `bound ≤ S.time` ✓

**The key insight:**
```
x.bound ≤ R.time    (from x.bound_le_time)
R.time ≤ S.time     (from h.1)
──────────────────────────────────────────
∴ x.bound ≤ S.time  (by transitivity)
```

This is why we needed the ordering on `ResCtx`! Without `R ≤ S`, we couldn't prove `widen` is safe!

---

## Key Concepts Glossary

### Lean Basics

**Tactic Mode (`by`)**
- Interactive proof construction
- Like writing step-by-step instructions
- Alternative to writing proofs directly (term mode)

**Term Mode**
- Direct proof construction
- Like writing expressions
- Example: `⟨a, b, c⟩` is term mode

**Type Signature (`: Type`)**
- The `:` means "has type"
- Like type annotations in TypeScript: `x: number`

**Implicit Parameters (`{...}`)**
- Lean figures them out automatically
- Don't need to write them when calling the function
- Contrast with explicit `(...)` parameters

**Dependent Types**
- Types that depend on values
- Example: `FeasibleNat R` - the type depends on which `R` you pick
- Allows compile-time reasoning about runtime values

**Propositions as Types**
- Statements (like `val ≤ bound`) are types
- Proofs are values of those types
- "Proving X" = "constructing a value of type X"

### Proof Techniques

**Reflexivity (`refl`, `rfl`)**
- Proves `x = x` or `x ≤ x`
- "Obvious" equalities/inequalities

**Transitivity (`trans`)**
- Chains relationships: `a R b → b R c → a R c`
- Works for `=`, `≤`, `<`, etc.

**Constructor**
- Tactic for proving `A ∧ B` (and statements)
- Splits into separate subgoals

**Intro**
- Assumes hypotheses
- Turns `A → B` goal into: assume `A`, prove `B`

**Exact**
- Provides a complete proof directly
- "Here's the answer"

**By_cases**
- Case analysis: prove for both `P` and `¬P`
- Like if/else for proofs

**Have**
- Introduces intermediate lemma
- "Let me first prove this helper fact"

**Calc Mode**
- Step-by-step calculation/proof
- Each line justified separately
- Very readable!

### Lean Features

**Attributes (`@[...]`)**
- Metadata about declarations
- `@[simp]` - use in simplifier
- Like annotations in Java

**Deriving**
- Automatically generate typeclass instances
- Saves boilerplate code

**Proof Irrelevance**
- All proofs of same statement are equal
- Allows `DecidableEq` on structures with proofs

**Typeclasses**
- Like interfaces/traits
- `Trans`, `DecidableEq`, `Repr` are typeclasses
- Enable ad-hoc polymorphism

### Mathematical Concepts

**Preorder**
- Set with reflexive and transitive ordering
- Not necessarily antisymmetric (can have `a ≤ b` and `b ≤ a` with `a ≠ b`)
- We implemented this manually!

**Monotonicity**
- Operations preserve ordering
- If `R ≤ R'` then `f(R) ≤ f(R')`
- Essential for compositional reasoning

**Field Accessors (`.1`, `.2`, `.2.1`)**
- Extract components from tuples/structures
- `.1` = first field
- `.2` = second field (which might itself be a tuple!)
- `.2.1` = second field's first component

---

## Summary: What Did We Achieve?

### Item #1: ResCtx Ordering
✅ Proved reflexivity: every resource context is ≤ itself
✅ Proved transitivity: can chain orderings
✅ Added Trans instance: enables calc mode automation
✅ Proved left monotonicity: `⊕` respects ordering on left argument
✅ Proved right monotonicity: `⊕` respects ordering on right argument

**Impact**: Can now reason about resource contexts mathematically!

### Item #2: FeasibleNat Budget
✅ Strengthened structure: bounds must fit in budget
✅ Updated addition: requires proof that sum fits
✅ Implemented widen: lift values to larger contexts using transitivity
✅ Restored DecidableEq: enables testing and comparisons

**Impact**: "Feasible" now means "provably within budget"!

### Enhanced Automation
✅ Trans instance enables calc mode
✅ @[simp] attributes enable automatic simplification
✅ DecidableEq enables runtime equality checks

### Type Safety Wins
✅ Can't create out-of-budget feasible numbers
✅ Can't add feasible numbers that exceed budget
✅ Can only widen to contexts with sufficient resources
✅ All safety checked at compile time!

---

## Next Steps

To fully understand this code:
1. **Read this guide multiple times** - it's dense!
2. **Try modifying the code** - change something and see what breaks
3. **Write small test theorems** - use the properties we proved
4. **Implement Item #7** - write test cases using these features

Remember: Understanding comes from doing! 🚀
