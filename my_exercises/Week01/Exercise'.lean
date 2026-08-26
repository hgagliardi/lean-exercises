import Mathlib.Tactic



section BasicLogic

/-! ## Basic Logic

These exercises practice the fundamental logical reasoning tactics.
Remember:
- Use `intro` to introduce hypotheses for implications
- Use `exact` when you have exactly what you need
- Use `constructor` to split goals like `P ∧ Q` or `P ↔ Q`
-/

variable (P Q R : Prop)

-- Example: reflexivity of implication
example : P → P := by
  intro h
  exact h

-- Exercise 3: Simple implication chain
example : P → (Q → P) := by
  intro h   -- "Suppose P is true"
  intro hq  -- "Suppose Q is true"
  exact h   -- "Then P is still true (we already knew this)"

-- Exercise 4: Transitivity of implication
example : (P → Q) → (Q → R) → (P → R) := by
  intro hpq  -- "Suppose P implies Q"
  intro hqr  -- "Suppose Q implies R"
  intro hp   -- "Now suppose P is true"
  apply hqr  -- "To prove R, we use Q → R, so we need to prove Q"
  apply hpq  -- "To prove Q, we use P → Q, so we need to prove P"
  exact hp   -- "P is exactly our assumption"

-- Exercise 5: Conjunction introduction
example (hP : P) (hQ : Q) : P ∧ Q := by
  constructor  -- "To prove P ∧ Q, we need to prove both P and Q separately"
  exact hP     -- "P is true by assumption"
  exact hQ     -- "Q is true by assumption"

-- Exercise 6: Conjunction commutativity
example : P ∧ Q ↔ Q ∧ P := by
  constructor  -- "To prove ↔, we prove both directions"
  · intro h    -- "Forward direction: assume P ∧ Q"
    constructor -- "To prove Q ∧ P, prove Q and P separately"
    exact h.2  -- "Q is the second part of our assumption h : P ∧ Q"
    exact h.1  -- "P is the first part of our assumption"
  · intro h    -- "Backward direction: assume Q ∧ P"
    constructor -- "To prove P ∧ Q, prove P and Q separately"
    exact h.2  -- "P is the second part of h : Q ∧ P"
    exact h.1  -- "Q is the first part of h : Q ∧ P"

-- Exercise 7: More complex logical reasoning
example : (P → Q) ∧ (P → R) → (P → Q ∧ R) := by
  intro h   -- "Assume we have both P → Q and P → R"
  intro hp  -- "Now assume P"
  constructor -- "To prove Q ∧ R, prove Q and R separately"
  · apply h.1  -- "Q follows from P → Q (the first part of h)"
    exact hp   -- "We have P"
  · apply h.2  -- "R follows from P → R (the second part of h)"
    exact hp   -- "We have P"

end BasicLogic


section ApplyTactic

variable (P Q R S : Prop)

-- Example: basic apply usage
example (h1 : P → Q) (h2 : P) : Q := by
  apply h1  -- "To prove Q, use h1 : P → Q, so now we need to prove P"
  exact h2  -- "P is exactly h2"

-- Exercise 8: Chaining apply
example (h1 : P → Q) (h2 : Q → R) (h3 : P) : R := by
  apply h2  -- "To prove R, use h2 : Q → R, so now we need to prove Q"
  apply h1  -- "To prove Q, use h1 : P → Q, so now we need to prove P"
  exact h3  -- "P is exactly h3"

-- Exercise 9: Apply with multiple premises (from w1sheet2 style)
example (h0 : P ∧ Q ∧ R) (h : P → Q → R → S) : S := by
  apply h      -- "h expects three arguments to produce S"
  exact h0.1   -- "First argument: P (first component of h0)"
  exact h0.2.1 -- "Second argument: Q (first component of h0.2)"
  exact h0.2.2 -- "Third argument: R (second component of h0.2)"

-- Exercise 10: Mixed apply and intro
example : (P → Q) → (Q → R) → (P → R) := by
  intro hpq  -- "Assume P → Q"
  intro hqr  -- "Assume Q → R"
  intro hp   -- "Assume P"
  apply hqr  -- "Use Q → R, need to prove Q"
  apply hpq  -- "Use P → Q, need to prove P"
  exact hp   -- "We have P"

-- Hint: Chain the implications by working backwards from the goal
example (P Q R : Prop) : ((P → Q) ∧ (Q → R)) → (P → R) := by
  intro h   -- "Assume we have both P → Q and Q → R"
  intro hp  -- "Assume P"
  apply h.2 -- "To prove R, use Q → R, so we need to prove Q"
  apply h.1 -- "To prove Q, use P → Q, so we need to prove P"
  exact hp  -- "We have P as our assumption"


end ApplyTactic

section Functions

def f := fun x : ℕ ↦ fun y : ℕ ↦ x = y

-- Exercise 11: Basic function application
example : f 0 0 := by rfl

-- Exercise 12: Function reasoning
example (x : ℕ) : f 0 x → x = 0 := by
  intro h       -- "Assume f 0 x, which means 0 = x"
  rw [f] at h   -- "Unfold f in h, so h : 0 = x"
  symm at h     -- "Flip the equality: h : x = 0"
  assumption    -- "The goal x = 0 is exactly our assumption h"

-- Exercise 13: Function with inequality
example (x : ℕ) : f x 1 → x ≠ 2 := by
  intro h    -- "Assume f x 1, which means x = 1"
  rw [f] at h -- "Unfold f: h : x = 1"
  rw [h]     -- "Replace x with 1 in the goal: prove 1 ≠ 2"
  trivial    -- "1 ≠ 2 is obviously true"


-- Exercise 14: More complex function reasoning
example (x y : ℕ) : f 0 x ∧ f 0 y → x = y := by
  intro h              -- "Assume both f 0 x and f 0 y"
  obtain ⟨h1, h2⟩ := h -- "Extract: h1 : f 0 x and h2 : f 0 y"
  rw [f] at h1 h2      -- "Unfold f: h1 : 0 = x and h2 : 0 = y"
  rw [← h1, ← h2]      -- "Since both x and y equal 0, they equal each other"

end Functions
