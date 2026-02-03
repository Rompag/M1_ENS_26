import Mathlib.Tactic

variable (P Q R S : Prop)
open Polynomial


example (n : ℕ) (hn : n ≤ 3) : n ≤ 5 := by
  sorry

-- `⌘`

/- # exact, intro, apply, rfl-/

-- Use of the `exact` tactic

example (hP : P) : P := by
  sorry

-- Use of the `apply` tactic

example (h : P → Q) (hP : P) : Q := by
  sorry

-- `⌘`

-- Use of the `intro` tactic

example : P → P := by
  sorry

-- Use `\.` to write `·`

example : (P → Q → R) → ((P → Q) → (P → R)) := by
  sorry


-- Use of the `rfl` tactic

example : P = P := by
  sorry


example : 3 = 2 + 1 := by
  sorry

-- `⌘`

-- # `rw`

-- `P` is not a proposition: it is a True/False statement for terms in `α`.

example (α : Type) (P : α → Prop) (x y : α) (hx : P x) (h : y = x) : P y := by
  sorry



example (α : Type) (P Q : α → Prop) (x : α) (hP : P x) (h : P = Q) : Q x := by
  sorry


example (α : Type) (P Q : α → Prop) (x : α) (hP : P x) (h : P = Q) : Q x := by
  sorry

-- `⌘`

/- # Conjunction / And
  Use `\and` to write `∧` -/


example : P → Q → P ∧ Q := by
  sorry


example : P ∧ Q → P := by
  sorry

/-  # Disjunction / Or
  Use `\or` to write `∨` -/


example : P → P ∨ Q := by
  sorry

/- Symmetry of `∨`, and use of `assumption`  -/
example : P ∨ Q → Q ∨ P := by
  sorry

/- The result of `cases` can be given explicit names, by using `rcases ? with ?1 | ?h2 `-/
example : P ∨ Q → (P → R) → (Q → R) → R := by
  sorry

/- Use of the `by_cases` tactic. -/
example : R ∨ ¬ R := by
  sorry

-- `⌘`

/- # Types -/

#check 2
#check ℕ
#check (2 : ℤ)
#check 2 < 3
#check (∀ n : ℕ, ∀ x y z : ℤ, 2 < n → x ^ n + y ^ n = z ^ n → x*y*z = 0)
#check Real.sin
#check (Real.sin : ℝ → ℝ)


example : (1 : ℕ) = (1 : ℝ) := by
  sorry


example : 1 = (1 : ℚ) := by
  sorry


example : (1 : ℚ) = (1 : ℚ[X]):= by
  sorry

-- `⌘`

/- ## Prop types -/

#check 37 < 1
#check True
#check False
#check trivial
#check true
#check false
#check Bool



example : True := by
  sorry

-- `⌘`

/- # Exercises -/

-- Modus Ponens: if `P → Q` then `Q` can be deduced from `P`
-- **Exercise**
example : P → (P → Q) → Q := by
  intro h
  intro H
  apply H
  exact h

-- Transitivity of `→`
-- **Exercise**
example : (P → Q) → (Q → R) → P → R := by
  intro h1
  intro h2
  intro hP
  apply h2 (h1 hP)


-- **Exercise**
example (hP : P) : Q → (hP = hP) := by
  intro hQ
  rfl

-- **Exercise**
example (hP : P) : R → P → Q → (hP = hP) := by
  intro hR
  intro hP
  intro hQ
  rfl

-- **Exercise**
example (n : ℕ) (h : n = 5) : n = 2 + 3 := by
  rw [h]

-- **Exercise**
example (n m : ℕ) (hn : n = 5) (hm : 11 = m) : m = n + 6 := by
  rw [hn]
  rw [← hm]

-- **Exercise**
example (α : Type) (a b c : α) (H : (a = b) → P ) (h1 : c = a) (h2 : b = c) : P := by
  apply H
  rw [h2]
  rw [h1]

-- **Exercise**
example : P ∧ Q → Q := by
  intro h
  exact h.right

-- **Exercise**
example : (P → Q → R) → P ∧ Q → R := by
  intro h
  intro hP
  apply h hP.left
  exact hP.right

-- `∧` is symmetric
-- **Exercise**
example : P ∧ Q → Q ∧ P := by
  intro h
  constructor
  · exact h.right
  · exact h.left


-- `∧` is transitive
-- **Exercise**
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro h H
  constructor
  · exact h.left
  exact H.right

/- The result of `cases` can be given explicit names, by using `rcases ? with ?1 | ?h2 `-/
example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h
  rcases h with hP | hQ
  · intro h2
    intro h3
    apply h2 hP
  · intro h2
    intro h3
    exact h3 hQ

-- **Exercise**
example : False → P ∧ False := by
  intro h
  cases h -- nothing to prove

-- **Exercise**
example : (P ∧ Q → R) → P → Q → R := by
  sorry

-- **Exercise**
example : Q → P ∨ Q := by
  sorry

-- **Exercise**
example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  sorry


-- **Exercise**
example : (P → Q) → P ∨ R → Q ∨ R := by
  sorry
