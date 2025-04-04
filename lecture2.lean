import Mathlib.Tactic

example (a b : ℝ) : a^2 - b^2 = (a-b)*(a+b) := by
  rw [mul_add]
  repeat rw [sub_eq_add_neg]
  repeat rw [right_distrib]
  rw [← add_assoc]
  repeat rw [pow_two]
  repeat rw [neg_mul]
  rw [mul_comm b a]
  simp

example (x : ℝ) (n : ℕ) : x^(n + 1) = x*x^n := by
  induction n with
  | zero =>
    rw [add_comm 0 1]
    rw [add_zero]
    rw [pow_zero]
    rw [pow_one]
    rw [mul_one]
  | succ x2  =>
  rw [pow_add]
  rw [pow_one]
  sorry

example (a b : ℝ) : a^2 - b^2 = (a-b)*(a+b) := by
  repeat rw [left_distrib]
  repeat rw [sub_eq_add_neg]
  repeat rw [right_distrib]
  rw [← add_assoc]
  repeat rw [pow_two]
  repeat rw [neg_mul]
  rw [mul_comm b a]
  simp

variable (P Q R : Prop)

example (hQ : Q) : P → Q := by
  intro h
  apply hQ

example (h : P→ Q) (hP : P) : Q := by
  apply (h hP)

example : P → P := by
  intro a
  exact a

example : P → Q → P := by
  intro a b
  apply a

example : P → (P → Q) → Q := by
  intro hP hpQ
  apply hpQ at hP
  exact hP

example : (P → Q) → (Q → R) → P → R := by
  intro a b c
  apply a at c
  apply b at c
  exact c

example : (P → Q) → (¬Q → ¬P) := flip Function.comp

example : (P → Q) → (¬Q → ¬P) := fun a a1 => a1 ∘ a

example : (P → Q) → (¬Q → ¬P) := fun a a1 a2 => a1 (a a2)
