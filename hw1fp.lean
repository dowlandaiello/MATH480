--Math 480, Spring 2025, Jarod Alper
--Homework 1: Fill in the sorries below
import Mathlib.Tactic
--Helpful tactics: rfl, rintro, use, rw, intro, exact, apply, triv, exfalso, left, right, cases'

-- 1
example : 3 + 2 = 5 := rfl

-- 2
--Useful lemmas
#check mul_comm --a * b = b * a
#check mul_assoc --a * b * c = a * (b * c)
example (a b c : ℝ) : a * b * c = (a * b) * c := rfl

-- 3
example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
  --have h0 : a * b * c = b * a * c ↔ a * (b * c) = b * (a * c) :=
    --Eq.congr (mul_assoc a b c) (mul_assoc b a c)
  --have h1 : a * (b * c) = b * (a * c) ↔ a * b * c = b * a * c :=
    --Eq.congr (Eq.symm (mul_assoc a b c)) (Eq.symm (mul_assoc b a c))
  --have h2 : a * b * c = b * a * c ↔ a * (b * c) = b * (a * c) :=
    --Eq.congr (mul_assoc a b c) (mul_assoc b a c)
  let x := (Eq.congr (id_eq (a * b * c)) (Eq.symm (mul_assoc a b c))).mp (mul_assoc a b c)
  let y := (Eq.congr (mul_assoc a b c) (id_eq (a * b * c))).mp x
  let z := (Eq.congr (id_eq (a * (b * c))) (mul_assoc a b c)).mp y
  let bruh := (Eq.congr (id_eq (a * (b * c))) (mul_comm a (b * c))).mp z

  --let x := mp mul_comm

  --have h2 := mul_assoc a b c
  --have h3 : a * b * c = a * (b * c) ↔ a * (b * c) = a * b * c :=
    --Eq.congr (mul_assoc a b c) (Eq.symm (mul_assoc a b c))
  --have h4 : a * (b * c) = a * b * c ↔ a * (b * c) = a * c * b :=
    --Eq.congr (id_eq (a * (b * c))) (mul_comm a b c)
  sorry

-- 4
example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a b c]
  rw [h]
  rw [← mul_assoc]

-- 5
--Please do this exercise without using the ring tactic.
example (a b : ℝ) : a^3 - b^3 = (a-b)*(a^2+a*b+b^2) := by
  -- Cheeky solution
  linarith

-- More drawn out solution to #5
example (a b : ℝ) : a^3 - b^3 = (a-b)*(a^2+a*b+b^2) := by
  simp [sub_eq_add_neg]
  simp [left_distrib]
  simp [right_distrib]
  simp [pow_two]
  simp [← pow_three]
  simp [← add_assoc]
  simp [← sub_eq_add_neg]
  have h1 : b * (a * a) = a * (a * b) := by
    simp [← mul_assoc]
    conv =>
      left
      simp [mul_comm]
      simp [← mul_assoc]
      rfl
  have h2 : b * (a * b) = a * (b * b) := by
    conv =>
      right
      simp [← mul_assoc]
      simp [← mul_comm]
      rfl
  simp [h1]
  simp [h2]

example (a b : ℝ) : a^3 - b^3 = (a-b)*(a^2+a*b+b^2) := by
  simp [sub_eq_add_neg]
  simp [left_distrib]
  simp [right_distrib]
  simp [pow_two]
  simp [← pow_three]
  simp [← add_assoc]
  simp [← sub_eq_add_neg]
  have h1 : b * (a * a) = a * (a * b) := by
    simp [← mul_assoc]
    conv =>
      left
      simp [mul_comm]
      simp [← mul_assoc]
      rfl
  have h2 : b * (a * b) = a * (b * b) := by
    conv =>
      right
      simp [← mul_assoc]
      simp [← mul_comm]
      rfl
  simp [h1]
  simp [h2]

-- 6: Product of two odd numbers is odd.
example : ∀ m n : Nat, Odd m ∧ Odd n → Odd (m * n) := by
  simp [imp_and]
  apply Odd.mul

-- 7
-- Useful lemma
#check le_trans -- a ≤ b → b ≤ c → a ≤ c
--Please do not use the linarith tactic
example (x y z w: ℝ) (h1 : x ≤ y) (h2 : y ≤ z) (h3: z ≤ w) : x ≤ w := by
  calc
    x ≤ z := by {
      simp [le_trans h1 h2]
    }
    z ≤ w := by {
      simp [h3]
    }

-- 8
-- Note: This is the S combinator right here
variable (P Q R : Prop)
example : (P → Q → R) → (P → Q) → P → R := fun a b c => a c (b c)

-- 9
example : False → P := False.elim

-- 10
example : P → ¬¬P := not_not_intro

-- 11
example : P ∧ Q → Q := by
  intro a
  obtain ⟨h1, h2⟩ := a
  apply h2

-- 12
example : (P → Q → R) → P ∧ Q → R := by
  intro a b
  obtain ⟨h1, h2⟩ := b
  apply a
  apply h1
  exact h2

-- 14
example : ∀ x : ℝ, ∃ y, y + x = 2 := by
  intro x
  use 2 - x
  rw [sub_eq_add_neg]
  rw [add_assoc]
  rw [add_comm]
  rw [neg_add_cancel]
  rw [zero_add]

-- 15
example : ∃ x : ℝ, 3 * x + 7 ≠ 12 := by
  use 4
  norm_num
