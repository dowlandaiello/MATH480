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
  let h0 : a * (b * c) = a * b *c := Eq.symm $ mul_assoc a b c
  let h1 : a * b *c  = b * a * c := congr_fun (congr_arg HMul.hMul (mul_comm a b)) c
  let h2 : b * a * c = b * (a * c) := mul_assoc b a c
  Eq.trans (Eq.trans h0 h1) h2

example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
  Eq.trans (Eq.trans (Eq.symm $ mul_assoc a b c) (congr_fun (congr_arg HMul.hMul (mul_comm a b)) c)) $ mul_assoc b a c

-- 4
example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d :=
  -- A few facts we will use
  -- Function composition associates in useful ways:
  -- a ∘ b ∘ c = a (b ∘ (c ∘ d))
  -- We can easily prove a * d * (b * c) = a * d (e * f) using congr_arg
  let h0 : a * d * (b * c) = a * d * (e * f) := congr_arg (HMul.hMul (a * d)) h
  -- Associativity gives us (a * d) * (b * c) = a * d * (b * c)
  let h1a : a * d * (b * c) = (a * d) * (b * c) := rfl
  -- Now, we can use associativity to get a * d * e * f
  let h2a : (a * d) * (b * c) = (a * d) * b * c := Eq.symm $ mul_assoc (a * d) b c
  let h3a : (a * d) * b * c = a * d * b * c := rfl
  -- We want to get this in terms of only function compositions
  -- since function composition associates literally however
  let fD := fun x => x * d
  let fB := fun x => x * b
  let fC := fun x => x * c
  let h3a : a * d * b * c = fC (fB (fD a)) := rfl
  let h4a : a * d * b * c = (fC ∘ fB ∘ fD) a := rfl
  let h5a : (fC ∘ fB ∘ fD) a = ((fC ∘ fB) ∘ fD) a := rfl
  let hbruha : fC ∘ fB = fun x => (x * b) * c := rfl
  let hbruha : (fun x => (x * b) * c) = (fun x => c * (x * b)) := funext (fun x => sorry)
  let h6a : ((fC ∘ fB) ∘ fD) a = ((fB ∘ fC) ∘ fD) a := congr_fun (congr_fun (sorry) fD) a
  sorry

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
