--Math 480, Spring 2025, Jarod Alper
--Homework 3: Fill in the sorries below
import Mathlib.Tactic

/-
  Recall from hw2.lean that we defined the limit of a sequence of real numbers `tendsTo_add`.  We are now going to define the limit of a function f: ℝ → ℝ at a ∈ ℝ.
-/

--Defining lim_{x → a} f(x)
def limit (f : ℝ → ℝ) (a : ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (x : ℝ), |x-a| < δ → |f x - L| < ε

--Problem 1: If f(x) = 3 is the constant function, lim_{x → a} f(x) = 3
def g (x : ℝ) : ℝ := 3
example : limit g a 3
  | ε, hε => ⟨ε / 2, ⟨by simp_all, fun x h_x => by
    unfold g
    simp_all
  ⟩⟩

--Problem 2: If f(x) = x is the identity function, lim_{x → a} f(x) = 3
example : limit (fun x : ℝ => x) a a
  | ε, hε => ⟨ε / 2, ⟨by simp_all, fun x h_x => by
    simp_all
    exact lt_trans h_x (by simp_all)
  ⟩⟩
--Problem 3: lim_{x → 0} |x| = 0
example : limit (fun x : ℝ => |x|) 0 0
  | ε, hε => ⟨ε / 2, ⟨by simp_all, fun x h_x => by
    simp_all
    exact lt_trans h_x (by simp_all)
  ⟩⟩

--A function f(x) is continuous at a ∈ ℝ if lim_{x → a} f(x) = f(a)
def isContinuous (f : ℝ → ℝ) (a : ℝ) : Prop :=
  limit f a (f a)

--Problem 4: Formulate and prove that the identity function is continuous at all a
theorem id_continuous : ∀ a, isContinuous id a
  | a, ε, hε => ⟨ε / 2, ⟨by simp_all, fun x h_x => by
    simp_all
    exact lt_trans h_x (by simp_all)
  ⟩⟩

--Problem 5: Formulate and prove that the absolute value function |x| is continuous at all a
theorem abs_continuous : ∀ a, isContinuous (|.|) a
  | a, ε, hε => ⟨ε / 2, ⟨by simp_all, fun x h_x => by
    simp_all
    exact lt_trans (lt_of_le_of_lt (abs_abs_sub_abs_le x a) h_x) (by simp_all)
  ⟩⟩

--Problem 6  Prove that the step function f(x) = {-1 if x< 0, 1 if x ≥ 0} is not continuous at 0
noncomputable def step (x : ℝ) : ℝ := if x < 0 then -1 else 1
theorem notContinous : ¬(isContinuous step 0)
  | cont => by
    let ⟨δ, ⟨hδleft, hδright⟩⟩ := cont (1) (by simp_all)
    let x := hδright (-(δ / 2)) (by rw [sub_zero, abs_neg, abs_of_pos (by simp_all)]; simp_all)
    unfold step at x
    simp at x
    if h : 0 < δ then
      simp_all
      ring_nf at x
      rw [abs_neg] at x
      simp at x
    else
      contradiction

--Let's now define the derivative of a function f at a ∈ ℝ
def derivative (f : ℝ → ℝ) (a : ℝ) (D : ℝ) : Prop :=
  isContinuous (λx : ℝ => if x = a then D else (f x - f a) / (x - a)) a

--Problem 7: If f(x) = 3, then f'(a) = 0 for all a
def f₇ (x : ℝ) : ℝ := 3
example : derivative f₇ a 0
  | ε, h_ε => ⟨1, ⟨by simp, λx h_x => by
    simp_all
    split_ifs
    case pos h =>
      simp_all
    case neg h =>
      rw [abs_div]
      unfold f₇
      simp
      exact h_ε
  ⟩⟩

--Problem 8: If f(x) = x, then f'(a) = 1 for all a
-- Note, this was a typo. 0 Replaced with one here.
def f₈ (x : ℝ) : ℝ := x
example : derivative f₈ a 1
  | ε, h_ε => ⟨ε, ⟨h_ε, λx h_x => by
    simp_all
    split_ifs
    case pos h =>
      simp_all
    case neg h =>
      unfold f₈
      rw [div_self, sub_self, abs_zero]
      exact h_ε
      exact (sub_ne_zero.mpr h)
  ⟩⟩

--Bonus problem: derivative of x^2 is 2x
def square (x : ℝ) : ℝ := x^2
example : (x : ℝ) → derivative square x (2 * x)
  | x, ε, h_ε => ⟨ε, ⟨by simp_all, λx₂ h₂_x => by
    simp_all
    split_ifs
    case pos h =>
      simp_all
    case neg h =>
      unfold square
      ring_nf
      repeat rw [sub_eq_add_neg]
      rw [← add_assoc]
      repeat rw [neg_mul_eq_neg_mul]
      calc
        |x₂ ^ 2 * (x₂ + -x)⁻¹ + -x * 2 + -x ^ 2 * (x₂ + -x)⁻¹| = |x₂ ^ 2 * (x₂ + -x)⁻¹ + -x ^ 2 * (x₂ + -x)⁻¹ + -x * 2| := by
          ring_nf
        |x₂ ^ 2 * (x₂ + -x)⁻¹ + -x ^ 2 * (x₂ + -x)⁻¹ + -x * 2| = |(x₂ + -x)⁻¹ * x₂ ^ 2 + (x₂ + -x)⁻¹ * -x ^ 2 + -x * 2| := by
          ring_nf
        |(x₂ + -x)⁻¹ * x₂ ^ 2 +  (x₂ + -x)⁻¹ * -x ^ 2 + -x * 2| = |(x₂ + -x)⁻¹ * (x₂ ^ 2 + -x ^ 2) + -x * 2| := by
          ring_nf
        |(x₂ + -x)⁻¹ * (x₂ ^ 2 + -x ^ 2) + -x * 2| = |(x₂ + -x)⁻¹ * (x₂ + x) * (x₂ - x) + -x * 2| := by
          ring_nf
        |(x₂ + -x)⁻¹ * (x₂ + x) * (x₂ - x) + -x * 2| = |(x₂ - x)⁻¹ * (x₂ + x) * (x₂ - x) + -x * 2| := by
          rw [← sub_eq_add_neg]
        |(x₂ - x)⁻¹ * (x₂ + x) * (x₂ - x) + -x * 2| = |(x₂ + x) * ((x₂ - x) * (x₂ - x)⁻¹) + -x * 2| := by
          ring_nf
        |(x₂ + x) * ((x₂ - x) * (x₂ - x)⁻¹) + -x * 2| = |(x₂ + x) * 1 + -x * 2| := by
          rw [mul_inv_cancel₀ $ sub_ne_zero.mpr h]
        |(x₂ + x) * 1 + -x * 2| = |x₂ + x + -x * 2| := by
          ring_nf
        |x₂ + x + -x * 2| = |x₂ - x| := by
          ring_nf
        |x₂ - x| < ε := h₂_x
  ⟩⟩
