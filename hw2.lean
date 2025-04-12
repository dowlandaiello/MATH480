--Math 480, Spring 2025, Jarod Alper
--Homework 2: Fill in the sorries below
import Mathlib.Tactic
open Real

--Problem 1
example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by positivity
  apply log_le_log h₀
  simp
  exact h

-- Alternative solution
example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < exp a := Real.exp_pos a
  have h₁ : 0 < 1 + exp a := lt_add_of_lt_of_nonneg zero_lt_one (LT.lt.le h₀)
  apply log_le_log h₁
  simp
  exact h

--Problem 2:
/-This following definition is "min" in mathlib, but we will
give our own definition-/
def my_min (a b : ℕ) : ℕ :=
  if a < b then a else b

lemma my_min_eq_min : my_min = min := funext fun x => funext fun b => by
  unfold my_min
  show (if x < b then x else b) = min x b
  rw [min_def x b]
  split_ifs
  case pos => rfl
  case neg h₁ h₂ =>
    have h₃ : b < x := (not_le.mp) h₂
    have h₄ := lt_trans h₃ h₁
    exfalso
    exact (lt_self_iff_false b).mp h₄
  case pos h₁ h₂=>
    have h₃ : b ≤ x := (not_lt.mp) h₁
    have h₄ := le_antisymm h₂ h₃
    exact (Eq.symm h₄)
  case neg =>
    rfl

example : my_min a b = my_min b a := by
  rw [my_min_eq_min]
  rw [min_comm]

example : my_min a b = my_min b a := by
  unfold my_min

  split_ifs
  case pos h h₂ =>
    exfalso
    apply lt_trans h₂ at h
    exact (lt_self_iff_false b).mp h
  case neg h =>
    rfl
  case pos h =>
    rfl
  case neg h h₂ =>
    have ha : ¬a < b ↔ b ≤ a := not_lt
    have hb : ¬b < a ↔ a ≤ b := not_lt

    have hc := ha.mp h
    have hd := hb.mp h₂

    exact (le_antisymm hc hd)

--Problem 3: this is min_assoc in mathlib
example : my_min (my_min a b) c = my_min a (my_min b c) := by
  repeat rw [my_min_eq_min]
  rw [min_assoc]

--Problem 4: this is min_add_add_right in mathlib
example : my_min a b + c = my_min (a + c) (b + c) := by
  rw [my_min_eq_min]
  rw [min_add]

--Bonus problem: Show that our definition agree's with mathlib's.
example : my_min a b = min a b := congr_fun (congr_fun my_min_eq_min a) b

--Problem 5: do not use abs_neg
example (x : ℝ) : |-x| = |x| := by
  show -x ⊔ -(-x) = x ⊔ -x
  rw [neg_neg]
  rw [max_comm]

--Problem 6: do not use abs_sub_abs_le_abs_sub
#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)
variable (a b : ℝ)
example : |a| - |b| ≤ |a - b| := by
  have h := abs_add' a (-b)
  rw [add_comm (-b) a] at h
  rw [← sub_eq_add_neg] at h
  rw [abs_neg] at h

  have h₁ : |a| - |b| ≤ |a - b| := by
    linarith

  apply h₁


--Problem 7:
example : P ∨ Q → (P → R) → (Q → R) → R := Or.elim

--Problem 8: the limit of the 0 sequence is 0

--first we need to define the limit of a sequence a : ℕ → ℝ
def TendsTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n, n ≥ N → |a n - L| < ε
example : TendsTo (fun n ↦ 0) 0
  | e, he_zero => ⟨0, by
    simp
    apply he_zero
  ⟩

--Problem 9: the limit of 1/n is 0
 example : TendsTo (fun n ↦ 1/n) 0
   | ε, (he_zero : 0 < ε) => ⟨Nat.ceil ε, fun x (h_x : ⌈ε⌉₊ ≤ x) => by
     simp
     have h : |(↑x)⁻¹| < ε := (abs_lt).mpr (by
       have h : ((↑x : ℝ))⁻¹ ≤ 1 := Nat.cast_inv_le_one x
       have h₂ : 0 ≤ ((↑x : ℝ))⁻¹ := by
         simp at h
         simp
       have h₃ : -ε < 0 := by
         simp [he_zero]
       have h₄ : -ε < ((↑x : ℝ))⁻¹ := by
         simp [lt_of_lt_of_le h₃ h₂]
       constructor
       exact h₄
       have h₆ : ⌈ε⌉₊ > 0 := by
         simp
         exact he_zero
       have hbruh : 0 < x := by
         simp [lt_of_lt_of_le h₆ h_x]
       have hbruh' : 0 < ((↑x)⁻¹ : ℝ) := by
         simp_all
       have h₇ : ε ≤ ⌈ε⌉₊ := by
         simp [Nat.le_ceil]
       have h₉ : ε ≤ x := le_trans h₇ (by simp_all [h₇, h_x])
       have h11 := (neg_lt.mpr h₄)
       have h12 : -((↑x : ℝ))⁻¹ ≤ 0 := by
         simp
       have h12 : ((↑x)⁻¹)⁻¹ < ε⁻¹ ↔ ε < (↑x)⁻¹ := inv_lt_inv₀ (hbruh') he_zero
     )
     simp_all [Nat.ceil_le]
   ⟩

--Problem 10: limit of a sum is the sum of the limits
theorem tendsTo_add {a₁ a₂ : ℕ → ℝ} {L₁ L₂ : ℝ} (h₁ : TendsTo a₁ L₁) (h₂ : TendsTo a₂ L₂) :
    TendsTo (fun n ↦ a₁ n + a₂ n) (L₁ + L₂) := by
  sorry
