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
  repeat rw [my_min_eq_min, min_assoc]

--Problem 4: this is min_add_add_right in mathlib
example : my_min a b + c = my_min (a + c) (b + c) := by
  rw [my_min_eq_min, min_add]

--Bonus problem: Show that our definition agree's with mathlib's.
example : my_min a b = min a b := congr_fun (congr_fun my_min_eq_min a) b

--Problem 5: do not use abs_neg
example (x : ℝ) : |-x| = |x| := by
  show -x ⊔ -(-x) = x ⊔ -x
  rw [neg_neg, max_comm]

--Problem 6: do not use abs_sub_abs_le_abs_sub
#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)
variable (a b : ℝ)
example : |a| - |b| ≤ |a - b| := by
  have h := abs_add' a (-b)
  rw [add_comm (-b) a, ← sub_eq_add_neg, abs_neg, add_comm] at h
  rw [tsub_le_iff_right]
  exact h

--Problem 7:
example : P ∨ Q → (P → R) → (Q → R) → R := Or.elim

variable (P Q R : Prop)

example : P ∨ Q → (P → R) → (Q → R) → R
  | Or.inl h, p_r, _ => p_r h
  | Or.inr h, _, q_r => q_r h

example : P ∨ Q → (P → R) → (Q → R) → R := fun p_or_q p_r q_r => match p_or_q with
  | Or.inl h => p_r h
  | Or.inr h => q_r h

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
   | ε, (he_zero : 0 < ε) => ⟨Nat.ceil (1 / ε) + 1, fun x (h_x : ⌈1 / ε⌉₊ + 1 ≤ x) => by
     simp
     have h0 : 0 < ⌈ε⁻¹⌉₊ := Nat.ceil_pos.mpr (inv_pos.mpr he_zero)
     have h0a : ⌈ε⁻¹⌉₊ <  ⌈ε⁻¹⌉₊ + 1 := by
       simp
     have h1 : 0 < x := by
       exact (lt_trans h0 (lt_of_lt_of_le h0a (by simp_all)))
     rw [abs_of_pos (by simp [Nat.cast_pos]; exact h1)]
     apply inv_lt_of_inv_lt₀
     exact he_zero
     simp_all
     have h2 : (↑⌈ε⁻¹⌉₊ : ℝ) < x := by
       simp [Nat.cast_lt]
       exact h_x
     have h3 : ε⁻¹ ≤ (↑⌈ε⁻¹⌉₊ : ℝ) := by
       simp [Nat.le_ceil]
     simp [lt_of_le_of_lt h3 h2]
   ⟩

--Problem 10: limit of a sum is the sum of the limits
-- Note: this can be shortened a ton with linarith, but I omitted that.
-- Same with a bunch of others.
theorem tendsTo_add {a₁ a₂ : ℕ → ℝ} {L₁ L₂ : ℝ} (h₁ : TendsTo a₁ L₁) (h₂ : TendsTo a₂ L₂) :
    TendsTo (fun n ↦ a₁ n + a₂ n) (L₁ + L₂) := fun ε hε =>
    let ⟨N₁, h_N₁⟩ := h₁ (ε / 2) (by simp [hε])
    let ⟨N₂, h_N₂⟩ := h₂ (ε / 2) (by simp [hε])

    ⟨max N₁ N₂, fun x hx => by
      let ⟨x_ge_N₁, x_ge_N₂⟩ : x ≥ N₁ ∧ x ≥ N₂ := max_le_iff.mp (by simp_all)
      let h_Nx₁ := h_N₁ x x_ge_N₁
      let h_Nx₂ := h_N₂ x x_ge_N₂
      simp_all
      let h₂ : |a₁ x + a₂ x - (L₁ + L₂)| ≤ |a₁ x - L₁| + |a₂ x - L₂| := by {
        calc
          |a₁ x + a₂ x - (L₁ + L₂)| = |(a₁ x - L₁) + (a₂ x - L₂)| := by
            rw [sub_eq_add_neg]
            simp
            -- Note: doing the rearranging is kind of annoying here
            -- seems kind of pointless to handwrite
            -- This isn't really critical to the problem, so I left it
            -- Handwrote linarith though
            ring_nf
          |(a₁ x - L₁) + (a₂ x - L₂)| ≤ |a₁ x - L₁| + |a₂ x - L₂| := by
            simp [abs_add_le]
      }
      let h₃ := add_lt_add_of_lt_of_le h_Nx₁ (LT.lt.le h_Nx₂)
      simp at h₃
      simp [lt_of_le_of_lt h₂ h₃]
    ⟩
