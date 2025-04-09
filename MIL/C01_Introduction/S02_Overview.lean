import MIL.Common
import Mathlib.Tactic

open Nat

example : ∀ m n : Nat, Even n → Even (m * n) := by
  intro n m
  intro hm
  unfold Even
  cases hm with
  | intro k hk => {
    use k * n
    rw [hk]
    simp [mul_add]
    simp [mul_comm]
  }

example : ∀ m n : Nat, Even n → Even (m * n) := by
  unfold Even
  simp
  
  sorry
