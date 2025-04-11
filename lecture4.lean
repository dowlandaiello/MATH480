import Mathlib.Tactic

example : ∀ x : ℝ, ∃ y, x + y = 2 := fun x => ⟨2 - x, by ring⟩

