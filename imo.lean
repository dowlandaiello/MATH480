import Mathlib.Tactic

-- Solve over ℤ the functional equation f(2a) + 2f(b) = f(f(a + b))
-- No other variables are involved, so f must be of a few forms
-- f = fun x => x * c
-- f = fun x => x + c
-- Therefore f(2x) = 2x + c
-- while 2 (f x) = 2(x + c)
example (a b : ℤ) : ∃ (f : ℤ → ℤ), f (2 * a) + 2 * f b = f (f (a + b)) := by
  let c : ℤ := 1
  let f : ℤ → ℤ := fun x => (1/2) * x * c

  use f

  unfold f
  rw [← mul_assoc]
  norm_num

example (a b : ℤ) : ∃ (f : ℤ → ℤ), f (2 * a) + 2 * f b = f (f (a + b)) := ⟨((1/2) * .), by ring⟩

