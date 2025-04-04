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
example (a b c : â„) : a * b * c = (a * b) * c := by
  sorry

-- 3
example (a b c : â„) : a * (b * c) = b * (a * c) := by
  sorry

-- 4
example (a b c d e f : â„) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  sorry

-- 5
--Please do this exercise without using the ring tactic.
example (a b : â„) : a^3 - b^3 = (a-b)*(a^2+a*b+b^2) := by
  sorry

-- 6: Product of two odd numbers is odd.
example : âˆ€ m n : Nat, Odd m âˆ§ Odd n â†’ Odd (m * n) := by
  sorry

-- 7
-- Useful lemma
#check le_trans -- a â‰¤ b â†’ b â‰¤ c â†’ a â‰¤ c
--Please do not use the linarith tactic
example (x y z w: â„) (h1 : x â‰¤ y) (h2 : y â‰¤ z) (h3: z â‰¤ w) : x â‰¤ w := by
  sorry

-- 8
variable (P Q R : Prop)
example : (P â†’ Q â†’ R) â†’ (P â†’ Q) â†’ P â†’ R := by
  sorry

-- 9
example : False â†’ P := by
  sorry

-- 10
example : P â†’ Â¬Â¬P := by
  sorry

-- 11
example : P âˆ§ Q â†’ Q := by
  sorry

-- 12
example : (P â†’ Q â†’ R) â†’ P âˆ§ Q â†’ R := by
  sorry

-- 13
example : Â¬(P âˆ§ Q) â†” Â¬P âˆ¨ Â¬Q := by
  sorry

-- 14
example : âˆ€ x : â„, âˆƒ y, x + y = 2 := by
  sorry

-- 15
example : âˆƒ x : â„, 3 * x + 7 â‰  12 := by
  sorry
