--Math 480, Spring 2025, Jarod Alper
--Homework 1: Fill in the sorries below
import Mathlib.Tactic
--Helpful tactics: rfl, rintro, use, rw, intro, exact, apply, triv, exfalso, left, right, cases'

-- Little note: I solved a few of these problems in term mode for fun.

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
-- Some lemmas for solving this in term mode for fun
lemma mul_fn_comm (a b : ℝ) : ((. * a) ∘ (. * b)) = ((. * b) ∘ (. * a)) :=
  have h0a : ((. * a) ∘ (. * b)) = (. * b * a) := rfl
  have h0b : ((. * b) ∘ (. * a)) = (. * a * b) := rfl
  have h1 : (. * a * b) = (fun x => b * (x * a)) := funext (fun x => Eq.symm $ mul_comm b (x * a))
  have h2 : (fun x => b * (x * a)) = (b * . * a) := funext (fun x => Eq.symm $ mul_assoc b x a)
  have h3 : (b * . * a) = (b * . * a) := rfl
  have h4 : (b * . * a) = (. * b * a) := funext (fun x => congr_arg (. * a) $ (mul_comm b x))

  let x : ((. * b) ∘ (. * a)) = (. * b * a) := Eq.trans (Eq.trans (Eq.trans (Eq.trans h0b h1) h2) h3) h4
  Eq.trans h0a (Eq.symm x)

lemma mul_assoc_4 (a b c d : ℝ) : a * d * (b * c) = a * b * c * d :=
  let h2a : (a * d) * (b * c) = (a * d) * b * c := Eq.symm $ mul_assoc (a * d) b c
  let h25a : (a * d) * b * c = a * d * b * c := rfl
  let fD := (. * d)
  let fB := (. * b)
  let fC := (. * c)
  let h3a : a * d * b * c = fC (fB (fD a)) := rfl
  let h5a : fC ∘ (fB ∘ fD) = fC ∘ (fD ∘ fB) := congr_arg (fC ∘ .) (mul_fn_comm b d)
  let h6a : fC ∘ fD ∘ fB = fD ∘ fC ∘ fB := congr_arg (. ∘ fB) (mul_fn_comm c d)
  let h8a : (fC ∘ fB ∘ fD) a = (fD ∘ fC ∘ fB) a := congr_fun (Eq.trans h5a h6a) a

  Eq.trans (Eq.trans (Eq.trans h2a h25a) h3a) h8a

-- Actual solution
example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d :=
  -- See above lemmas
  -- A few facts we will use
  -- Function composition associates in useful ways:
  -- a ∘ b ∘ c = a (b ∘ (c ∘ d))
  -- We can easily prove a * d * (b * c) = a * d (e * f) using congr_arg
  let h0 : a * d * (b * c) = a * d * (e * f) := congr_arg (HMul.hMul (a * d)) h
  -- Associativity gives us (a * d) * (b * c) = a * d * (b * c)
  let h1a : a * d * (b * c) = a * b * c * d := mul_assoc_4 a b c d
  let h2a : a * d * (e * f) = a * e * f * d := mul_assoc_4 a e f d

  Eq.trans (Eq.trans (Eq.symm h1a) h0) h2a

-- 5
--Please do this exercise without using the ring tactic.
example (a b : ℝ) : a^3 - b^3 = (a-b)*(a^2+a*b+b^2) :=
  -- Distribute a - b by converting to a + -b
  have h : (a-b)*(a^2+a*b+b^2) = (a + -b) * (a^2 + a*b + b^2) := congr_fun (congr_arg HMul.hMul (sub_eq_add_neg a b)) (a^2 + a*b + b^2)
  have h1 : (a + -b) * (a^2 + a*b + b^2) = a * (a^2+a*b+b^2) + -b * (a^2+a*b+b^2) := right_distrib a (-b) (a^2 + a * b + b^2)
  sorry

-- 6: Product of two odd numbers is odd.
example : ∀ m n : Nat, Odd m ∧ Odd n → Odd (m * n) := fun _ _ ⟨hm, hn⟩ => Odd.mul hm hn

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
example : P ∧ Q → Q := And.right

-- 12
example : (P → Q → R) → P ∧ Q → R
  | a, ⟨hp, hq⟩ => a hp hq

-- 14
example : ∀ x : ℝ, ∃ y, y + x = 2 := fun x => ⟨2 + -x, by simp⟩

-- 15
example : ∃ x : ℝ, 3 * x + 7 ≠ 12 := ⟨4, by norm_num⟩
