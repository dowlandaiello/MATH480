import Mathlib.Tactic
import Mathlib.Data.Rat.Sqrt

def MyVector (α : Type) (n : ℕ) := Vector α n

def magnitude {α : Type} {n : ℕ} [Add α] [Zero α] : MyVector α n → α := List.sum ∘ Array.toList ∘ Vector.toArray

def div {α : Type} {n : ℕ} [Div α] : MyVector α n → MyVector α n → MyVector α n
  | a, b => ⟨Array.map (fun (a, b) => Div.div a b) $ ((Vector.toArray a).zip (Vector.toArray b)), by simp⟩

def sub {α : Type} {n : ℕ} [Sub α] : MyVector α n → MyVector α n → MyVector α n
  | a, b => ⟨Array.map (fun (a, b) => a - b) $ ((Vector.toArray a).zip (Vector.toArray b)), by simp⟩

-- Note that the only thing different in the above 2 defs is the term x inside fun (a, b) => x
-- Take a look at the definition of a functor

def mapvector_2 {α : Type} {n : ℕ} : (α → α → α) → MyVector α n → MyVector α n → MyVector α n
  | f, a, b => ⟨Array.zipWith f (Vector.toArray a) (Vector.toArray b), by simp⟩

def add {α : Type} {n : ℕ} [Add α] : MyVector α n → MyVector α n → MyVector α n := mapvector_2 Add.add

def dot {α : Type} {n : ℕ} [Zero α] [Add α] [Mul α] : MyVector α n → MyVector α n → α
  | a, b => Array.sum ∘ Vector.toArray $ (mapvector_2 Mul.mul a b)

lemma a_dot_a_eq_mag_a_squared {α : Type} {n : ℕ} (a : MyVector α n) [Semiring α] : dot a a = (magnitude a) * (magnitude a) := by
  let ⟨⟨l⟩, _⟩ := a

  induction l with
  | nil =>
    unfold dot
    unfold magnitude
    simp
    unfold mapvector_2
    simp
  | cons x xs =>
    unfold dot
    unfold magnitude
    simp
    unfold mapvector_2
    simp
    simp [map_mul]
    --simp
    --repeat rw [left_distrib]
    --repeat rw [right_distrib]
    --rw [add_assoc]
    --rw [Mul.mul]
    --simp [HMul.hMul]
    --rw [Distrib.toMul]
    --rw [Mul.mul]
    --exact (congr rfl (by {
    --  rw [← Distrib.toMul]
    --  rw [← Mul.mul]
    --  
    --  sorry
    --}))
  --match a with
  --| (x, (y, z)) =>
  --  unfold dot
  --  unfold magnitude
  --  simp
  --  rw [pow_two]
  --  rw [Real.mul_self_sqrt $ add_nonneg (add_nonneg (pow_two_nonneg x) (pow_two_nonneg y)) (pow_two_nonneg z)]
  --  repeat rw [pow_two]
  sorry

lemma zero_dot (a : MyVector) : dot ⟨0,0,0⟩ a = 0 := by
  unfold dot
  simp
  match a with
  | (x, (y, z)) =>
    simp

lemma dot_commutes (a : MyVector) (b : MyVector) : dot a b = dot b a := by
  unfold dot
  match a, b with
  | (x₁, (y₁, z₁)), (x₂, (y₂, z₂)) =>
    simp
    ring

lemma dot_distributes (a : MyVector) (b : MyVector) (c : MyVector) : dot a (add b c) = dot a b + dot a c := by
  unfold dot
  unfold add
  match a, b, c with
  | (x₁, (y₁, z₁)), (x₂, (y₂, z₂)), (x₃, (y₃, z₃)) =>
    ring

example : ∃ a b c, 

