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
  | f, a, b => ⟨Array.map (fun (a, b) => f a b) $ ((Vector.toArray a).zip (Vector.toArray b)), by simp⟩

instance Functor 

def add : MyVector → MyVector → MyVector
  | ⟨x₁, y₁, z₁⟩, ⟨x₂, y₂, z₂⟩ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

def dot : MyVector → MyVector → ℝ
  | ⟨x₁, y₁, z₁⟩, ⟨x₂, y₂, z₂⟩ => x₁ * x₂ + y₁ * y₂ + z₁ * z₂

lemma a_dot_a_eq_mag_a_squared (a : MyVector) : dot a a = (magnitude a) ^ 2 := by
  match a with
  | (x, (y, z)) =>
    unfold dot
    unfold magnitude
    simp
    rw [pow_two]
    rw [Real.mul_self_sqrt $ add_nonneg (add_nonneg (pow_two_nonneg x) (pow_two_nonneg y)) (pow_two_nonneg z)]
    repeat rw [pow_two]

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

--theorem dot_geometric_eq (a : MyVector) (b : MyVector) (θ : ℝ) (h1 : Real.sin θ = (magnitude (sub a b)) / (magnitude a)) : dot a b = (magnitude a) * (magnitude b) * (Real.cos θ) := by

lemma orthoganol : 
