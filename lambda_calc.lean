import Mathlib.Tactic

-- Lambda calculus is a computational system based on variable substitution within function scopes
-- You indicate a function in lambda calculus with
-- λx.x
-- Eerything occurring after the . indicates the output of the function
-- the variable after the λ indicates the name the input value is substituted in
-- In the above function, x in the body is substituted with the input
--
-- For example (λx.x) (a)
-- => a

-- Lambda notation in lean

#check (fun x => x)

#check (fun x => x) 1
#eval (fun x => x) 1

-- It is important to note that a λ expression is an "anonymous function"
-- It is a **value**. It has no name.
-- However, we can attach a name to it for convenience in Lean

-- Lean has issues with this, since expressions must be well-typed in lean
-- We cannot have an expression with an unknown type
-- This is what *failed to infer binder type* means
-- The expression is not well-typed
def myidbad := fun x => x

-- We can fix this easily

def myid := fun x : ℕ => x

-- We can type this function a few different ways
-- Here, the type of myid is inferred from our typign of x
-- However, we can be more explicit if we want
-- Here is the notation for typing a lambda
def myid' : ℕ → ℕ := fun x : ℕ => x

-- We can remove the type for x now
def myid'' : ℕ → ℕ := fun x => x

-- This notation is semantically equivalent in this case to
-- a named definition with a named x parameter
def myid''' (n : ℕ) : ℕ := n

-- I mean semantically equivalent in that their usage is the same
#check myid''' 1
#check myid 2
#check (myid''')

-- Lean's type system is based on a powerful, expressive type system
-- called the calculus of constructions
-- the calculus of constructions's main feature is that you can
-- MIX types and terms
-- This is because types are themselves terms
-- See here:
#check ℕ → ℕ
#check ℕ
#check Type

-- We can define our own type, for example, as a term
-- This unlike other languages where there is a barrier between types and terms
def MyType : Type := ℕ

-- This is kind of useless, but we can now type a function with our type
def myfunc : MyType → MyType := fun x => x

#check myfunc

-- This is perfectly valid
-- So, if types can be terms, and terms can be types,
-- can types be functions? And what does that mean?
-- Let's try it out.
-- Ideally, we want our tuple to allow different types
-- to be stored next to each other.

-- Let's define the type of our tuple container
-- Tuple is obviously going to be a type.
-- However, Tuple ℕ ℝ is not the same type as Tuple ℚ ℝ
-- So, how can we make them different?
-- We can make our type a function of the two types
-- to create a new type
def Tuple : Type → Type → Type 1 := fun _t1 _t2 => Type

-- Now, we can make a Tuple of ℕ and ℝ
def my_tup : Tuple ℝ ℕ := sorry

-- Here, we called Tuple as a function to create a new type, which is the type of my_tup

#check my_tup

-- Ideally, we would like to use our tuple like such fist (mk_tup 1 2) = 1
-- snd (mk_tup 1 2) = 2
-- We can say that the return type of our tup function is a Tuple α β,
-- where α and β are the input types to the Tuple
-- However, we will need some way to reference these types
def mk_tup (α : Type) (β : Type) (val1 : α) (val2 : β) : Tuple α β := Sort 0

-- This is kind of useless, since we won't have a way to retrieve the values later
-- Sort here indicates the type universe below Type n.
-- Sort n = Type n + 1
#check (Sort 1) = Type 0

def Tuple' (α : Type) (β : Type) : Type 1 := ∀ (γ : Type), (α → β → γ) → γ
def TupleMaker (α : Type) (β : Type) := α → β → Tuple' α β

def mk_tup' (α : Type) (β : Type) : TupleMaker α β :=
  fun x y _ f => (f x) y

-- And a first function
def fst (α : Type) (β : Type) : Tuple' α β → α :=
  fun tup => tup α (fun x _ => x)

def snd (α : Type) (β : Type) : Tuple' α β → β :=
  fun tup => tup β (fun _ y => y)

-- Now, we can make a Tuple of ℕ and ℝ
def my_tup' : Tuple' ℝ ℕ := mk_tup' ℝ ℕ (0 : ℝ) (1 : ℕ)

def first_elem := fst ℝ ℕ my_tup'

-- This is the power of dependent typing
-- Types are terms.
-- Here are examples of some dependent types:

-- This has a maximum value of 10
def maxInt := Fin 10

#check (⟨9, by simp⟩ : maxInt)

-- This does not compile
#check (⟨10, by simp⟩ : maxInt)

def vector4 := Vector ℕ 4

-- This compiles
#check (⟨⟨[1, 2, 3, 4]⟩, by simp⟩ : vector4)
-- This does not
#check (⟨⟨[1, 2, 3, 4, 5]⟩, by simp⟩ : vector4)

-- Conveniences

-- We can rewrite our fst and snd functions to use implict parameters
def fst'' {α : Type} {β : Type} : Tuple' α β → α :=
  fun tup => tup α (fun x _ => x)

def snd'' {α β : Type} : Tuple' α β → β :=
  fun tup => tup β (fun _ y => y)

-- Example: the S K combinators
-- K x y   = x
-- S x y z = x z (y z)
def k {α : Type} {β : Type} (a : α) (_ : β) := a

def s {α : Type} {β : Type} {γ : Type} (y : β → α) (x : β → α → γ) (z : β) := x z (y z)

-- Extra: we can do this in tactic mode treating this like a prop logic problem
def s' {α : Type} {β : Type} {γ : Type} (y : β → α) (x : β → α → γ) (z : β) : γ := by
  apply x
  apply z
  apply y
  apply z
