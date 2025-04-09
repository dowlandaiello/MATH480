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
-- Supposed we want to create a tuple type
-- that stores two types next to each other
-- We will do this by defining a fst function and a snd function
-- the fst function returns the first of two elements
-- and the snd function returns the second of two elements:
-- fst a b => a
-- snd a b => b

-- We can obviously say that fst is a function that takes in a type a, a type b,
-- a value of type a called first_elem, a value of type b called second_elem,
-- and returns first_elem (of type a)
--
-- However, if we want to return type a, we need some way to refer to it
-- This is where named parameters become handy
def fst (ta : Type) (tb : Type) : ta → tb → ta := fun first_elem _ => first_elem

#check fst ℕ
#check fst ℕ ℝ

-- Snd is easy
def snd (ta : Type) (tb : Type) : ta → tb → tb := fun _ second_elem => second_elem

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
def fst' {ta : Type} {tb : Type} : ta → tb → ta := fun first_elem _ => first_elem

-- The usual notation is to use greek letters for type parameters
def snd' {α β : Type} : α → β → α := fun first_elem _ => first_elem

