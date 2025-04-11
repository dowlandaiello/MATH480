import Mathlib.Tactic

class MyGroup (α : Type) where
  mul : α → α → α

  id : α
  inv : α → α

  id_mul (a : α) : mul a id = a

  mul_id (a : α) : mul id a = a
  mul_assoc (a b c : α) : mul (mul a b) c = mul a (mul b c)

  mul_inv (a : α) : mul a (inv a) = id
  inv_mul (a : α) : mul (inv a) a  = id

class MyAbelianGroup (α : Type) extends (MyGroup α) where
  mul_comm (a b : α) : mul a b = mul b a

lemma inv_uniquely_determined {α : Type} {G : Type} [MyGroup α g] : 
