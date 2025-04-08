import Mathlib.Tactic

def is_id {α : Type} (op : α → α → α) (id : α) := ∀ a, (op a id = a) ∧ (op id a = a)

-- The identity element is unique
lemma identity_monoid_unique {α : Type} (op : α → α → α) : ∀ e f, is_id op e ∧ is_id op f → e  = f
  | e, f, ⟨e_id, f_id⟩ =>
    have h1 : e = op e f := Eq.symm ∘ And.left $ (f_id e)
    have h2 : op e f = f := And.right $ e_id f

    Eq.trans h1 h2


