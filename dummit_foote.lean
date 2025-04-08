import Mathlib.Tactic

-- Axioms for groups
def bin_op_associative {α : Type} (op : α → α → α) := ∀ a b c, op (op a b) c = op a (op b c)
def has_identity {α : Type} (op : α → α → α) := ∀ a, ∃ e, op a e = a ∧ op e a = a

def is_identity {α : Type} (op : α → α → α) (id : α) := ∀ a, (op a id = a) ∧ (op id a = a)

-- Identity in a group is unique
lemma identity_unique {α : Type} (a : α) 
