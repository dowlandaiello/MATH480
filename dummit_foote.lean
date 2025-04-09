import Mathlib.Tactic

-- Axioms for groups
def bin_op_associative {α : Type} (op : α → α → α) := ∀ a b c, op (op a b) c = op a (op b c)

def is_identity {α : Type} (op : α → α → α) (e : α) := ∀ a, op a e = a ∧ op e a = a
def has_identity {α : Type} (op : α → α → α) := ∃ e, is_identity op e
def has_identity_for {α : Type} (op : α → α → α) (a : α) := ∃ e, op a e = a ∧ op e a = a

def is_inverse {α : Type} (op : α → α → α) (inv : α) := ∀ a e, is_identity op e → op a inv = e ∧ op inv a = e
def is_inverse_for {α : Type} (op : α → α → α) (inv : α) (a : α) (e : α) := is_identity op e → op a inv = e ∧ op inv a = e
def has_inverse {α : Type} (op : α → α → α) := ∃ inv, is_inverse op inv
def has_inverse_for {α : Type} (op : α → α → α) (a : α) := ∃ e inv, is_identity op e → op a inv = e ∧ op inv a = e

-- Abelian group axioms
def is_abelian {α : Type} (op : α → α → α) := ∀ a b, op a b = op b a

-- Identity in a group is unique
lemma identity_unique {α : Type} (op : α → α → α) : ∀ e₁ e₂, is_identity op e₁ ∧ is_identity op e₂ → e₁ = e₂
  | e₁, e₂, ⟨id_e₁, id_e₂⟩ => by
    unfold is_identity at id_e₁
    unfold is_identity at id_e₂
    let ⟨a1, b1⟩ := id_e₁ e₂
    let ⟨_, b2⟩ := id_e₂ e₁
    rw [← a1]
    rw [← b2]
    conv =>
      right
      right
      rw [b2]

lemma inv_uniquely_determined {α : Type} (op : α → α → α) (e : α) (h_id_all : ∀ a, op a e = a ∧ op e a = a) (h_associative : bin_op_associative op): ∀ a inv₁ inv₂, is_inverse_for op inv₁ a e ∧ is_inverse_for op inv₂ a e → inv₁ = inv₂
  | a, inv₁, inv₂, ⟨is_inv₁, is_inv₂⟩ => by
    unfold is_inverse_for at is_inv₁
    unfold is_inverse_for at is_inv₂

    let ⟨h_is_inv₁l, h_is_inv₁r⟩ := is_inv₁ h_id_all
    let ⟨h_is_inv₂l, h_is_inv₂r⟩ := is_inv₂ h_id_all

    have ha : op a inv₁ = e := h_is_inv₁l

    have hc : op inv₂ e = op inv₂ (op a inv₁) := by
      rw [← ha]
    have hd : inv₂ = op inv₂ (op a inv₁) := by
      conv =>
        left
        rw [← (h_id_all inv₂).left]
        rfl
      exact hc

    have he : inv₂ = op (op inv₂ a) inv₁ := by
      simp [h_associative inv₂ a inv₁]
      simp [ha]
      simp [h_id_all inv₂]

    rw [h_is_inv₂r] at he
    simp [h_id_all] at he

    exact (Eq.symm he)

lemma inv_inv_eq_a {α : Type} (op : α → α → α) (e : α) (h_id_all : ∀ a, op a e = a ∧ op e a = a) (h_associative : bin_op_associative op) : ∀ a a_inv a_inv_inv, is_inverse_for op a_inv a e ∧ is_inverse_for op a_inv_inv a_inv e → op (op a a_inv) a_inv_inv = a
  | a, a_inv, a_inv_inv, ⟨a_inv_is_inverse, a_inv_inv_is_inverse⟩ => by
    have h : op a_inv a_inv_inv = e := (a_inv_inv_is_inverse h_id_all).left
    rw [h_associative a a_inv a_inv_inv]
    rw [h]

    exact And.left $ h_id_all a
