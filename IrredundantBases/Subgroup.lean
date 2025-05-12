import Mathlib.Algebra.Group.Subgroup.Finite

lemma Subgroup.card_lt_iff_lt {G : Type*} [Group G] [Finite G] (H: Subgroup G) :
    Nat.card H < Nat.card G ↔ H < ⊤ := by
  rw [Nat.lt_iff_le_and_ne]
  simp [Subgroup.card_le_card_group H]
