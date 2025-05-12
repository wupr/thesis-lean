import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Data.Finite.Card

variable {M : Type*} [Monoid M]

namespace Submonoid

@[to_additive]
lemma card_le_card_of_finite [Finite M] {N O : Submonoid M} (h : N < O) :
    Nat.card N < Nat.card O :=
  Set.toFinite _ |>.card_lt_card h

@[to_additive]
theorem card_top : Nat.card (⊤ : Submonoid M) = Nat.card M :=
  Nat.card_congr topEquiv.toEquiv

@[to_additive]
lemma le_iff_map_le {M' : Type*} [Monoid M'] (φ : M →* M') (hφ : Function.Injective φ)
    {N₁ N₂ : Submonoid M} :
    N₁ ≤ N₂ ↔ N₁.map φ  ≤ N₂.map φ := by
  nth_rw 2 [← SetLike.coe_subset_coe]
  simp_all

@[to_additive]
lemma eq_iff_map_eq {M' : Type*} [Monoid M'] (φ : M →* M') (hφ : Function.Injective φ)
    {N₁ N₂ : Submonoid M} :
    N₁ = N₂ ↔ N₁.map φ = N₂.map φ := by
  rw [le_antisymm_iff, le_antisymm_iff]
  exact and_congr (le_iff_map_le φ hφ) (le_iff_map_le φ hφ)

@[to_additive]
lemma lt_iff_map_lt {M' : Type*} [Monoid M'] (φ : M →* M') (hφ : Function.Injective φ)
    {N₁ N₂ : Submonoid M} :
    N₁ < N₂ ↔ N₁.map φ  < N₂.map φ := by
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne]
  exact Iff.and (le_iff_map_le φ hφ) (not_iff_not.mpr (eq_iff_map_eq φ hφ))

@[to_additive (attr := simp)]
lemma map_subtype_top (N : Submonoid M) : Submonoid.map N.subtype ⊤ = N := by
  ext _
  simp

@[to_additive]
lemma inclusion_injective {S T : Submonoid M} (h : S ≤ T) :
    Function.Injective (Submonoid.inclusion h) :=
  Set.inclusion_injective h

end Submonoid
