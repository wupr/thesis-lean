import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Hom

import IrredundantBases.Submonoid

section OrbitRel

variable {G α : Type*} [Group G] [MulAction G α]

open MulAction in
@[to_additive]
noncomputable def MulActionHom.stabilizerEquivStabilizerOfOrbitRel
    {a b : α} (h : orbitRel G α a b) :
    α →ₑ[stabilizerEquivStabilizerOfOrbitRel h] α :=
  let x := Classical.choose h
  {
    toFun a := x⁻¹ • a
    map_smul' y c := by
      obtain ⟨y, _⟩ := y
      change x⁻¹ • y • c = (x⁻¹ * y * x) • x⁻¹ • c
      rw [mul_smul, smul_smul, smul_inv_smul]
  }

open MulAction in
@[to_additive]
lemma MulActionHom.stabilizerEquivStabilizerOfOrbitRel_bijective
    {a b : α} (h : orbitRel G α a b) :
    Function.Bijective (stabilizerEquivStabilizerOfOrbitRel h) :=
  MulAction.bijective _

end OrbitRel

namespace MulActionHom

variable {M α : Type*} [Monoid M] [MulAction M α]

@[to_additive (attr := simps!)]
def ofSubmonoidSubtype (N : Submonoid M) : α →ₑ[N.subtype] α where
  toFun := id
  map_smul' _ _ := rfl

@[to_additive (attr := simp)]
lemma coe_ofSubmonoidSubtype (N : Submonoid M) : (ofSubmonoidSubtype N : α → α) = id := rfl

@[to_additive]
lemma ofSubmonoidSubtype_injective (N : Submonoid M) :
    Function.Injective (ofSubmonoidSubtype (α := α) N) :=
  Function.injective_id

@[to_additive]
lemma ofSubmonoidSubtype_bijective (N : Submonoid M) :
    Function.Bijective (ofSubmonoidSubtype (α := α) N) :=
  Function.bijective_id

@[to_additive (attr := simps)]
def ofSubmonoidInclusion {S T : Submonoid M} (h : S ≤ T) : α →ₑ[Submonoid.inclusion h] α where
  toFun := id
  map_smul' _ _ := rfl

@[to_additive (attr := simp)]
lemma coe_ofSubmonoidInclusion {S T : Submonoid M} (h : S ≤ T) :
    (ofSubmonoidInclusion h : α → α) = id :=
  rfl

@[to_additive]
lemma ofSubmonoidInclusion_injective {S T : Submonoid M} (h : S ≤ T) :
    Function.Injective (ofSubmonoidInclusion (α := α) h) :=
  Function.injective_id

end MulActionHom

namespace Submonoid

variable {M N α β : Type*} [Monoid M] [Monoid N] [MulAction M α] [MulAction N β]

open MulAction

@[to_additive]
lemma image_stabilizerSubmonoid_le (φ : M → N) (f : α →ₑ[φ] β) (a : α) :
    φ '' stabilizerSubmonoid M a ≤ stabilizerSubmonoid N (f a) := by
  intro n ⟨m, h1, h2⟩
  rw [SetLike.mem_coe, mem_stabilizerSubmonoid_iff, ← h2, ← map_smulₛₗ, h1]

@[to_additive]
lemma map_stabilizerSubmonoid_le (φ : M →* N) (f : α →ₑ[φ] β) (a : α) :
    (stabilizerSubmonoid M a).map φ ≤ stabilizerSubmonoid N (f a) := by
  exact image_stabilizerSubmonoid_le _ f a

@[to_additive]
lemma image_stabilizerSubmonoid_eq_of_injective (φ : M → N) (f : α →ₑ[φ] β)
    (hf : Function.Injective f) (a : α) :
    φ '' stabilizerSubmonoid M a = Set.range φ ⊓ stabilizerSubmonoid N (f a) := by
  refine le_antisymm ?_ ?_
  · exact le_inf (Set.image_subset_range ..) (image_stabilizerSubmonoid_le ..)
  intro n
  simp only [Set.inf_eq_inter, Set.mem_inter_iff, Set.mem_range, SetLike.mem_coe,
    mem_stabilizerSubmonoid_iff, Set.mem_image, and_imp, forall_exists_index]
  rintro m rfl h2
  refine ⟨m, hf ?_, rfl⟩
  rwa [← map_smulₛₗ] at h2

@[to_additive]
lemma map_stabilizerSubmonoid_eq_of_injective (φ : M →* N) (f : α →ₑ[φ] β)
    (hf : Function.Injective f) (a : α) :
    (stabilizerSubmonoid M a).map φ = MonoidHom.mrange φ ⊓ stabilizerSubmonoid N (f a) := by
  rw [SetLike.ext'_iff]
  simpa using image_stabilizerSubmonoid_eq_of_injective _ _ hf a

section MulActionHom

open MulActionHom

@[to_additive]
lemma subtype_image_stabilizerSubmonoid (N : Submonoid M) (a : α) :
    N.subtype '' (stabilizerSubmonoid N a) = N ⊓ stabilizerSubmonoid M a := by
  convert image_stabilizerSubmonoid_eq_of_injective _ _ (ofSubmonoidSubtype_injective N) a using 1
  simp [ofSubmonoidSubtype_apply N]

@[to_additive]
lemma map_subtype_stabilizerSubmonoid (N : Submonoid M) (a : α) :
    (stabilizerSubmonoid N a).map N.subtype  = N ⊓ stabilizerSubmonoid M a := by
  convert map_stabilizerSubmonoid_eq_of_injective _  _ (ofSubmonoidSubtype_injective N) a using 1
  simp [ofSubmonoidSubtype_apply N]

end MulActionHom

end Submonoid

namespace MulActionHom

variable {M N α β : Type*} [Monoid M] [Monoid N] [MulAction M α] [MulAction N β]

open MulAction

@[to_additive]
lemma stabilizerSubmonoid_lt_top (φ : M →* N) (hφ : Function.Injective φ) (f : α →ₑ[φ] β)
    (hf : Function.Injective f) (a : α) :
    stabilizerSubmonoid M a < ⊤ → stabilizerSubmonoid N (f a) < ⊤ := by
  rw [Submonoid.lt_iff_map_lt φ hφ, Submonoid.map_stabilizerSubmonoid_eq_of_injective φ f hf,
    ← MonoidHom.mrange_eq_map φ]
  intro h; contrapose! h
  simp_all

end MulActionHom
