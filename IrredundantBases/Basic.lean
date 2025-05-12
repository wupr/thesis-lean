import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Have

import IrredundantBases.MulAction
import IrredundantBases.MulActionHom

@[to_additive]
lemma MonoidHom.restrict_injective {M N : Type*} [MulOneClass M] [MulOneClass N] {S : Type*}
    [SetLike S M] [SubmonoidClass S M] (φ : M →* N) (s : S) :
    Function.Injective φ → Function.Injective (φ.restrict s) :=
  fun h _ _ hmn => Subtype.eq <| h hmn

@[to_additive]
lemma Submonoid.top_eq_bot_iff_subsingleton {M : Type*} [Monoid M] :
  (⊤ : Submonoid M) = ⊥ ↔ Subsingleton M := by
  rw [Submonoid.eq_bot_iff_forall, _root_.subsingleton_iff]
  exact ⟨fun h x y => h y trivial ▸ h x trivial, fun h x _ => h x 1⟩

namespace MulAction

variable {M α : Type*} [Monoid M] [MulAction M α]

/- **Irredundancy** -/

def IsIrredundant (M : Type*) {α : Type*} [Monoid M] [MulAction M α] : List α → Prop
  | [] => True
  | a :: as => stabilizerSubmonoid M a < ⊤ ∧ IsIrredundant (stabilizerSubmonoid M a) as

def _root_.AddAction.IsIrredundant (M : Type*) {α : Type*} [AddMonoid M] [AddAction M α] :
    List α → Prop
  | [] => True
  | a :: as => AddAction.stabilizerAddSubmonoid M a < ⊤ ∧
      IsIrredundant (AddAction.stabilizerAddSubmonoid M a) as

attribute [to_additive existing] IsIrredundant

@[to_additive (attr := simp)]
lemma isIrredundant_nil : IsIrredundant M ([] : List α) :=
  (@IsIrredundant.eq_1 M α _ _) ▸ True.intro

@[to_additive]
lemma isIrredundant_cons {a : α} {as : List α} :
    IsIrredundant M (a :: as) ↔
      stabilizerSubmonoid M a < ⊤ ∧ IsIrredundant (stabilizerSubmonoid M a) as :=
  (IsIrredundant.eq_2 M a as).to_iff

@[to_additive]
lemma isIrredundant_singleton {a : α} :
    IsIrredundant M [a] ↔ stabilizerSubmonoid M a < ⊤ := by
  simp [isIrredundant_cons]

@[to_additive]
lemma length_le_card_of_isIrredundant [Finite M] {as : List α} (h : IsIrredundant M as) :
    as.length ≤ Nat.card M := by
  induction as generalizing M with
  | nil => simp only [List.length_nil, zero_le]
  | cons a as ih =>
    rw [List.length_cons]
    rw [isIrredundant_cons] at h
    obtain ⟨h1, h2⟩ := h
    refine lt_of_le_of_lt (ih h2) ?_
    exact Submonoid.card_top (M := M) ▸ Submonoid.card_le_card_of_finite h1

@[to_additive]
lemma isIrredundant_of_mulActionHom
    {M₁ M₂ α₁ α₂: Type*} [Monoid M₁] [Monoid M₂] [MulAction M₁ α₁] [MulAction M₂ α₂]
    (φ : M₁ →* M₂) (hφ : Function.Injective φ) (f : α₁ →ₑ[φ] α₂) (hf : Function.Injective f)
    (as : List α₁) :
    IsIrredundant M₁ as → IsIrredundant M₂ (as.map f) := by
  induction as generalizing M₁ M₂ with
  | nil => simp only [isIrredundant_nil, List.map_nil, imp_self]
  | cons a as ih =>
    rw [List.map_cons,isIrredundant_cons, isIrredundant_cons]
    refine And.imp (MulActionHom.stabilizerSubmonoid_lt_top φ hφ f hf a) ?_
    set N₁ := stabilizerSubmonoid M₁ a
    set N₂ := stabilizerSubmonoid M₂ (f a)
    let φ':= (φ.restrict N₁).codRestrict N₂ <| fun m => by
      have := SetLike.le_def.mp <| Submonoid.map_stabilizerSubmonoid_le φ f a
      refine this ⟨m, ?_⟩
      simp only [Subtype.coe_prop, MonoidHom.restrict_apply, and_self]
    have hφ' : Function.Injective φ' :=
      MonoidHom.injective_codRestrict .. |>.mpr <| φ.restrict_injective N₁ hφ
    let f' : α₁ →ₑ[φ'] α₂ := ⟨f, fun _ _ => by rw [Submonoid.mk_smul, map_smulₛₗ]; rfl⟩
    have hf' : Function.Injective f' := fun _ _ h => hf h
    exact ih φ' hφ' f' hf'

@[to_additive]
lemma isIrredundant_of_submonoid {N : Submonoid M} {as : List α} :
    IsIrredundant N as → IsIrredundant M as := by
  convert isIrredundant_of_mulActionHom _ N.subtype_injective _
    (MulActionHom.ofSubmonoidSubtype_injective N) as using 2
  exact (List.map_id as).symm

@[to_additive]
lemma isIrredundant_of_submonoid_le {N₁ N₂ : Submonoid M} (h : N₁ ≤ N₂) {as : List α} :
    IsIrredundant N₁ as → IsIrredundant N₂ as := by
  convert isIrredundant_of_mulActionHom _ (Submonoid.inclusion_injective h) _
    (MulActionHom.ofSubmonoidInclusion_injective h) as using 2
  exact (List.map_id as).symm

@[to_additive]
lemma isIrredundant_append {as bs : List α}
    (h1 : IsIrredundant M as)
    (h2 : IsIrredundant (⨅ a ∈ as, stabilizerSubmonoid M a : Submonoid M) bs) :
    IsIrredundant M (as ++ bs) := by
  induction as generalizing M with
  | nil => exact bs.nil_append ▸ isIrredundant_of_submonoid h2
  | cons a as ih =>
    simp only [List.cons_append, isIrredundant_cons] at h1 ⊢
    refine ⟨h1.1, ih h1.2 ?_⟩
    set N := stabilizerSubmonoid M a
    let φ : (⨅ b ∈ a :: as, stabilizerSubmonoid M b : Submonoid M) →*
      (⨅ b ∈ as, stabilizerSubmonoid N b : Submonoid _) := {
        toFun m := by
          have := m.property
          simp only [List.mem_cons, iInf_or, iInf_inf_eq] at this
          refine ⟨⟨m.val, ?_⟩, ?_⟩
          · simpa [mem_stabilizerSubmonoid_iff] using this.1
          · simpa [Submonoid.mem_iInf] using this.2
        map_one' := rfl
        map_mul' _ _ := rfl
      }
    have hφ : Function.Injective φ := fun _ _ h => by simpa [φ] using h
    let f : α →ₑ[φ] α := ⟨id, fun _ _ => rfl⟩
    convert isIrredundant_of_mulActionHom φ hφ f Function.injective_id bs h2
    exact (List.map_id bs).symm

/- **Bases** -/

variable (M) in
@[to_additive]
def IsBase (as : List α) : Prop :=
  (⨅ δ ∈ as, stabilizerSubmonoid M δ) = ⊥

@[to_additive]
lemma isBase_iff {as : List α} :
    IsBase M as ↔ (⨅ δ ∈ as, stabilizerSubmonoid M δ) = ⊥ :=
  Iff.rfl

@[to_additive (attr := simp)]
lemma isBase_submonoid (N : Submonoid M) (as : List α) :
    IsBase N as ↔ N ⊓ (⨅ δ ∈ as, stabilizerSubmonoid M δ) = ⊥ := by
  rw [isBase_iff, Submonoid.eq_iff_map_eq _ N.subtype_injective, Submonoid.map_bot]
  refine Eq.congr ?_ rfl
  rw [SetLike.ext'_iff]
  ext m
  simp [And.comm]

@[to_additive (attr := simp)]
lemma isBase_of_subsingleton [Subsingleton M] {as : List α} : IsBase M as := by
  exact Submonoid.eq_bot_of_subsingleton _

/- **Irredundant bases** -/

@[to_additive]
lemma exists_isIrredundant_and_isBase (M α : Type*) [Monoid M] [MulAction M α]
    [Finite M] [FaithfulSMul M α] :
    ∃ as : List α, IsIrredundant M as ∧ IsBase M as := by
  by_cases h : Nontrivial M
  · obtain ⟨a, ha⟩ := exists_not_mem_fixedPoints_iff _ α |>.mpr h
    have ha' := stabilizerSubmonoid_lt_top_iff_notin_fixedPoints.mpr ha
    have : FaithfulSMul (stabilizerSubmonoid M a) α
    · exact FaithfulSMul.mk (Subtype.eq <| FaithfulSMul.eq_of_smul_eq_smul ·)
    obtain ⟨as, h3, h4⟩ := exists_isIrredundant_and_isBase (stabilizerSubmonoid M a) α
    use a :: as
    rw [isIrredundant_cons]
    use ⟨ha', h3⟩
    rw [isBase_submonoid] at h4
    simpa [isBase_iff, iInf_or, iInf_inf_eq]
  · use []
    rw [not_nontrivial_iff_subsingleton, ← Submonoid.top_eq_bot_iff_subsingleton] at h
    simpa [isBase_iff]
  termination_by Nat.card M
  decreasing_by exact Submonoid.card_top (M := M) ▸ Submonoid.card_le_card_of_finite ha'

@[to_additive]
lemma exists_isBase_extending_isIrredundant [Finite M] [FaithfulSMul M α] [Nonempty α]
    (as : List α) (h : IsIrredundant M as) :
    ∃ bs : List α, as <+: bs ∧ IsIrredundant M bs ∧ IsBase M bs := by
  obtain ⟨bs, h2, h3⟩ := exists_isIrredundant_and_isBase
    (⨅ δ ∈ as, stabilizerSubmonoid M δ : Submonoid M) α
  use as ++ bs
  refine ⟨List.prefix_append _ _, isIrredundant_append h h2, ?_⟩
  simp only [isBase_submonoid] at h3
  simpa [isBase_iff, iInf_or, iInf_inf_eq]

/- **Maximum irredundant base size** -/

variable (M α) in
@[reducible]
private def lengthImageOfIsIrredundant : Set ℕ :=
  List.length '' {as : List α | IsIrredundant M as}

private lemma lengthImageOfIsIrredundant_finite [Finite M] :
    (lengthImageOfIsIrredundant M α).Finite := by
  rw [Set.finite_iff_bddAbove]
  use Nat.card M
  intro n hn
  obtain ⟨as, h1 ,h2⟩ := Set.mem_image .. |>.mp hn
  exact h2 ▸ length_le_card_of_isIrredundant h1

private lemma lengthImageOfIsIrredundant_nonempty :
    (lengthImageOfIsIrredundant M α).Nonempty :=
  Set.image_nonempty.mpr ⟨[], @isIrredundant_nil M α _ _⟩

variable [Finite M]

variable (M α) in
@[to_additive]
noncomputable def mlii : ℕ :=
  lengthImageOfIsIrredundant_finite.toFinset.max' <| Set.Finite.toFinset_nonempty _ |>.mpr <|
    lengthImageOfIsIrredundant_nonempty (M := M) (α := α)

@[to_additive]
lemma length_le_mlii (as : List α) (h : IsIrredundant M as) :
    as.length ≤ mlii M α := by
  apply Finset.le_max'
  rw [Set.Finite.mem_toFinset]
  use as, h

@[to_additive]
lemma mlii_le {n : ℕ} (h : ∀ as : List α, IsIrredundant M as → as.length ≤ n) :
    mlii M α ≤ n := by
  apply Finset.max'_le _ _
  simpa

@[to_additive]
lemma mlii_le' {n : ℕ} (h : ∀ as : List α, 0 < as.length → IsIrredundant M as → as.length ≤ n) :
    mlii M α ≤ n := by
  refine mlii_le fun as h1 => ?_
  exact (Nat.eq_zero_or_pos as.length).elim (fun h2 => h2 ▸ Nat.zero_le _) (fun h' => h as h' h1)

variable (M α) in
@[to_additive]
lemma exists_isIrredundant_and_length_eq_mlii :
    ∃ as : List α, IsIrredundant M as ∧ as.length = mlii M α :=
  lengthImageOfIsIrredundant_finite.mem_toFinset.mp <| Set.Finite.toFinset _ |>.max'_mem _

@[to_additive]
lemma mlii_lt {n : ℕ} (h : ∀ as : List α, IsIrredundant M as → as.length < n) :
    mlii M α < n := by
  apply Finset.max'_lt_iff _ _ |>.mpr
  simpa

@[to_additive]
lemma mlii_lt' {n : ℕ} (h1 : mlii M α > 0)
    (h2 : ∀ as : List α, 0 < as.length → IsIrredundant M as → as.length < n) :
    mlii M α < n := by
  cases n with
  | zero =>
    obtain ⟨bs, h4, h5⟩ := exists_isIrredundant_and_length_eq_mlii M α
    simp_all [h2 bs (h5 ▸ h1) h4]
  | succ n =>
    simp_rw [Nat.lt_add_one_iff] at h2 ⊢
    exact mlii_le' h2

variable (M α) in
@[to_additive]
lemma nontrivial_iff_mlii_pos [FaithfulSMul M α] :
    Nontrivial M ↔ 0 < mlii M α := by
  simp_rw [← exists_not_mem_fixedPoints_iff M α, ← stabilizerSubmonoid_lt_top_iff_notin_fixedPoints]
  refine ⟨fun ⟨a, ha⟩ => ?_, fun h => ?_⟩
  · rw [← Order.one_le_iff_pos]
    exact length_le_mlii [a] (isIrredundant_singleton.mpr ha)
  · obtain ⟨as, h1, h2⟩ :=
      exists_isIrredundant_and_length_eq_mlii M α
    rw [← h2, List.length_pos_iff_exists_cons] at h
    obtain ⟨a, _, rfl⟩ := h
    exact ⟨a, (isIrredundant_cons.mp h1).1⟩

variable (M α) in
@[to_additive]
lemma subsingleton_iff_mlii_eq_zero [FaithfulSMul M α] :
    Subsingleton M ↔ mlii M α = 0 := by
  rw [← not_nontrivial_iff_subsingleton]
  have := nontrivial_iff_mlii_pos M α
  rwa [Nat.pos_iff_ne_zero, iff_not_comm, Iff.comm] at this

section

variable {M₁ M₂ α₁ α₂: Type*} [Monoid M₁] [Monoid M₂] [MulAction M₁ α₁] [MulAction M₂ α₂]
  [Finite M₁] [Finite M₂]

@[to_additive]
lemma mlii_le_of_mulActionHom
    (φ : M₁ →* M₂) (hφ : Function.Injective φ) (f : α₁ →ₑ[φ] α₂) (hf : Function.Injective f) :
    mlii M₁ α₁ ≤ mlii M₂ α₂ := by
  refine mlii_le fun as h => ?_
  have := length_le_mlii _ (isIrredundant_of_mulActionHom φ hφ f hf as h)
  rwa [List.length_map] at this

@[to_additive]
lemma mlii_eq_of_bijective_mulActionHom
    (φ : M₁ ≃* M₂) (f : α₁ →ₑ[φ] α₂) (hf : Function.Bijective f) :
    mlii M₁ α₁ = mlii M₂ α₂ := by
  refine Nat.le_antisymm ?_ ?_
  · exact mlii_le_of_mulActionHom φ φ.injective f hf.1
  · let f' := Equiv.ofBijective f hf
    let g : α₂ →ₑ[φ.symm] α₁ := {
      toFun := f'.symm
      map_smul' m a₂ := hf.1 <| by
        have (a₂ : α₂) : f (f'.symm a₂) = a₂ := Equiv.apply_symm_apply f' a₂
        rw [this]
        have map_smul := f.map_smul' (φ.symm m) (f'.symm a₂)
        have toFun_apply (a : α₁) : f.toFun a = f a := rfl
        rw [toFun_apply, toFun_apply] at map_smul
        rw [map_smul, this, MulEquiv.apply_symm_apply]
    }
    exact mlii_le_of_mulActionHom φ.symm φ.symm.injective g f'.symm.injective

end

@[to_additive]
lemma mlii_submonoid_le (N : Submonoid M) :
    mlii N α ≤ mlii M α :=
  mlii_le_of_mulActionHom _ N.subtype_injective _ <| MulActionHom.ofSubmonoidSubtype_injective _

@[to_additive]
lemma mlii_stabilizerSubmonoid_lt {a : α} (h : a ∉ fixedPoints M α) :
    mlii (stabilizerSubmonoid M a) α < mlii M α := by
  refine mlii_lt fun as h' => ?_
  rw [← Nat.add_one_le_iff, ← @List.length_cons _ a]
  refine length_le_mlii _ <| isIrredundant_cons.mpr ?_
  exact ⟨stabilizerSubmonoid_lt_top_iff_notin_fixedPoints.mpr h, h'⟩

@[to_additive]
lemma mlii_stabilizerSubmonoid_eq {a : α} (h : a ∈ fixedPoints M α) :
    mlii (stabilizerSubmonoid M a) α = mlii M α := by
  rw [← stabilizerSubmonoid_eq_top_iff_mem_fixedPoints] at h
  let φ := stabilizerSubmonoidMulEquivOfEqTop a h
  exact mlii_eq_of_bijective_mulActionHom φ _ (MulActionHom.ofSubmonoidSubtype_bijective _)

@[to_additive]
lemma mlii_stabilizerSubmonoid_lt_iff {a : α} :
    mlii (stabilizerSubmonoid M a) α < mlii M α ↔ a ∉ fixedPoints M α := by
  refine ⟨fun h => ?_, mlii_stabilizerSubmonoid_lt⟩
  · contrapose! h
    exact ge_of_eq <| mlii_stabilizerSubmonoid_eq h

@[to_additive]
lemma exists_mlii_stabilizerSubmonoid_add_one_eq (h : 0 < mlii M α) :
    ∃ a : α, a ∉ fixedPoints M α ∧ mlii (stabilizerSubmonoid M a) α + 1 = mlii M α := by
  obtain ⟨as, h1, h2⟩ := exists_isIrredundant_and_length_eq_mlii M α
  obtain ⟨a, as, rfl⟩ := List.exists_cons_of_length_pos (h2 ▸ h)
  rw [isIrredundant_cons, stabilizerSubmonoid_lt_top_iff_notin_fixedPoints] at h1
  use a, h1.1
  refine Nat.le_antisymm ?_ ?_
  · rw [Nat.add_one_le_iff]
    apply mlii_stabilizerSubmonoid_lt
    exact h1.1
  · rw [← h2, List.length_cons, Nat.add_one_le_add_one_iff]
    exact length_le_mlii _ h1.2

end MulAction

namespace MulAction

variable {G α : Type*} [Group G] [MulAction G α] [Finite G]

lemma mlii_stabilizerSubmonoid_eq_mlii_stabilizer {a : α} :
    mlii (stabilizerSubmonoid G a) α = mlii (stabilizer G a) α := by
  rfl

@[to_additive]
lemma mlii_subgroup_le (H : Subgroup G) :
    mlii H α ≤ mlii G α :=
  mlii_submonoid_le _

end MulAction
