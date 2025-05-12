import Mathlib.Data.Finite.Prod

import IrredundantBases.Basic

variable {M₁ M₂ α₁ α₂ : Type*}
namespace Prod

@[to_additive]
instance instSMul' [SMul M₁ α₁] [SMul M₂ α₂] : SMul (M₁ × M₂) (α₁ × α₂) where
  smul m a := (m.1 • a.1, m.2 • a.2)

@[to_additive (attr := simp)]
lemma smul'_def [SMul M₁ α₁] [SMul M₂ α₂] (m : M₁ × M₂) (a : α₁ × α₂) :
    m • a = (m.1 • a.1, m.2 • a.2) := rfl

@[to_additive]
instance instFaithfulSMul  [SMul M₁ α₁] [SMul M₂ α₂] [Nonempty α₁] [Nonempty α₂]
    [FaithfulSMul M₁ α₁] [FaithfulSMul M₂ α₂]:
    FaithfulSMul (M₁ × M₂) (α₁ × α₂) where
  eq_of_smul_eq_smul {m n} h := by
    simp_rw [eq_iff_fst_eq_snd_eq] at h ⊢
    constructor
    · apply @FaithfulSMul.eq_of_smul_eq_smul _ α₁ _ _ m.1 n.1
      intro a₁
      refine Nonempty.elim ‹_› fun a₂ => (h ⟨a₁, a₂⟩).1
    · apply @FaithfulSMul.eq_of_smul_eq_smul _ α₂ _ _ m.2 n.2
      intro a₂
      refine Nonempty.elim ‹_› fun a₁ => (h ⟨a₁, a₂⟩).2

@[to_additive]
instance instMulAction [Monoid M₁] [Monoid M₂] [MulAction M₁ α₁] [MulAction M₂ α₂] :
    MulAction (M₁ × M₂) (α₁ × α₂) where
  one_smul a := show ⟨1 • a.1, 1 • a.2⟩ = a by simp
  mul_smul m1 m2 a :=
    show Prod.mk ((m1 * m2).1 • a.1) ((m1 * m2).2 • a.2) = ⟨m1.1 • m2.1 • a.1, m1.2 • m2.2 • a.2⟩
    by simp [mul_smul]

end Prod

namespace MulAction

variable [Monoid M₁] [Monoid M₂] [MulAction M₁ α₁] [MulAction M₂ α₂]

@[to_additive]
lemma mem_fixedPoints_prod (a₁ : α₁) (a₂ : α₂) :
    (a₁, a₂) ∈ fixedPoints (M₁ × M₂) (α₁ × α₂) ↔
      a₁ ∈ fixedPoints M₁ α₁ ∧ a₂ ∈ fixedPoints M₂ α₂ := by
  simp [forall_and_left, forall_and_right]

@[to_additive]
lemma fixedPoints_prod :
    fixedPoints (M₁ × M₂) (α₁ × α₂) = (fixedPoints M₁ α₁) ×ˢ (fixedPoints M₂ α₂) :=
  Set.ext fun _ => mem_fixedPoints_prod ..

@[to_additive]
lemma stabilizerSubmonoid_prod (a₁ : α₁) (a₂ : α₂) :
    stabilizerSubmonoid (M₁ × M₂) (a₁, a₂) =
      (stabilizerSubmonoid M₁ a₁ : Set M₁) ×ˢ (stabilizerSubmonoid M₂ a₂) := by
  ext ⟨_, _⟩
  simp

variable (M₁ M₂) in
@[to_additive]
def mulEquivProdStabilizerSubmonoid (a₁ : α₁) (a₂ : α₂) :
    stabilizerSubmonoid M₁ a₁ × stabilizerSubmonoid M₂ a₂ ≃*
      stabilizerSubmonoid (M₁ × M₂) (a₁, a₂) where
  toFun m := by
    refine ⟨⟨m.1.val, m.2.val⟩, ?_⟩
    simpa using ⟨m.1.property, m.2.property⟩
  invFun m := by
    obtain ⟨m, hm⟩ := m
    simp only [mem_stabilizerSubmonoid_iff, Prod.smul'_def, Prod.mk.injEq] at hm
    exact ⟨⟨m.1, hm.1⟩, ⟨m.2, hm.2⟩⟩
  left_inv _ := by simp
  right_inv _ := by simp
  map_mul' x y := by simp

variable [Finite M₁] [Finite M₂]

@[to_additive]
lemma mlii_prod_comm :
    mlii (M₁ × M₂) (α₁ × α₂) = mlii (M₂ × M₁) (α₂ × α₁) :=
  mlii_eq_of_bijective_mulActionHom
    MulEquiv.prodComm ⟨Prod.swap, by simp⟩ Prod.swap_bijective

variable (M₁ M₂ α₁ α₂) in
@[to_additive]
lemma mlii_prod_ge_left [Nonempty α₂] :
    mlii M₁ α₁ ≤ mlii (M₁ × M₂) (α₁ × α₂) :=
  Nonempty.elim ‹_› fun a₂ => mlii_le_of_mulActionHom
    (MonoidHom.inl M₁ M₂)
    (fun _ _ => by simp)
    ⟨fun a₁ => (a₁, a₂), by simp⟩
    (fun _ _ => And.left ∘ Prod.eq_iff_fst_eq_snd_eq.mp)

variable (M₁ M₂ α₁ α₂) in
@[to_additive]
lemma mlii_prod_ge_right [Nonempty α₁] :
    mlii M₂ α₂ ≤ mlii (M₁ × M₂) (α₁ × α₂) :=  by
  rw [mlii_prod_comm]
  exact mlii_prod_ge_left ..

variable (M₁ M₂) in
@[to_additive]
lemma mlii_stabilizerSubmonoid_prod_eq (a₁ : α₁) (a₂ : α₂) :
    mlii ((stabilizerSubmonoid M₁ a₁) × (stabilizerSubmonoid M₂ a₂)) (α₁ × α₂) =
      mlii (stabilizerSubmonoid (M₁ × M₂) (a₁, a₂)) (α₁ × α₂) :=
  mlii_eq_of_bijective_mulActionHom (α₂ := α₁ × α₂)
    (mulEquivProdStabilizerSubmonoid M₁ M₂ a₁ a₂)
    (by use id; simp [mulEquivProdStabilizerSubmonoid])
    Function.bijective_id

variable [Nonempty α₁] [Nonempty α₂]

@[to_additive]
lemma mlii_prod_le (M₁ M₂ α₁ α₂ : Type*)
    [Monoid M₁] [Monoid M₂] [MulAction M₁ α₁] [MulAction M₂ α₂] [Finite M₁] [Finite M₂]
    [Nonempty α₁] [Nonempty α₂] [FaithfulSMul M₁ α₁] [FaithfulSMul M₂ α₂] :
    mlii (M₁ × M₂) (α₁ × α₂) ≤ (mlii M₁ α₁) + (mlii M₂ α₂) := by
  by_cases h : Nontrivial (M₁ × M₂)
  · refine mlii_le fun as h1 => ?_
    refine Nat.eq_zero_or_pos as.length |>.elim (fun h2 => h2 ▸ Nat.zero_le _) fun h2 => ?_
    obtain ⟨⟨a₁, a₂⟩, as, rfl⟩ := List.exists_cons_of_length_pos h2
    rw [List.length_cons, Nat.succ_le]
    obtain ⟨h11, h12⟩ := isIrredundant_cons.mp h1
    have eq := mlii_stabilizerSubmonoid_prod_eq M₁ M₂ a₁ a₂
    replace h12 := length_le_mlii as h12
    refine lt_of_le_of_lt (h12.trans <| eq ▸ mlii_prod_le ..) ?_
    rw [stabilizerSubmonoid_lt_top_iff_notin_fixedPoints, mem_fixedPoints_prod, not_and_or] at h11
    obtain h' | h' := h11
    <;> have := mlii_stabilizerSubmonoid_lt h'
    · exact Nat.add_lt_add_of_lt_of_le this <| mlii_submonoid_le _
    · exact Nat.add_lt_add_of_le_of_lt (mlii_submonoid_le _) this
  · rw [not_nontrivial_iff_subsingleton] at h
    rw [subsingleton_iff_mlii_eq_zero .. |>.mp h]
    exact Nat.zero_le _
  termination_by Nat.card M₁ + Nat.card M₂
  decreasing_by
    rw [stabilizerSubmonoid_lt_top_iff_notin_fixedPoints, mem_fixedPoints_prod, not_and_or] at h11
    obtain h' | h' := h11
    <;> have := stabilizerSubmonoid_lt_top_iff_notin_fixedPoints.mpr h'
    refine Nat.add_lt_add_of_lt_of_le ?_ (Finite.card_subtype_le _)
    swap; refine Nat.add_lt_add_of_le_of_lt (Finite.card_subtype_le _) ?_
    all_goals convert (Set.toFinite ⊤).card_lt_card this using 1; exact Nat.card_univ.symm

@[to_additive]
lemma mlii_prod_le' [FaithfulSMul M₁ α₁] [FaithfulSMul M₂ α₂]
    (h1 : fixedPoints M₁ α₁ = ∅) (h2 : fixedPoints M₂ α₂ = ∅) :
    mlii (M₁ × M₂) (α₁ × α₂) ≤ (mlii M₁ α₁) + (mlii M₂ α₂) - 1 := by
  refine mlii_le' fun as h3 h4 => ?_
  obtain ⟨⟨a₁, a₂⟩, as, rfl⟩ := List.exists_cons_of_length_pos h3
  replace h1 := mlii_stabilizerSubmonoid_lt (h1 ▸ Set.not_mem_empty a₁)
  replace h2 := mlii_stabilizerSubmonoid_lt (h2 ▸ Set.not_mem_empty a₂)
  have eq := mlii_stabilizerSubmonoid_prod_eq M₁ M₂ a₁ a₂
  replace h4 := length_le_mlii as (isIrredundant_cons.mp h4).2
  replace h4 := h4.trans <| eq ▸ mlii_prod_le ..
  refine Nat.le_sub_one_of_lt <| lt_of_le_of_lt ?_ <|
    Nat.add_lt_add_of_lt_of_le h1 (Nat.lt_iff_add_one_le.mp h2)
  rw [List.length_cons, ← add_assoc]
  exact Nat.succ_le_succ h4

@[to_additive]
lemma mlii_prod_ge_of_left (M₁ M₂ α₁ α₂ : Type*)
    [Monoid M₁] [Monoid M₂] [MulAction M₁ α₁] [MulAction M₂ α₂] [Finite M₁] [Finite M₂]
    [Nonempty α₁] [Nonempty α₂] (h : (fixedPoints M₁ α₁).Nonempty) :
    (mlii M₁ α₁) + (mlii M₂ α₂) ≤ mlii (M₁ × M₂) (α₁ × α₂) := by
  obtain h2 | h2 := Nat.eq_zero_or_pos (mlii M₂ α₂)
  · rw [h2, Nat.add_zero]
    exact Nonempty.elim ‹_› fun (a₂ : α₂) => mlii_prod_ge_left M₁ M₂ α₁ α₂
  · obtain ⟨a₂, ha₂, h3⟩ := exists_mlii_stabilizerSubmonoid_add_one_eq h2
    rw [← h3, ← add_assoc, Nat.add_one_le_iff]
    have ⟨a₁, ha₁⟩ := h
    have eq1 := mlii_stabilizerSubmonoid_eq ha₁
    refine eq1 ▸ Nat.lt_of_le_of_lt (mlii_prod_ge_of_left _ _ _ _ ?_) ?_
    · exact Set.Nonempty.mono (subset_fixedPoints_stabilizerSubmonoid a₁) h
    have eq2 := mlii_stabilizerSubmonoid_prod_eq M₁ M₂ a₁ a₂
    exact eq2 ▸ mlii_stabilizerSubmonoid_lt (by simp_all)
  termination_by Nat.card M₂
  decreasing_by
    refine Nat.card_univ (α := M₂) ▸ Set.Finite.card_lt_card (Set.toFinite ⊤) ?_
    exact stabilizerSubmonoid_lt_top_iff_notin_fixedPoints.mpr ha₂

variable (M₁ M₂ α₁ α₂) in
@[to_additive]
lemma mlii_prod_ge_of_right (h : (fixedPoints M₂ α₂).Nonempty) :
    (mlii M₁ α₁) + (mlii M₂ α₂) ≤ mlii (M₁ × M₂) (α₁ × α₂) := by
  rw [add_comm, mlii_prod_comm]
  exact mlii_prod_ge_of_left M₂ M₁ α₂ α₁ h

@[to_additive]
lemma mlii_prod_ge :
    (mlii M₁ α₁) + (mlii M₂ α₂) - 1 ≤ mlii (M₁ × M₂) (α₁ × α₂) := by
  obtain h | h1 := Nat.eq_zero_or_pos (mlii M₁ α₁)
  · rw [h, Nat.zero_add]
    exact le_trans (Nat.sub_le _ 1) (mlii_prod_ge_right ..)
  obtain h | h2 := Nat.eq_zero_or_pos (mlii M₂ α₂)
  · rw [h, Nat.add_zero]
    exact le_trans (Nat.sub_le _ 1) (mlii_prod_ge_left ..)
  obtain ⟨a₁, ha₁, h1⟩ := exists_mlii_stabilizerSubmonoid_add_one_eq h1
  obtain ⟨a₂, ha₂, h2⟩ := exists_mlii_stabilizerSubmonoid_add_one_eq h2
  rw [← h1, ← h2, Nat.add_succ_sub_one, add_assoc, add_comm 1, ← add_assoc, Nat.add_one_le_iff]
  refine Nat.lt_of_le_of_lt ?_ (mlii_stabilizerSubmonoid_lt (a := (a₁, a₂)) ?_)
  · rw [← mlii_stabilizerSubmonoid_prod_eq]
    exact mlii_prod_ge_of_left _ _ _ _ ⟨a₁, by simp⟩
  · rw [mem_fixedPoints_prod, not_and_or]
    exact Or.inl ha₁

@[to_additive]
theorem mlii_prod_eq_of_fixedPoints_eq_empty [FaithfulSMul M₁ α₁] [FaithfulSMul M₂ α₂]
    (h1 : fixedPoints M₁ α₁ = ∅) (h2 : fixedPoints M₂ α₂ = ∅) :
    mlii (M₁ × M₂) (α₁ × α₂) = (mlii M₁ α₁) + (mlii M₂ α₂) - 1 :=
  Nat.le_antisymm (mlii_prod_le' h1 h2) (mlii_prod_ge ..)

@[to_additive]
theorem mlii_prod_eq_of_nonempty_fixedPoints_left
    [FaithfulSMul M₁ α₁] [FaithfulSMul M₂ α₂] (h : (fixedPoints M₁ α₁).Nonempty) :
    mlii (M₁ × M₂) (α₁ × α₂) = (mlii M₁ α₁) + (mlii M₂ α₂) :=
  Nat.le_antisymm (mlii_prod_le ..) <|
    mlii_prod_ge_of_left _ _ _ _ h

@[to_additive]
theorem mlii_prod_eq_of_nonempty_fixedPoints_right
    [FaithfulSMul M₁ α₁] [FaithfulSMul M₂ α₂] (h : (fixedPoints M₂ α₂).Nonempty) :
    mlii (M₁ × M₂) (α₁ × α₂) = (mlii M₁ α₁) + (mlii M₂ α₂) :=
  Nat.le_antisymm (mlii_prod_le ..) <|
    mlii_prod_ge_of_right _ _ _ _ h

end MulAction
