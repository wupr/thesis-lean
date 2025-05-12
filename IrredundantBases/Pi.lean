import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset

import IrredundantBases.Prod

variable {ι : Type*} {M α : (i : ι) → Type*} [∀ i, Monoid (M i)]

def Finset.PiEquivPiUniv [Fintype ι] [DecidableEq ι] :
    ((i : ι) → α i) ≃ ((i : Finset.univ (α := ι)) → α i) where
  toFun a i := a i.val
  invFun a i := a ⟨i, Finset.mem_univ i⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simps]
def Finset.PiInsertEquivProdPi [Fintype ι] [DecidableEq ι] (i : ι) (s : Finset ι) (h : i ∉ s) :
    ((j : { x // x ∈ insert i s }) → α j) ≃ α i × ((j : { x // x ∈ s }) → α j) where
  toFun a := ⟨a ⟨i, s.mem_insert_self i⟩, Finset.restrict₂ (s.subset_insert i) a⟩
  invFun a j := if hji : j.val = i
    then Eq.ndrec (motive := fun i ↦ α i → α j) id hji a.fst
    else a.snd ⟨j.val, Finset.mem_of_mem_insert_of_ne j.property hji⟩
  left_inv x := by
    ext ⟨j, hj⟩
    if hji : j = i then subst hji; simp else simp [hji]
  right_inv x := by
    refine Prod.eq_iff_fst_eq_snd_eq.mpr ⟨by simp, ?_⟩
    ext ⟨j, hj⟩
    simp [ne_of_mem_of_not_mem hj h]

open MulAction

instance Pi.instFaithfulSMul' [∀ i, SMul (M i) (α i)] [∀ (i : ι), Nonempty (α i)]
    [∀ (i : ι), FaithfulSMul (M i) (α i)] [DecidableEq ι] :
    FaithfulSMul ((i : ι) → M i) ((i : ι) → α i) where
  eq_of_smul_eq_smul {x y} h := by
    simp_rw [Pi.smul_def', funext_iff] at h
    ext i
    refine Nonempty.elim (by infer_instance) fun (a : (i : ι) → α i) => ?_
    refine FaithfulSMul.eq_of_smul_eq_smul (α := α i) ?_
    intro b
    let a' (j : ι) : α j :=
      if hji : j = i then Eq.ndrec (motive := fun i ↦ α i → α j) id hji b else a j
    have : a' i = b := (Ne.dite_eq_left_iff fun h _ ↦ h rfl).mpr rfl
    exact this ▸ h a' i

variable [∀ i, MulAction (M i) (α i)]

lemma fixedPoints_pi [DecidableEq ι] :
    fixedPoints ((i : ι) → M i) ((i : ι) → α i) =
    Set.pi Set.univ fun i => fixedPoints (M i) (α i) := by
  ext a
  simp only [mem_fixedPoints, Set.mem_pi, Set.mem_univ, forall_const]
  refine ⟨fun h i m => ?_, fun h m => ?_⟩
  · let m' (j : ι) : M j :=
      if hji : j = i then Eq.ndrec (motive := fun i ↦ M i → M j) id hji m else 1
    have : m' i = m := (Ne.dite_eq_left_iff fun h _ ↦ h rfl).mpr rfl
    exact this ▸ congrFun (h m') i
  · ext i
    exact h i (m i)

lemma fixedPoints_pi_eq_empty [DecidableEq ι]
    {s : Finset ι} (hs : s.Nonempty) (h : ∀ a ∈ s, fixedPoints (M a) (α a) = ∅) :
    fixedPoints ((i : s) → M ↑i) ((i : s) → α i) = ∅ := by
  rw [fixedPoints_pi]
  obtain ⟨i, hi⟩ := hs
  exact Set.univ_pi_eq_empty (i := ⟨i, hi⟩) (h i hi)

variable [∀ (i : ι), Finite (M i)]

lemma mlii_pi_empty_eq_zero :
    mlii ((i : (∅ : Finset ι)) → M i) ((i : (∅ : Finset ι)) → α i) = 0 := by
  refine @subsingleton_iff_mlii_eq_zero _ _ _ _ _ ?h' |>.mp Unique.instSubsingleton
  exact FaithfulSMul.mk fun _ => Subsingleton.elim ..

variable (M α) in
lemma mlii_pi_insert_eq [Fintype ι] [DecidableEq ι] {i : ι} {s : Finset ι} (h : i ∉ s) :
  mlii ((j : { x // x ∈ insert i s }) → M j) ((j : { x // x ∈ insert i s }) → α j) =
    mlii (M i × ((i : { x // x ∈ s }) → M i)) (α i × ((i : { x // x ∈ s }) → α i)) := by
  refine mlii_eq_of_bijective_mulActionHom ?φ ?f ?hf
  case φ => exact MulEquiv.mk (s.PiInsertEquivProdPi i h) (fun _ _ => rfl)
  case f => exact MulActionHom.mk (s.PiInsertEquivProdPi i h) (fun _ _ => rfl)
  case hf => exact Equiv.bijective _

variable (M α) in
lemma mlii_pi_eq_mlii_pi_univ [Fintype ι] [DecidableEq ι] :
    mlii ((i : ι) → M i) ((i : ι) → α i) =
      mlii ((i : (Finset.univ : Finset ι)) → M i) ((i : (Finset.univ : Finset ι)) → α i) := by
  refine mlii_eq_of_bijective_mulActionHom ?φ ?f ?hf
  case φ => exact MulEquiv.mk Finset.PiEquivPiUniv (fun _ _ => rfl)
  case f => exact MulActionHom.mk Finset.PiEquivPiUniv (fun _ _ => rfl)
  case hf => exact Equiv.bijective _

variable [∀ (i : ι), Nonempty (α i)] [∀ (i : ι), FaithfulSMul (M i) (α i)]
  [Fintype ι] [DecidableEq ι]

lemma mlii_pi_eq_of_fixedPoints_nonempty' (s : Finset ι)
    (h : ∀ i ∈ s, (fixedPoints (M i) (α i)).Nonempty):
    mlii ((i : s) → M i) ((i : s) → α i) = ∑ i ∈ s, mlii (M i) (α i) := by
  induction' s using Finset.induction with i s hi ih
  · rw [Finset.sum_empty, mlii_pi_empty_eq_zero]
  · rw [Finset.sum_insert hi]
    simp only [Finset.mem_insert, forall_eq_or_imp] at h
    convert ih h.2 ▸ mlii_prod_eq_of_nonempty_fixedPoints_left h.1 using 1
    exact mlii_pi_insert_eq M α hi

lemma mlii_pi_eq_of_fixedPoints_nonempty (h : ∀ i, (fixedPoints (M i) (α i)).Nonempty) :
    mlii ((i : ι) → M i) ((i : ι) → α i) = ∑ i, mlii (M i) (α i) :=
  mlii_pi_eq_mlii_pi_univ M α ▸ mlii_pi_eq_of_fixedPoints_nonempty' Finset.univ (fun i _ ↦ h i)

lemma mlii_pi_eq_of_fixedPoints_eq_empty' (s : Finset ι)
    (h : ∀ i ∈ s, fixedPoints (M i) (α i) = ∅):
    mlii ((i : s) → M i) ((i : s) → α i) = ∑ i ∈ s, mlii (M i) (α i) - (s.card - 1) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [mlii_pi_empty_eq_zero]
  induction' hs using Finset.Nonempty.cons_induction with i i t hi ht ih
  · simp only [Finset.sum_singleton, Finset.card_singleton, tsub_self, tsub_zero]
    refine mlii_eq_of_bijective_mulActionHom ?φ ?f ?hf
    · exact MulEquiv.piUnique <| fun (j : ({i} : Finset ι)) => M j
    · use Equiv.piUnique <| fun (j : ({i} : Finset ι)) => α j
      intro m a
      rfl
    · exact Equiv.bijective _
  · rw [Finset.cons_eq_insert, Finset.sum_insert hi]
    simp only [Finset.cons_eq_insert, Finset.mem_insert, forall_eq_or_imp] at h
    have h3 : t.card ≤ ∑ x ∈ t, mlii (M x) (α x)
    · rw [Finset.card_eq_sum_ones]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [Order.one_le_iff_pos, ← nontrivial_iff_mlii_pos]
      exact nontrivial_of_fixedPoints_eq_empty <| h.2 i hi
    have := ih h.2 ▸ mlii_prod_eq_of_fixedPoints_eq_empty h.1 (fixedPoints_pi_eq_empty ht h.2)
    rw [Finset.card_insert_of_not_mem hi, Nat.add_sub_assoc (Nat.add_sub_cancel .. ▸ h3),
      Nat.sub_add_comm (Finset.one_le_card.mpr ht)]
    rw [Nat.add_sub_assoc ?hrw, Nat.sub_sub] at this
    exact mlii_pi_insert_eq M α hi ▸ this
    case hrw =>
      rw [Order.one_le_iff_pos, Nat.sub_pos_iff_lt]
      exact Nat.sub_one_lt_of_le (Finset.card_pos.mpr ht) h3

lemma mlii_pi_eq_of_fixedPoints_eq_empty (h : ∀ i, fixedPoints (M i) (α i) = ∅):
    mlii ((i : ι) → M i) ((i : ι) → α i) = ∑ i, mlii (M i) (α i) - (Fintype.card ι - 1) :=
  mlii_pi_eq_mlii_pi_univ M α ▸ mlii_pi_eq_of_fixedPoints_eq_empty' Finset.univ (fun i _ ↦ h i)
