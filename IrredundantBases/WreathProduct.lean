import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.Algebra.Equiv.TransferInstance
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Perm
import Mathlib.SetTheory.Cardinal.Finite

import IrredundantBases.MulAction
import IrredundantBases.MulActionHom
import IrredundantBases.Perm
import IrredundantBases.Pi
import IrredundantBases.Subgroup

@[ext]
structure WreathProduct (G H β : Type*) : Type _ where
  mk ::
  top : H
  func : β → G

@[ext]
structure AddWreathProduct (G H β : Type*) : Type _ where
  mk ::
  top : H
  func : β → G

attribute [to_additive existing AddWreathProduct] WreathProduct

variable {G H α β : Type*}

namespace WreathProduct

section Card

@[to_additive (attr := simps)]
def equivProdPi : WreathProduct G H β ≃ H × (β → G) where
  toFun x := ⟨x.top, x.func⟩
  invFun x := ⟨x.fst, x.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[to_additive (attr := simp)]
lemma card [Finite G] [Finite H] [Finite β] :
    Nat.card (WreathProduct G H β) = Nat.card (H × (β → G)) :=
  Nat.card_congr <| equivProdPi

@[to_additive]
instance [Finite G] [Finite H] [Finite β] : Finite (WreathProduct G H β) :=
  Finite.of_equiv _ (equivProdPi.symm)

@[to_additive]
instance [IsEmpty β] [Subsingleton H] : Subsingleton (WreathProduct G H β) :=
  Equiv.subsingleton_congr equivProdPi |>.mpr instSubsingletonProd

@[to_additive]
instance [Nonempty G] [Nontrivial H] : Nontrivial (WreathProduct G H β) :=
  Equiv.nontrivial equivProdPi

@[to_additive]
theorem nonempty_of_faithfulSMul_of_nontrivial [SMul H β] [FaithfulSMul H β]
    (h : Nontrivial (WreathProduct G H β)) :
    Nonempty β := by
  contrapose h
  rw [not_nonempty_iff] at h
  have : Subsingleton H
  · exact ⟨fun x y => @FaithfulSMul.eq_of_smul_eq_smul _ β _ _ x y (by simp)⟩
  rw [not_nontrivial_iff_subsingleton]
  infer_instance

end Card

section One

variable [One G] [One H]

@[to_additive]
instance : One (WreathProduct G H β) where
  one := ⟨1, fun _ => 1⟩

@[to_additive]
lemma one_def : (1 : WreathProduct G H β) = ⟨1, fun _ => 1⟩ := rfl

@[to_additive]
lemma one_def' : (1 : WreathProduct G H β) = ⟨1, 1⟩ := rfl

@[to_additive (attr := simp)]
lemma func_one : func (1 : WreathProduct G H β) = 1 := rfl

@[to_additive (attr := simp)]
lemma top_one : top (1 : WreathProduct G H β) = 1 := rfl

end One

section Mul

variable [Mul G] [Mul H] [SMul H β]

@[to_additive]
instance : Mul (WreathProduct G H β) where
  mul x y := ⟨x.top * y.top, fun b => x.func (y.top • b) * y.func b⟩

@[to_additive]
lemma mul_def (x y : WreathProduct G H β) :
    x * y = ⟨x.top * y.top, fun b ↦ x.func (y.top • b) * y.func b⟩ :=
  rfl

@[to_additive (attr := simp)]
lemma func_mul (x y : WreathProduct G H β) :
    (x * y).func = fun b ↦ x.func (y.top • b) * y.func b :=
  rfl

@[to_additive (attr := simp)]
lemma top_mul (x y : WreathProduct G H β) : (x * y).top = x.top * y.top := rfl

end Mul

section Inv

variable [Inv G] [Inv H] [SMul H β]

@[to_additive]
instance : Inv (WreathProduct G H β) where
  inv x := ⟨x.top⁻¹, fun b => (x.2 (x.1⁻¹ • b))⁻¹⟩

@[to_additive]
lemma inv_def (x : WreathProduct G H β) :
    x⁻¹ = ⟨x.top⁻¹, fun b ↦ (x.func (x.top⁻¹ • b))⁻¹⟩ :=
  rfl

@[to_additive (attr := simp)]
lemma func_inv (x : WreathProduct G H β) :
    x⁻¹.func = fun b ↦ (x.func (x.top⁻¹ • b))⁻¹ :=
  rfl

@[to_additive (attr := simp)]
lemma top_inv (x : WreathProduct G H β) : x⁻¹.top = x.top⁻¹ := rfl

end Inv

section Group

variable [Group G] [Group H] [MulAction H β]

@[to_additive]
instance : Group (WreathProduct G H β) where
  mul_assoc x y z := by simp [mul_def, mul_assoc, mul_smul]
  one_mul x := by simp [one_def, mul_def]
  mul_one x := by simp [one_def, mul_def]
  inv_mul_cancel x := by simp [mul_def, one_def, inv_def]

@[to_additive (attr := simps)]
def include_func :
    (β → G) →* WreathProduct G H β where
  toFun f := ⟨1, f⟩
  map_one' := rfl
  map_mul' x y := by simp [mul_def, Pi.mul_def]

@[to_additive]
lemma include_func_injective :
    Function.Injective (include_func : (β → G) → WreathProduct G H β) := by
  intro x y h
  cases h
  rfl

@[to_additive (attr := simps)]
def include_top : H →* WreathProduct G H β where
  toFun h := ⟨h, fun _ => 1⟩
  map_one' := rfl
  map_mul' x y := by simp [mul_def]

@[to_additive]
lemma include_top_injective :
    Function.Injective (include_top : H → WreathProduct G H β) := by
  intro x y h
  cases h
  rfl

end Group

section Properties

@[to_additive (attr := simps)]
def congr [Monoid G] [Monoid H] [MulAction H β]
    {G' H' β': Type*} [Monoid G'] [Monoid H'] [MulAction H' β']
    (f1 : G ≃* G') (f2 : H ≃* H') (f3 : β ≃ β') (h : ∀ (x : H) (b : β), f3 (x • b) = f2 x • f3 b) :
    WreathProduct G H β ≃* WreathProduct G' H' β' where
  toFun x := ⟨f2 x.top, f1 ∘ x.func ∘ f3.symm⟩
  invFun x := ⟨f2.symm x.top, f1.symm ∘ x.func ∘ f3⟩
  map_mul' x y := by
    ext b'
    · simp only [top_mul, map_mul]
    · simp only [func_mul, Function.comp_apply, map_mul]
      have := h y.top (f3.symm b')
      rw [Equiv.apply_symm_apply] at this
      congr
      rwa [Equiv.eq_symm_apply]
  left_inv _ := by ext _ <;> simp
  right_inv _ := by ext _ <;> simp

end Properties

section SMul

variable [Inv H] [SMul G α] [SMul H β]

@[to_additive]
instance : SMul (WreathProduct G H β) (β → α) where
  smul x f b := (x.func • f) (x.top⁻¹ • b)

@[to_additive]
lemma smul_apply' (x : WreathProduct G H β) (f : β → α) (b : β) :
    (x • f) b = (x.func • f) (x.top⁻¹ • b) :=
  rfl

@[to_additive]
lemma smul_apply (x : WreathProduct G H β) (f : β → α) (b : β) :
    (x • f) b = (x.func (x.top⁻¹ • b)) • f (x.top⁻¹ • b) :=
  rfl

@[to_additive (attr := simp)]
lemma smul_mk_apply (h : H) (φ : β → G) (f : β → α) (b : β) :
    (mk h φ • f) b = (φ (h⁻¹ • b)) • f (h⁻¹ • b) := by
  rfl

end SMul

section MulAction

variable [Group G] [Group H] [MulAction G α] [MulAction H β]

@[to_additive]
instance : MulAction (WreathProduct G H β) (β → α) where
  one_smul f := by
    ext b
    simp [smul_apply]
  mul_smul x y f := by
    ext b
    simp [smul_apply, smul_smul]

open MulAction

@[to_additive]
instance [DecidableEq β] [Nontrivial α] [FaithfulSMul G α] [FaithfulSMul H β] :
    FaithfulSMul (WreathProduct G H β) (β → α) := FaithfulSMul.mk' fun x h => by
  obtain ⟨y, φ⟩ := x
  have : φ = 1
  · ext b
    apply FaithfulSMul.eq_of_smul_eq_smul (α := α)
    intro a
    simpa using congrFun (h (fun _ => a)) (y • b)
  subst this
  simp only [one_def', mk.injEq, and_true]
  apply FaithfulSMul.eq_of_smul_eq_smul (α := β)
  intro b
  rw [one_smul]
  obtain ⟨a, a', h'⟩ := exists_pair_ne α
  let f : β → α := fun b' => if b' = b then a else a'
  have := congrFun (h f).symm (y • b)
  simpa [Ne.ite_eq_left_iff h', f]

@[to_additive]
instance [Fintype G] [DecidableEq α] : DecidableRel (orbitRel G α) := fun _ _ => by
  rw [orbitRel_apply, mem_orbit_iff]
  exact Fintype.decidableExistsFintype

@[to_additive]
lemma mem_orbit_of_apply_mem_orbit (f f' : β → α) (h : ∀ b : β, f' b ∈ orbit G (f b)):
    f' ∈ orbit (WreathProduct G H β) f := by
  use ⟨1, fun b => (h b).choose⟩
  ext b
  simp [(h b).choose_spec]

end MulAction


variable [Group G] [Group H] [MulAction G α] [MulAction H β]
variable {f : β → α}

open MulAction

variable (G f) in
abbrev COR : Setoid β := (orbitRel G α).comap f

variable (G f) in
abbrev QCOR : Type _ := Quotient ((orbitRel G α).comap f)

def QCOR.class (q : QCOR G f) : Set β := { b | ⟦b⟧ = q}

namespace QCOR

instance [Nonempty β] : Nonempty (QCOR G f) := by
  rwa [nonempty_quotient_iff]

instance [DecidableRel (orbitRel G α)] [Fintype β] : Fintype (QCOR G f) := Quotient.fintype _

instance [DecidableRel (orbitRel G α)] [Fintype β] : DecidableEq (QCOR G f) := Quotient.decidableEq

lemma mem_class_iff {q : QCOR G f} {b : β} : b ∈ q.class ↔ ⟦b⟧ = q := Iff.rfl

lemma mk_eq_mk_iff {b₁ b₂ : β} : (⟦b₁⟧ : QCOR G f) = ⟦b₂⟧ ↔ orbitRel G α (f b₁) (f b₂) := by
  rw [Quotient.eq]; rfl

lemma class_mk_eq (b : β) : QCOR.class (⟦b⟧ : QCOR G f) = f ⁻¹' orbit G (f b) := by
  ext b'
  rw [mem_class_iff, mk_eq_mk_iff]
  rfl

@[simp]
lemma mk_subtype_val_eq {q : QCOR G f} {b : q.class} : ⟦b.val⟧ = q := b.property

instance [DecidableRel (orbitRel G α)] (q : QCOR G f) : DecidablePred (· ∈ q.class) :=
  fun _ => decidable_of_iff' _ mem_class_iff

variable (G f) in
def piEquivPiQCORPiClass (γ : Type*) : (β → γ) ≃ ((q : QCOR G f) → (q.class → γ)) where
  toFun f' _ b := f' b
  invFun f' b := f' (⟦b⟧ : QCOR G f) ⟨b, rfl⟩
  left_inv f' := rfl
  right_inv f' := by ext _ ⟨_, rfl⟩; rfl

variable (G f) in
lemma sum_card_class_eq [DecidableRel (orbitRel G α)] [Fintype β] :
    ∑ (q : QCOR G f), Fintype.card q.class = Fintype.card β := by
  simp_rw [Fintype.card_eq_sum_ones]
  convert Fintype.sum_fiberwise (fun b => (⟦b⟧ : QCOR G f)) (fun _ => (1 : ℕ))

noncomputable def repr (q : QCOR G f) : β := q.exists_rep.choose

@[simp]
lemma repr_spec (q : QCOR G f) : ⟦q.repr⟧ = q := q.exists_rep.choose_spec

lemma repr_mem_class (q : QCOR G f) : q.repr ∈ q.class := q.repr_spec

instance {q : QCOR G f} : Nonempty q.class := ⟨q.repr, q.repr_spec⟩

lemma eq_of_class_eq_class {q₁ q₂ : QCOR G f} (h : q₁.class = q₂.class) : q₁ = q₂ := by
  rw [← repr_spec q₁, ← mem_class_iff, ← h, mem_class_iff]
  exact q₁.repr_spec

lemma orbitRel_comap_repr_mk (b : β) : orbitRel G α (f <| QCOR.repr (⟦b⟧ : QCOR G f)) (f b) := by
  rw [← mk_eq_mk_iff]
  exact repr_spec ⟦b⟧

lemma card_class_lt_of_nontrivial [DecidableRel (orbitRel G α)] [Fintype β]
    {f : β → α} [Nontrivial (QCOR G f)] (q : QCOR G f) :
    Fintype.card q.class < Fintype.card β := by
  obtain ⟨q', hq'⟩ := exists_ne q
  refine Fintype.card_subtype_lt (x := q'.repr) ?_
  simpa [mem_class_iff] using hq'

end QCOR

section CanonicalPoint

variable (G f) in
noncomputable def canonicalPoint : β → α := fun b => (f (QCOR.repr (⟦b⟧ : QCOR G f)))

lemma canonicalPoint_apply (b : β) : canonicalPoint G f b = (f (QCOR.repr (⟦b⟧ : QCOR G f))) :=
  rfl

lemma canonicalPoint_apply_mem_orbit (b : β) : canonicalPoint G f b ∈ orbit G (f b) :=
  QCOR.orbitRel_comap_repr_mk b

lemma canonicalPoint_apply_repr_mk_repr_mem_orbit (q : QCOR G f) :
    canonicalPoint G f (QCOR.repr (⟦q.repr⟧ : QCOR G (canonicalPoint G f))) ∈
      orbit G (f q.repr) := by
  rw [← orbitRel_apply]
  refine Setoid.trans' _ ?_ (QCOR.orbitRel_comap_repr_mk q.repr)
  exact QCOR.orbitRel_comap_repr_mk q.repr

variable (G H f) in
lemma canonicalPoint_mem_orbit : canonicalPoint G f ∈ orbit (WreathProduct G H β) f :=
  mem_orbit_of_apply_mem_orbit _ _ <| canonicalPoint_apply_mem_orbit

lemma orbitRel_comap_canonicalPoint_iff {b₁ b₂ : β} :
    orbitRel G α (canonicalPoint G f b₁) (canonicalPoint G f b₂) ↔
      orbitRel G α (f b₁) (f b₂) := by
    simp [canonicalPoint_apply, ← QCOR.mk_eq_mk_iff]

variable (G f) in
lemma canonicalPoint_property :
    ∀ b₁ b₂ : β, orbitRel G α (canonicalPoint G f b₁) (canonicalPoint G f b₂) →
      canonicalPoint G f b₁ = canonicalPoint G f b₂ :=
  fun b₁ b₂ => by simp_all [canonicalPoint_apply, ← QCOR.mk_eq_mk_iff, -Quotient.eq]

end CanonicalPoint

section StabilizerOfCanonicalPoint

lemma mem_stabilizer_wreathProduct_iff
    (h : ∀ b₁ b₂ : β, orbitRel G α (f b₁) (f b₂) → f b₁ = f b₂) (x : Equiv.Perm β) (φ : β → G) :
    ⟨x, φ⟩ ∈ stabilizer (WreathProduct _ _ _) f ↔
      ∀ b : β, φ b ∈ stabilizer G (f b) ∧ f (x b) = (f b) := by
  rw [mem_stabilizer_iff]
  refine ⟨fun h' b  => ?_, fun h' => funext fun b => ?_⟩
  · replace h' := congrFun h' (x b)
    rw [smul_mk_apply, Equiv.Perm.smul_def, Equiv.Perm.inv_apply_self] at h'
    specialize h _ _ ⟨_, h'⟩
    exact ⟨h ▸ h', h⟩
  · obtain ⟨h1, h2⟩ := h' (x⁻¹ b)
    rw [smul_mk_apply, Equiv.Perm.smul_def, h1, ← h2, Equiv.Perm.apply_inv_self]

@[simp]
lemma Equiv.Perm.inv_eq_symm (x : Equiv.Perm β) : x⁻¹ = x.symm := rfl

@[simps]
def restrictToQCOR (x : Equiv.Perm β) (h : ∀ b : β, f (x b) = (f b)) (q : QCOR G f) :
    Equiv.Perm q.class where
  toFun b := ⟨x b, by
    obtain ⟨b, rfl⟩ := b
    rw [QCOR.mem_class_iff, QCOR.mk_eq_mk_iff, h]
  ⟩
  invFun b := ⟨x⁻¹ b, by
    obtain ⟨b, rfl⟩ := b
    rw [QCOR.mem_class_iff, QCOR.mk_eq_mk_iff, ← h (x⁻¹ b), Equiv.Perm.apply_inv_self]
  ⟩
  left_inv _ := by simp
  right_inv _ := by simp

@[simps]
def combineOverQCOR (x : (q : QCOR G f) → Equiv.Perm q.class) : Equiv.Perm β where
  toFun b := (x ⟦b⟧) ⟨b, rfl⟩
  invFun b := (x ⟦b⟧).symm ⟨b, rfl⟩
  left_inv b := by
    have : ((x ⟦b⟧).symm ⟨(x ⟦b⟧) ⟨b, rfl⟩, Subtype.property _⟩) = b
    · simp only [Subtype.coe_eta, Equiv.symm_apply_apply]
    convert this using 5
    all_goals exact QCOR.mk_subtype_val_eq
  right_inv b := by
    have : ((x ⟦b⟧) ⟨(x ⟦b⟧).symm ⟨b, rfl⟩, Subtype.property _⟩) = b
    · simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
    convert this using 4
    all_goals rw [QCOR.mk_subtype_val_eq]

variable (G f) in
@[simps]
def stabilizerMulEquivPi (h : ∀ b₁ b₂ : β, orbitRel G α (f b₁) (f b₂) → f b₁ = f b₂) :
    stabilizer (WreathProduct G (Equiv.Perm β) β) f ≃* Π q : QCOR G f,
      WreathProduct (stabilizer G (f q.repr)) (Equiv.Perm q.class) q.class := by
  refine {
    toFun w := fun q => ⟨restrictToQCOR w.val.top ?_ q, fun b => ⟨w.val.func b, ?_⟩⟩
    invFun w := ⟨⟨combineOverQCOR <| fun q => (w q).top, fun b => (w ⟦b⟧).func ⟨b, rfl⟩⟩, ?_⟩
    left_inv w := rfl
    right_inv w := ?_
    map_mul' w₁ w₂ := rfl
  }
  · exact fun b => ((mem_stabilizer_wreathProduct_iff h _ _ |>.mp w.property) b).2
  · obtain ⟨b, hb⟩ := b
    convert ((mem_stabilizer_wreathProduct_iff h _ _ |>.mp w.property) b).1 using 2
    exact h _ _ <| hb ▸ QCOR.orbitRel_comap_repr_mk _
  · simp only [mem_stabilizer_iff]
    ext b
    simp only [smul_mk_apply, Equiv.Perm.inv_eq_symm, Equiv.Perm.smul_def]
    let b' := (combineOverQCOR fun q ↦ (w q).top).symm b
    have h1 : f b' = f b
    · apply h
      rw [orbitRel_apply, ← Set.mem_preimage, ← QCOR.class_mk_eq]
      simp [b']
    have h2 : f (QCOR.repr (⟦b'⟧ : QCOR G f)) = f b' := h _ _ <| QCOR.orbitRel_comap_repr_mk ..
    have ⟨φ, hφ⟩ := (w ⟦b'⟧).func ⟨b', rfl⟩
    erw [h1]
    simpa only [h2, h1, mem_stabilizer_iff] using hφ
  · ext _ ⟨_, rfl⟩ <;> rfl

end StabilizerOfCanonicalPoint

section MLIIStabilizer

lemma mlii_stabilizer_eq_sum_of_canonicalPoint [Finite G] [Fintype β]
    [DecidableRel (orbitRel G α)] [DecidableEq β] [Nontrivial α] [FaithfulSMul G α]
    (h : ∀ b₁ b₂ : β, orbitRel G α (f b₁) (f b₂) → f b₁ = f b₂) :
    mlii (stabilizer (WreathProduct G (Equiv.Perm β) β) f) (β → α) = ∑ q : QCOR G f, mlii
      (WreathProduct (stabilizer G (f q.repr)) (Equiv.Perm q.class) q.class) (q.class → α) := by
  have eq1 := mlii_eq_of_bijective_mulActionHom (stabilizerMulEquivPi G f h)
    ⟨QCOR.piEquivPiQCORPiClass G f α, fun _ _ => rfl⟩ (Equiv.bijective _)
  refine eq1.trans <| mlii_pi_eq_of_fixedPoints_nonempty ?_
  intro q
  use fun _ => f q.repr
  simp only [mem_fixedPoints]
  intro ⟨x, φ⟩
  ext b
  simp only [smul_mk_apply, Equiv.Perm.inv_eq_symm, Equiv.Perm.smul_def]
  obtain ⟨y, hy⟩ := φ (x.symm b)
  simpa

lemma QCOR.mk_repr_mk_repr {f' : β → α}
    (h : ∀ {b₁ b₂}, orbitRel G α (f b₁) (f b₂) ↔ orbitRel G α (f' b₁) (f' b₂)) (q : QCOR G f) :
    ⟦repr (⟦q.repr⟧ : QCOR G f')⟧ = q := by
  rw [← mem_class_iff]
  convert repr_mem_class (⟦q.repr⟧) using 1
  ext b
  nth_rw 1 [← q.repr_spec]
  simpa only [mem_class_iff, mk_eq_mk_iff] using h

@[simps]
noncomputable def qcor_equiv_qcor_canonical : QCOR G f ≃ QCOR G (canonicalPoint G f) where
  toFun q := ⟦q.repr⟧
  invFun q := ⟦q.repr⟧
  left_inv _ := QCOR.mk_repr_mk_repr orbitRel_comap_canonicalPoint_iff.symm _
  right_inv _ := QCOR.mk_repr_mk_repr orbitRel_comap_canonicalPoint_iff _

lemma qcor_class_mk_canonicalPoint_eq (b : β) :
    QCOR.class (⟦b⟧ : QCOR G (canonicalPoint G f)) = QCOR.class (⟦b⟧ : QCOR G f) := by
  ext b'
  simpa only [QCOR.mem_class_iff, Quotient.eq] using orbitRel_comap_canonicalPoint_iff

@[simp]
lemma qcor_class_mk_repr_canonicalPoint_eq (q : QCOR G f) :
    QCOR.class (⟦q.repr⟧ : QCOR G (canonicalPoint G f)) = q.class := by
  nth_rw 2 [← q.repr_spec]
  exact qcor_class_mk_canonicalPoint_eq q.repr

@[simps]
def equiv_class_mk_repr_canonicalPoint (q : QCOR G f) :
    q.class ≃ QCOR.class (⟦q.repr⟧ : QCOR G (canonicalPoint G f)) where
  toFun b := ⟨b, by simp⟩
  invFun b := ⟨b, by simpa using b.property⟩
  left_inv b := rfl
  right_inv b := rfl

variable (G f) in
lemma mlii_stabilizer_eq_sum [Finite G] [Fintype β] [DecidableEq β] [DecidableRel (orbitRel G α)]
    [Nontrivial α] [FaithfulSMul G α] :
    mlii (stabilizer (WreathProduct G (Equiv.Perm β) β) f) (β → α) = ∑ q : QCOR G f, mlii
      (WreathProduct (stabilizer G (f q.repr)) (Equiv.Perm q.class) q.class) (q.class → α) := by
  convert mlii_stabilizer_eq_sum_of_canonicalPoint (canonicalPoint_property G f) using 1
  · exact Eq.symm <| mlii_eq_of_bijective_mulActionHom
      (stabilizerEquivStabilizerOfOrbitRel <| canonicalPoint_mem_orbit G (Equiv.Perm β) f)
      _ (MulActionHom.stabilizerEquivStabilizerOfOrbitRel_bijective _)
  refine Finset.sum_equiv qcor_equiv_qcor_canonical (by simp) (fun q _ => ?_)
  let e := equiv_class_mk_repr_canonicalPoint q
  have h' := canonicalPoint_apply_repr_mk_repr_mem_orbit q
  let x := Classical.choose h'
  let e' : (q.class → α) ≃ (QCOR.class ⟦q.repr⟧ → α) := Equiv.piCongr e (fun _ => toPerm x)
  refine mlii_eq_of_bijective_mulActionHom ?φ ⟨e', ?_⟩ e'.bijective
  · exact congr (stabilizerEquivStabilizerOfOrbitRel h').symm e.permCongr' e (fun _ _ => rfl)
  · intro y f'
    ext b'
    let b := e.symm b'
    have hb : b' = e b := rfl
    simpa [hb, smul_apply', mul_smul, e', e, x] using Subgroup.smul_def _ _

end MLIIStabilizer

section MLII

lemma mlii_le_mlii_perm [Finite G] [Finite H] [Finite β]
    [Nontrivial α] [FaithfulSMul G α] [FaithfulSMul H β] :
    mlii (WreathProduct G H β) (β → α) ≤ mlii (WreathProduct G (Equiv.Perm β) β) (β → α) := by
  refine mlii_le_of_mulActionHom ⟨⟨fun x => ⟨toPermHom _ _ x.top, x.func⟩, ?_⟩, ?_⟩ ?_ ⟨id, ?_⟩ ?_
  · simp [toPerm_one, one_def]
  · intro x y
    simp [toPerm_mul, mul_def]
  · intro x y h
    simp only [toPermHom_apply, MonoidHom.coe_mk, OneHom.coe_mk, mk.injEq] at h
    exact WreathProduct.ext (MulAction.toPerm_injective h.1) h.2
  · intro x f
    rfl
  · exact Function.injective_id

lemma mlii_ge_mlii_pi [Finite G] [Finite H] [Finite β] :
    mlii (β → G) (β → α) ≤ mlii (WreathProduct G H β) (β → α) := by
  refine mlii_le_of_mulActionHom _ include_func_injective ⟨id, ?_⟩ Function.injective_id
  intro φ f; ext b; simp [smul_apply]

-- A version of the pigeonhole principle
variable (f) in
lemma exists_qcor_repr_not_mem_fixedPoint
    (h : (fixedPoints G α).Subsingleton) [Nontrivial (QCOR G f)] :
    ∃ q : QCOR G f, f q.repr ∉ fixedPoints G α := by
  by_contra! h'
  obtain ⟨q, q', hqq'⟩ := exists_pair_ne (QCOR G f)
  absurd hqq'
  rw [← QCOR.repr_spec q, ← QCOR.repr_spec q', QCOR.mk_eq_mk_iff, h (h' q) (h' q')]

variable [Fintype G] [Finite H] [Fintype β] [DecidableEq α] [DecidableEq β]
  [Nontrivial α] [FaithfulSMul G α] [FaithfulSMul H β]

lemma mlii_le1_aux1 {f : β → α} [Unique (QCOR G f)] (q : QCOR G f)
    (h : mlii (stabilizer (WreathProduct G (Equiv.Perm β) β) f) (β → α) <
      mlii (WreathProduct G (Equiv.Perm β) β) (β → α)) :
    Fintype.card q.class = Fintype.card β ∧ stabilizer G (f q.repr) < ⊤ := by
  have h2 := mlii_stabilizer_eq_sum G f
  have : default = q := Unique.default_eq _
  have hq : q.class = Set.univ := Set.eq_univ_iff_forall.mpr fun _ => this ▸ Unique.eq_default _
  use set_fintype_card_eq_univ_iff _ |>.mpr hq
  by_contra h3; rw [not_lt_top_iff] at h3
  rw [Finset.univ_unique, Finset.sum_singleton, this] at h2
  refine Nat.ne_of_lt h <| Eq.trans h2 ?_
  let e : q.class ≃ β :=
    (Equiv.subtypeEquiv (Equiv.refl β) (fun _ => by simp [hq])).trans (Equiv.Set.univ β)
  let e' : (q.class → α) ≃ (β → α) := Equiv.piCongr e (fun _ => Equiv.refl _)
  refine mlii_eq_of_bijective_mulActionHom ?_ ⟨e', ?_⟩ e'.bijective
  · refine congr (stabilizerMulEquivOfEqTop (f q.repr) h3) e.permCongr' e ?_
    exact fun _ _ => e.permCongr'_apply_apply_apply _ _ |>.symm
  · intro _ _; rfl

-- (0 : ℕ) - 1 = 0
lemma mlii_perm_le :
    mlii (WreathProduct G (Equiv.Perm β) β) (β → α) ≤
      Fintype.card β * mlii G α + Fintype.card β - 1 := by
  simp_rw [← Nat.mul_add_one]
  induction' hn : Fintype.card G + Fintype.card β
    using Nat.strong_induction_on with n ih generalizing G β
  obtain h1 | h1 := Nat.eq_zero_or_pos (mlii (WreathProduct G (Equiv.Perm β) β) (β → α))
  · exact h1 ▸ Nat.zero_le _
  have : Nonempty β := nonempty_of_faithfulSMul_of_nontrivial <|
    nontrivial_iff_mlii_pos .. |>.mpr h1
  obtain ⟨f, hf, h2⟩ := exists_mlii_stabilizerSubmonoid_add_one_eq h1
  rw [mlii_stabilizerSubmonoid_eq_mlii_stabilizer] at h2
  rw [← h2, mlii_stabilizer_eq_sum G f, Nat.add_one_le_iff]
  obtain _ | _ := subsingleton_or_nontrivial (QCOR G f)
  · cases (nonempty_unique (QCOR G f))
    rw [Finset.univ_unique, Finset.sum_singleton]
    set q : QCOR G f := default
    obtain ⟨h3, h4⟩ := mlii_le1_aux1 q <| Nat.lt_of_succ_le <| Nat.le_of_eq h2
    let m := Fintype.card (stabilizer G (f q.repr)) + Fintype.card q.class
    have : m < n
    · refine hn ▸ Nat.add_lt_add_of_lt_of_le ?_ (set_fintype_card_le_univ _)
      simpa [← Subgroup.card_lt_iff_lt] using h4
    apply Nat.lt_of_le_of_lt <| ih m this rfl
    rwa [Nat.sub_lt_sub_iff_right NeZero.one_le, h3,
      Nat.mul_lt_mul_left Fintype.card_pos, Nat.add_lt_add_iff_right,
      ← mlii_stabilizerSubmonoid_eq_mlii_stabilizer, mlii_stabilizerSubmonoid_lt_iff,
      ← stabilizer_lt_top_iff_notin_fixedPoints]
  · let m (q : QCOR G f) := Fintype.card (stabilizer G (f q.repr)) + Fintype.card q.class
    have (q : QCOR G f) : m q < n
    · refine hn ▸ Nat.add_lt_add_of_le_of_lt (Fintype.card_subtype_le _) ?_
      exact QCOR.card_class_lt_of_nontrivial q
    apply Nat.lt_of_le_of_lt <| Finset.sum_le_sum fun q _ => ih (m q) (this q) rfl
    apply Nat.lt_of_le_of_lt <| Finset.sum_le_sum fun q _ => Nat.sub_le_sub_right
      (Nat.mul_le_mul_left _ <| Nat.add_le_add_iff_right.mpr <| mlii_subgroup_le _) 1
    rw [← Nat.add_lt_add_iff_right (k := ∑ (q : QCOR G f), 1), ← Finset.sum_add_distrib]
    simp_rw [Nat.sub_add_cancel NeZero.one_le]
    have : 1 < ∑ (q : QCOR G f), 1 := by simpa using Fintype.one_lt_card
    rw [← Finset.sum_mul, QCOR.sum_card_class_eq, ← Nat.sub_add_comm NeZero.one_le,
      Nat.add_sub_assoc (Nat.one_le_of_lt this)]
    exact Nat.lt_add_of_pos_right (Nat.zero_lt_sub_of_lt this)

lemma mlii_le :
    mlii (WreathProduct G H β) (β → α) ≤ Fintype.card β * mlii G α + Fintype.card β - 1 :=
  le_trans mlii_le_mlii_perm mlii_perm_le

variable (β) in
lemma mlii_le2_aux1 [Nonempty β] {a : α} (h : a ∉ fixedPoints G α) :
    mlii (WreathProduct (stabilizer G a) (Equiv.Perm β) β) (β → α) < Fintype.card β * mlii G α := by
  apply Nat.lt_of_le_of_lt mlii_perm_le
  rw [← Nat.mul_add_one]
  apply Nat.sub_one_lt_of_le <| Nat.mul_pos (Fintype.card_pos) (Nat.add_one_pos _)
  apply Nat.mul_le_mul_left _
  rwa [← mlii_stabilizerSubmonoid_lt_iff, mlii_stabilizerSubmonoid_eq_mlii_stabilizer,
    ← Nat.add_one_le_iff] at h

lemma mlii_perm_le_of_subsingleton_fixedPoints (h : (fixedPoints G α).Subsingleton) :
    mlii (WreathProduct G (Equiv.Perm β) β) (β → α) ≤ Fintype.card β * mlii G α := by
  induction' hn : Fintype.card β using Nat.strong_induction_on with n ih generalizing G β
  obtain h1 | h1 := Nat.eq_zero_or_pos (mlii (WreathProduct G (Equiv.Perm β) β) (β → α))
  · exact h1 ▸ Nat.zero_le _
  have : Nonempty β := nonempty_of_faithfulSMul_of_nontrivial <|
    nontrivial_iff_mlii_pos .. |>.mpr h1
  obtain ⟨f, hf, h2⟩ := exists_mlii_stabilizerSubmonoid_add_one_eq h1
  rw [mlii_stabilizerSubmonoid_eq_mlii_stabilizer] at h2
  rw [← h2, mlii_stabilizer_eq_sum G f, Nat.add_one_le_iff]
  obtain _ | _ := subsingleton_or_nontrivial (QCOR G f)
  · cases (nonempty_unique (QCOR G f))
    rw [Finset.univ_unique, Finset.sum_singleton]
    set q : QCOR G f := default
    obtain ⟨h3, h4⟩ := mlii_le1_aux1 q <| Nat.lt_of_succ_le <| Nat.le_of_eq h2
    apply Nat.lt_of_lt_of_le <| mlii_le2_aux1 _ <| stabilizer_lt_top_iff_notin_fixedPoints.mp h4
    rw [h3, hn]
  · have h3 (q : QCOR G f) :
      mlii (WreathProduct (stabilizer G (f q.repr)) (Equiv.Perm q.class) q.class) (q.class → α) ≤
        Fintype.card q.class * mlii G α
    · by_cases h' : f q.repr ∈ fixedPoints G α
      · rw [fixedPoints_eq_fixedPoints_stabilizer h'] at h
        rw [← mlii_stabilizerSubmonoid_eq h']
        exact ih (Fintype.card q.class) (hn ▸ QCOR.card_class_lt_of_nontrivial q) h rfl
      · exact Nat.le_of_lt <| mlii_le2_aux1 _ h'
    rw [← hn, ← QCOR.sum_card_class_eq G f, Finset.sum_mul]
    refine Finset.sum_lt_sum (fun q _ => h3 q) ?_
    obtain ⟨q₀, hq₀⟩ := exists_qcor_repr_not_mem_fixedPoint f h
    exact ⟨q₀, Finset.mem_univ _, mlii_le2_aux1 q₀.class hq₀⟩

lemma mlii_le_of_subsingleton_fixedPoints (h : (fixedPoints G α).Subsingleton) :
    mlii (WreathProduct G H β) (β → α) ≤ Fintype.card β * mlii G α :=
  le_trans mlii_le_mlii_perm <| mlii_perm_le_of_subsingleton_fixedPoints h

lemma mlii_le_of_subsingleton_fixedPoints_stabilizer (h1 : fixedPoints G α = ∅)
    (h2 : ∀ a : α, (fixedPoints (stabilizer G a) α).Subsingleton) :
    mlii (WreathProduct G H β) (β → α) ≤ Fintype.card β * mlii G α - (Fintype.card β - 1) := by
  apply le_trans mlii_le_mlii_perm
  obtain h3 | h3 := Nat.eq_zero_or_pos (mlii (WreathProduct G (Equiv.Perm β) β) (β → α))
  · exact h3 ▸ Nat.zero_le _
  have : Nonempty β := nonempty_of_faithfulSMul_of_nontrivial <|
    nontrivial_iff_mlii_pos .. |>.mpr h3
  obtain ⟨f, hf, h4⟩ := exists_mlii_stabilizerSubmonoid_add_one_eq h3
  rw [mlii_stabilizerSubmonoid_eq_mlii_stabilizer] at h4
  rw [← h4, mlii_stabilizer_eq_sum G f, tsub_tsub_assoc ?hrw NeZero.one_le,
    Nat.add_le_add_iff_right, ← Nat.mul_sub_one]
  apply le_trans <| Finset.sum_le_sum <| fun q _ => mlii_perm_le_of_subsingleton_fixedPoints <| h2 _
  rw [← QCOR.sum_card_class_eq G f, Finset.sum_mul]
  refine Finset.sum_le_sum fun q _ => Nat.mul_le_mul_left _ <| Nat.le_sub_one_of_lt ?_
  exact mlii_stabilizerSubmonoid_lt (h1 ▸ Set.not_mem_empty (f q.repr))
  case hrw =>
    exact Nat.le_mul_of_pos_right _ <| nontrivial_iff_mlii_pos .. |>.mp <|
      nontrivial_of_fixedPoints_eq_empty h1

theorem mlii_eq_of_unique_mem_fixedPoints (h : ∃! a : α, a ∈ fixedPoints G α) :
    mlii (WreathProduct G H β) (β → α) = Fintype.card β * mlii G α := by
  obtain ⟨a, h1, h2⟩ := h
  refine Nat.le_antisymm ?_ ?_
  · exact mlii_le_of_subsingleton_fixedPoints (fun a1 ha1 a2 ha2 => (h2 _ ha2) ▸ (h2 _ ha1))
  · have := mlii_pi_eq_of_fixedPoints_nonempty (ι := β) (α := fun _ => α) (fun i => ⟨a, h1⟩)
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at this
    exact this ▸ mlii_ge_mlii_pi

theorem mlii_eq_of_subsingleton_fixedPoints_stabilizer (h1 : fixedPoints G α = ∅)
    (h2 : ∀ a : α, (fixedPoints (stabilizer G a) α).Subsingleton) :
    mlii (WreathProduct G H β) (β → α) = Fintype.card β * mlii G α - (Fintype.card β - 1) := by
  refine Nat.le_antisymm (mlii_le_of_subsingleton_fixedPoints_stabilizer h1 h2) ?_
  have := mlii_pi_eq_of_fixedPoints_eq_empty (ι := β) (α := fun _ => α) (fun i => h1)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at this
  exact this ▸ mlii_ge_mlii_pi

end MLII

end WreathProduct
