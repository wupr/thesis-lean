import Mathlib.GroupTheory.GroupAction.Basic

section

lemma MulAction.toPerm_one {G α : Type*} [Group G] [MulAction G α] :
    toPerm (1 : G) = (1 : Equiv.Perm α) := by
  ext; simp

lemma AddAction.toPerm_zero {G α : Type*} [AddGroup G] [AddAction G α] :
    toPerm (0 : G) = (1 : Equiv.Perm α) := by
  ext; simp

attribute [to_additive existing] MulAction.toPerm_one

lemma MulAction.toPerm_mul {G α : Type*} [Group G] [MulAction G α] (g₁ g₂ : G) :
    (toPerm (g₁ * g₂) : Equiv.Perm α) = toPerm g₁ * toPerm g₂ := by
  ext; simp [mul_smul]

lemma AddAction.toPerm_add {G α : Type*} [AddGroup G] [AddAction G α] (g₁ g₂ : G) :
    (toPerm (g₁ + g₂) : Equiv.Perm α) = toPerm g₁ * toPerm g₂ := by
  ext; simp [add_vadd]

attribute [to_additive existing] MulAction.toPerm_mul

end

namespace MulAction

section

variable {M α : Type*} [Monoid M] [MulAction M α]

@[to_additive]
lemma stabilizerSubmonoid_eq_top_iff_mem_fixedPoints {a : α} :
    stabilizerSubmonoid M a = ⊤ ↔ a ∈ fixedPoints M α := by
  simp [Submonoid.eq_top_iff']

@[to_additive]
lemma stabilizerSubmonoid_lt_top_iff_notin_fixedPoints {a : α} :
    stabilizerSubmonoid M a < ⊤ ↔ a ∉ fixedPoints M α := by
  rw [← not_iff_not]; push_neg
  convert stabilizerSubmonoid_eq_top_iff_mem_fixedPoints using 1
  exact not_lt_top_iff

@[to_additive]
lemma subset_fixedPoints_stabilizerSubmonoid (a : α) :
    fixedPoints M α ⊆ fixedPoints (stabilizerSubmonoid M a) α :=
  fun _ ha m ↦ ha m.val

@[to_additive (attr := simps)]
def stabilizerSubmonoidMulEquivOfEqTop (a : α) (h : stabilizerSubmonoid M a = ⊤) :
    stabilizerSubmonoid M a ≃* M where
  toFun := Submonoid.subtype _
  invFun x := ⟨x, (Submonoid.eq_top_iff' _ |>.mp h) x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end

section

variable {G α : Type*} [Group G] [MulAction G α]

@[to_additive]
lemma stabilizer_eq_top_iff_mem_fixedPoints {a : α} :
    stabilizer G a = ⊤ ↔ a ∈ fixedPoints G α := by
  simp [Subgroup.eq_top_iff']

@[to_additive]
lemma stabilizer_lt_top_iff_notin_fixedPoints {a : α} :
    stabilizer G a < ⊤ ↔ a ∉ fixedPoints G α := by
  rw [← not_iff_not]; push_neg
  convert stabilizer_eq_top_iff_mem_fixedPoints using 1
  exact not_lt_top_iff

@[to_additive]
lemma fixedPoints_eq_fixedPoints_stabilizer {a : α} (h : a ∈ fixedPoints G α) :
    fixedPoints G α = fixedPoints (stabilizer G a) α := by
  ext b
  exact Iff.intro (fun hb x => hb x.val) (fun hb x => hb ⟨x, h x⟩)

@[to_additive (attr := simp)]
lemma stabilizerEquivStabilizerOfOrbitRel_apply_smul
    {a b : α} (h : orbitRel G α a b) (x : stabilizer G a) (c : α) :
    (stabilizerEquivStabilizerOfOrbitRel h x) • c =
      ((Classical.choose h)⁻¹ * x * (Classical.choose h)) • c :=
  rfl

@[to_additive (attr := simp)]
lemma stabilizerEquivStabilizerOfOrbitRel_inv_apply_smul
    {a b : α} (h : orbitRel G α a b) (x : stabilizer G b) (c : α) :
    ((stabilizerEquivStabilizerOfOrbitRel h).symm x) • c =
      ((Classical.choose h) * x * (Classical.choose h)⁻¹) • c :=
  rfl

@[to_additive (attr := simps)]
def stabilizerMulEquivOfEqTop (a : α) (h : stabilizer G a = ⊤) :
    stabilizer G a ≃* G where
  toFun := Subgroup.subtype _
  invFun x := ⟨x, (Subgroup.eq_top_iff' _ |>.mp h) x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end

end MulAction


section FaithfulSMul

@[to_additive]
theorem FaithfulSMul.mk' {G α : Type*} [Group G] [MulAction G α]
    (h : ∀ m : G, (∀ a : α, m • a = a) → m = 1) :
    FaithfulSMul G α := by
  refine mk ?_
  intro m₁ m₂ h'
  rw [← inv_mul_eq_one]
  apply h
  intro a
  rw [mul_smul, ← h' a, inv_smul_smul]

namespace MulAction

variable {M α : Type*} [Monoid M] [MulAction M α] [FaithfulSMul M α]

@[to_additive]
lemma iInf_stabiliserSubmonoid_eq_bot :
    ⨅ a : α, stabilizerSubmonoid M a = ⊥ := by
  simp only [Submonoid.eq_bot_iff_forall, Submonoid.mem_iInf, mem_stabilizerSubmonoid_iff]
  intro m
  convert @FaithfulSMul.eq_of_smul_eq_smul _ α _ ‹_› m 1 using 3
  exact Eq.symm (one_smul M _)

variable (M α) in
@[to_additive]
lemma exists_not_mem_fixedPoints_iff :
    (∃ a : α, a ∉ fixedPoints M α) ↔ Nontrivial M := by
  refine ⟨fun ⟨a, ha⟩ => ?_, fun h => ?_⟩
  · rw [← Submonoid.nontrivial_iff]
    use stabilizerSubmonoid M a, ⊤
    exact ne_top_of_lt <| stabilizerSubmonoid_lt_top_iff_notin_fixedPoints.mpr <| ha
  · have := @iInf_stabiliserSubmonoid_eq_bot M α _ _ _ ▸ bot_ne_top (α := Submonoid M)
    simpa [stabilizerSubmonoid_eq_top_iff_mem_fixedPoints]

@[to_additive]
lemma nontrivial_of_fixedPoints_eq_empty [Nonempty α] (h : fixedPoints M α = ∅) :
    Nontrivial M := by
  refine Nonempty.elim ‹_› fun (a : α) => ?_
  rw [← exists_not_mem_fixedPoints_iff M α, h]
  exact ⟨a, Set.not_mem_empty _⟩

end MulAction

end FaithfulSMul
