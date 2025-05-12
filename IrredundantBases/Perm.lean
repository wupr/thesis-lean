import Mathlib.Algebra.Group.End

namespace Equiv

variable {α β : Type*} {e : α ≃ β}

lemma permCongr_apply_symm (p : Perm α) : (e.permCongr p).symm = e.permCongr p.symm := rfl

@[simps!]
def permCongr' : Perm α ≃* Perm β := MulEquiv.mk' (permCongr e) (fun x y => by ext; simp)

lemma permCongr'_apply_apply_apply (p : Perm α) (a : α) : (e.permCongr' p) (e a) = e (p a) :=
  by simp

end Equiv
