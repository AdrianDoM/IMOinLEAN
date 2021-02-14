import algebra.category.Group
import category_theory.isomorphism_classes

open category_theory

@[simp]
def is_trivial_class (C : isomorphism_classes.obj (Cat.of Group)) : Prop :=
quotient.lift_on' C (λ (G : Group), subsingleton G)
  (λ G H ⟨h⟩, eq_iff_iff.mpr
    ⟨λ hG, @equiv.subsingleton.symm _ _ (iso.Group_iso_to_mul_equiv h).to_equiv hG,
    λ hH, @equiv.subsingleton _ _ (iso.Group_iso_to_mul_equiv h).to_equiv hH⟩)