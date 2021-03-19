import algebra.category.Group
import category_theory.isomorphism_classes

open category_theory

@[to_additive is_trivial_add_class]
def is_trivial_class (C : isomorphism_classes.obj (Cat.of Group)) : Prop :=
quotient.lift_on' C (λ (G : Group), subsingleton G)
  (λ G H ⟨h⟩, eq_iff_iff.mpr
    ⟨λ hG, @equiv.subsingleton.symm _ _ (iso.Group_iso_to_mul_equiv h).to_equiv hG,
    λ hH, @equiv.subsingleton _ _ (iso.Group_iso_to_mul_equiv h).to_equiv hH⟩)

@[simp, to_additive is_trivial_add_class_mk']
lemma is_trivial_class_mk' {G : Group} : is_trivial_class (quotient.mk' G) = subsingleton G :=
by simp only [quotient.lift_on'_mk', is_trivial_class]

@[to_additive is_trivial_add_class_one]
lemma is_trivial_class_one : is_trivial_class (quotient.mk' (1 : Group)) :=
punit.subsingleton

@[to_additive add_class_eq]
lemma class_eq {G H : Type*} [group G] [group H] : G ≃* H →
  (quotient.mk' (Group.of G) : isomorphism_classes.obj (Cat.of Group)) = quotient.mk' (Group.of H) :=
λ h, quotient.eq'.mpr ⟨h.to_Group_iso⟩

@[to_additive add_equiv_to_AddGroup_iso]
def mul_equiv_to_Group_iso {G H : Group} (e : G ≃* H) : G ≅ H :=
{ hom := e.to_monoid_hom, inv :=  e.symm.to_monoid_hom }

@[to_additive add_class_eq']
lemma class_eq' {G H : Group} : G ≃* H →
  (quotient.mk' G : isomorphism_classes.obj (Cat.of Group)) = quotient.mk' H :=
λ h, quotient.eq'.mpr ⟨mul_equiv_to_Group_iso h⟩

@[to_additive]
instance Group.fintype {G : Type*} [group G] [fintype G] : fintype (Group.of G) :=
show fintype G, from infer_instance