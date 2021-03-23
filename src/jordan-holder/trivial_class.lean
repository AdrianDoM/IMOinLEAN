import algebra.category.Group
import category_theory.isomorphism_classes
import .fingroup .simple_group

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

variable (C : isomorphism_classes.obj (Cat.of Group))

@[to_additive is_finite_add_class]
def is_finite_class : Prop :=
quotient.lift_on' C (λ (G : Group), nonempty (fintype G))
  (λ G H ⟨h⟩, eq_iff_iff.mpr
    ⟨λ ⟨hG⟩, ⟨@fintype.of_equiv _ _ hG h.Group_iso_to_mul_equiv.to_equiv⟩,
    λ ⟨hH⟩, ⟨@fintype.of_equiv _ _ hH h.Group_iso_to_mul_equiv.to_equiv.symm⟩⟩)

@[to_additive is_finite_add_class_mk']
lemma is_finite_class_mk' {G : Group} (hG : fintype G) :
  is_finite_class (quotient.mk' G) :=
by simp [is_finite_class, quotient.lift_on'_mk']; use hG

@[to_additive add_class_card]
noncomputable def class_card (h : is_finite_class C) : ℕ :=
begin
  let G : Group := quotient.out' C,
  dsimp [is_finite_class] at h,
  rw [←quotient.out_eq' C, quotient.lift_on'_mk'] at h,
  exact @fintype.card G h.some,
end

@[to_additive add_class_card_mk']
lemma class_card_mk' {G : Group} (hG : fintype G) :
  class_card (quotient.mk' G) (is_finite_class_mk' hG) = @fintype.card G hG :=
begin
  apply fintype.card_eq.mpr ⟨(iso.Group_iso_to_mul_equiv _).to_equiv⟩,
  exact (@quotient.mk_out' _ (is_isomorphic_setoid _) G).some,
end

variable {C}
variables (hC : is_finite_class C) (h : (class_card C hC).prime)
include h

@[to_additive not_is_trivial_add_class_of_prime_card]
lemma not_is_trivial_class_of_prime_card : ¬ is_trivial_class C :=
begin
  dsimp [is_trivial_class], dsimp [is_finite_class] at hC,
  rw [←quotient.out_eq' C, quotient.lift_on'_mk'] at *,
  haveI := hC.some,
  apply subgroup.not_subsingleton_of_prime_card,
  simpa only [←class_card_mk', quotient.out_eq'],
end

@[to_additive is_simple_add_class_of_prime_card]
lemma is_simple_class_of_prime_card : is_simple_class C :=
begin
  dsimp [is_simple_class], dsimp [is_finite_class] at hC,
  rw [←quotient.out_eq' C, quotient.lift_on'_mk'] at *,
  haveI := hC.some,
  apply subgroup.is_simple_of_prime_card,
  simpa only [←class_card_mk', quotient.out_eq'],
end