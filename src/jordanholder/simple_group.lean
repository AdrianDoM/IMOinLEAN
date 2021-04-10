import group_theory.quotient_group
import category_theory.isomorphism_classes
import algebra.category.Group
import .subgroup

open subgroup

@[to_additive is_simple_add]
def is_simple (G : Type*) [group G] : Prop :=
∀ (N : subgroup G), N.normal → N = ⊥ ∨ N = ⊤

variables {G H : Type*} [group G] [group H]

@[simp, to_additive is_simple_add_coe_AddGroup]
lemma is_simple_coe_Group : is_simple ↥(Group.of G) ↔ is_simple G := by refl

@[simp, to_additive not_is_simple_add]
lemma not_is_simple : ¬ is_simple G ↔ ∃ (N : subgroup G), N.normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ :=
by { dsimp [is_simple], push_neg } 

@[to_additive is_simple_add_of_surjetion]
lemma is_simple_of_surjection (hG : is_simple G) (f : G →* H) (hf : function.surjective f) :
  is_simple H :=
λ N hN, begin
  cases hG (N.comap f) (normal.comap hN f),
  { left, rw [← map_bot f, ← h, map_comap_eq hf] },
  right, rw ← comap_top f at h, rw [← map_comap_eq hf ⊤, ← h, map_comap_eq hf],
end

@[to_additive add_equiv_is_simple_add_iff]
lemma mul_equiv_is_simple_iff (h : G ≃* H) : is_simple G ↔ is_simple H :=
⟨λ hG, is_simple_of_surjection hG h.to_monoid_hom h.right_inv.surjective,
  λ hH, is_simple_of_surjection hH h.symm.to_monoid_hom h.symm.right_inv.surjective⟩

open category_theory

@[simp, to_additive is_simple_add_class] 
def is_simple_class (C : isomorphism_classes.obj (Cat.of Group)) : Prop :=
quotient.lift_on' C (λ (G : Group), is_simple G)
  (λ G H ⟨h⟩, eq_iff_iff.mpr $ mul_equiv_is_simple_iff (iso.Group_iso_to_mul_equiv h))

@[to_additive is_simple_add_quotient_eq]
def is_simple_quotient_eq {N M : subgroup G} [N.normal] [M.normal] (h : N = M) :
  is_simple (quotient_group.quotient N) = is_simple (quotient_group.quotient M) :=
by unfreezingI { subst h }
