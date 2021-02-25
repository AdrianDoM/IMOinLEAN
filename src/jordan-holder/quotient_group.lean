import group_theory.quotient_group
import .subgroup

open subgroup monoid_hom

namespace quotient_group

variables {G : Type*} [group G]

lemma subsingleton_of_subgroup_quotient_subsingleton {N : subgroup G} :
  subsingleton N → subsingleton (quotient N) → subsingleton G :=
λ hN hqN, @equiv.subsingleton G (quotient N × N) group_equiv_quotient_times_subgroup
  (@subsingleton.prod _ _ hqN hN)

lemma mk'_surjective {N : subgroup G} [N.normal] : function.surjective (mk' N) :=
λ x, x.induction_on' $ by { intro a, use a, refl }

def quotient_bot : quotient (⊥ : subgroup G) ≃* G :=
{ to_fun := lift ⊥ (id G) (λ x hx, (mem_bot.mp hx).symm ▸ rfl), inv_fun := mk' ⊥,
  left_inv := λ x, x.induction_on' $ by { intro a, simp only [lift_mk', id_apply], refl },
  right_inv := λ x, show (lift ⊥ (id G) _) (quotient_group.mk x) = x, by simp,
  map_mul' := λ x y, map_mul _ x y }

variables {N : subgroup G} [normal N]

noncomputable def equiv_of_subsingleton_quotient (h : subsingleton (quotient N)) : N ≃* G := sorry

end quotient_group