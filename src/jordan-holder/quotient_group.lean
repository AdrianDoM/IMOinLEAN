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

noncomputable def quotient_bot : quotient (⊥ : subgroup G) ≃* G :=
mul_equiv.symm $ mul_equiv.of_bijective (mk' ⊥)
  ⟨by rw [injective_iff_ker_eq_bot, ker_mk], mk'_surjective⟩

end quotient_group