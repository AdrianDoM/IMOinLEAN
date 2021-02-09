import group_theory.quotient_group
import .subgroup

open subgroup monoid_hom

namespace quotient_group

section snd_isomorphism_theorem

variables {G : Type*} [group G]

def φ (H N : subgroup G) [N.normal] : H →* quotient (N.comap (H.prod_normal N).subtype) :=
(mk' $ N.comap (H.prod_normal N).subtype).comp (inclusion le_prod_normal_left)

lemma ker_φ {H N : subgroup G} [N.normal] : (φ H N).ker = (H ⊓ N).comap H.subtype :=
ext $ λ x, 
  ⟨λ h, by { simp, use x.2, dsimp [φ] at h, rw [← comap_ker, ker_mk, mem_comap] at h, simpa using h }, 
  λ h, by { dsimp [φ], rw [← comap_ker, ker_mk], simp at h, simpa using h.2 }⟩

lemma φ_surjective {H N : subgroup G} [N.normal] : function.surjective (φ H N) :=
λ x, begin
  rcases quot.exists_rep x with ⟨⟨w, h, hh, n, hn, rfl⟩, rfl⟩,
  use [h, hh], apply quotient.eq.mpr, change h⁻¹ * (h * n) ∈ N,
  rwa [← mul_assoc, inv_mul_self, one_mul],
end

/- The second isomorphism theorem: given two subgroups `H` and `N` of a group `G`, where `N`
is normal, defines an isomorphism between `H/(H ∩ N)` and `(HN)/N`. -/
noncomputable def quotient_inf_equiv_prod_normal_quotient (H N : subgroup G) [N.normal] :
  quotient ((H ⊓ N).comap H.subtype) ≃* quotient (N.comap (H.prod_normal N).subtype) :=
quotient_ker_equiv_of_surjective (φ H N) φ_surjective


#check Prop

end snd_isomorphism_theorem

end quotient_group