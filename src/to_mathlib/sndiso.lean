/-
A proof of the second isomorphism theorem for groups.
Author: Adrián Doña Mateo

These were contributed to mathlib in
[#6187](https://github.com/leanprover-community/mathlib/pull/6187/).

An apostrophe was added at the end of the names to avoid clashes.
-/

import group_theory.quotient_group

-- These lemmas were added to src/group_theory/subgroup.lean.
namespace subgroup

variables {G : Type*} [group G]

/-- The inclusion homomorphism from a subgroup `H` contained in `K` to `K`. -/
@[to_additive "The inclusion homomorphism from a additive subgroup `H` contained in `K` to `K`."]
def inclusion' {H K : subgroup G} (h : H ≤ K) : H →* K :=
monoid_hom.mk' (λ x, ⟨x, h x.prop⟩) (λ ⟨a, ha⟩  ⟨b, hb⟩, rfl)

@[simp, to_additive]
lemma coe_inclusion' {H K : subgroup G} {h : H ≤ K} (a : H) : (inclusion h a : G) = a :=
by { cases a, simp only [inclusion, coe_mk, monoid_hom.coe_mk'] }

@[simp, to_additive]
lemma subtype_comp_inclusion' {H K : subgroup G} (hH : H ≤ K) :
  K.subtype.comp (inclusion hH) = H.subtype :=
by { ext, simp }

@[simp, to_additive]
lemma comap_subtype_inf_left' {H K : subgroup G} : comap H.subtype (H ⊓ K) = comap H.subtype K :=
ext $ λ x, and_iff_right_of_imp (λ _, x.prop)

@[simp, to_additive]
lemma comap_subtype_inf_right' {H K : subgroup G} : comap K.subtype (H ⊓ K) = comap K.subtype H :=
ext $ λ x, and_iff_left_of_imp (λ _, x.prop)

@[priority 100, to_additive]
instance subgroup.normal_inf' (H N : subgroup G) [hN : N.normal] :
  ((H ⊓ N).comap H.subtype).normal :=
⟨λ x hx g, begin
  simp only [subgroup.mem_inf, coe_subtype, subgroup.mem_comap] at hx,
  simp only [subgroup.coe_mul, subgroup.mem_inf, coe_subtype, subgroup.coe_inv, subgroup.mem_comap],
  exact ⟨H.mul_mem (H.mul_mem g.2 hx.1) (H.inv_mem g.2), hN.1 x hx.2 g⟩,
end⟩

end subgroup

-- These lemmas were added to src/group_theory/quotient_group.lean.
namespace quotient_group
open monoid_hom

variables {G : Type*} [group G]


/-- If two normal subgroups `M` and `N` of `G` are the same, their quotient groups are
isomorphic. -/
@[to_additive "If two normal subgroups `M` and `N` of `G` are the same, their quotient groups are
isomorphic."]
def equiv_quotient_of_eq' {M N : subgroup G} [M.normal] [N.normal] (h : M = N) :
  quotient M ≃* quotient N :=
{ to_fun := (lift M (mk' N) (λ m hm, quotient_group.eq.mpr (by simpa [← h] using M.inv_mem hm))),
  inv_fun := (lift N (mk' M) (λ n hn, quotient_group.eq.mpr (by simpa [← h] using N.inv_mem hn))),
  left_inv := λ x, x.induction_on' $ by { intro, refl },
  right_inv := λ x, x.induction_on' $ by { intro, refl },
  map_mul' := λ x y, by rw map_mul }

  section snd_isomorphism_thm

open subgroup

/-- The second isomorphism theorem: given two subgroups `H` and `N` of a group `G`, where `N`
is normal, defines an isomorphism between `H/(H ∩ N)` and `(HN)/N`. -/
@[to_additive "The second isomorphism theorem: given two subgroups `H` and `N` of a group `G`,
where `N` is normal, defines an isomorphism between `H/(H ∩ N)` and `(H + N)/N`"]
noncomputable def quotient_inf_equiv_prod_normal_quotient' (H N : subgroup G) [N.normal] :
  quotient ((H ⊓ N).comap H.subtype) ≃* quotient (N.comap (H ⊔ N).subtype) :=
/- φ is the natural homomorphism H →* (HN)/N. -/
let φ : H →* quotient (N.comap (H ⊔ N).subtype) :=
  (mk' $ N.comap (H ⊔ N).subtype).comp (inclusion le_sup_left) in
have φ_surjective : function.surjective φ := λ x, x.induction_on' $
  begin
    rintro ⟨y, (hy : y ∈ ↑(H ⊔ N))⟩, rw mul_normal H N at hy,
    rcases hy with ⟨h, n, hh, hn, rfl⟩,
    use [h, hh], apply quotient.eq.mpr, change h⁻¹ * (h * n) ∈ N,
    rwa [←mul_assoc, inv_mul_self, one_mul],
  end,
(equiv_quotient_of_eq (by simp [comap_comap, ←comap_ker])).trans
  (quotient_ker_equiv_of_surjective φ φ_surjective)

end snd_isomorphism_thm

end quotient_group
