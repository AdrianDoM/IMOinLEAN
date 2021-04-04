import group_theory.quotient_group
import .subgroup

instance quotient.subsingleton {α : Type*} [subsingleton α] (s : setoid α) :
  subsingleton (quotient s) :=
⟨λ a b, quotient.induction_on₂ a b $ λ x y, by rw subsingleton.elim x y⟩

open subgroup monoid_hom

namespace quotient_group

variables {G : Type*} [group G]

@[to_additive]
lemma subsingleton_of_subgroup_quotient_subsingleton {N : subgroup G} :
  subsingleton N → subsingleton (quotient N) → subsingleton G :=
λ hN hqN, @equiv.subsingleton G (quotient N × N) group_equiv_quotient_times_subgroup
  (@subsingleton.prod _ _ hqN hN)

@[to_additive]
lemma mk'_surjective (N : subgroup G) [N.normal] : function.surjective (mk' N) :=
surjective_quot_mk _

@[to_additive]
def quotient_bot : quotient (⊥ : subgroup G) ≃* G :=
{ to_fun := lift ⊥ (id G) (λ x hx, (mem_bot.mp hx).symm ▸ rfl), inv_fun := mk' ⊥,
  left_inv := λ x, x.induction_on' $ by { intro a, simp only [lift_mk', id_apply], refl },
  right_inv := λ x, show (lift ⊥ (id G) _) (quotient_group.mk x) = x, by simp,
  map_mul' := λ x y, map_mul _ x y }

variables {N : subgroup G} [normal N]

@[to_additive]
lemma map_mk'_normal {K : subgroup G} [hK : normal K] (h : N ≤ K) : normal (K.map (mk' N)) :=
⟨begin
  intros n hn, rcases mem_map.mp hn with ⟨k, hk, rfl⟩,
  intro g', apply quotient.induction_on' g', intro g, simp,
  use [g * k * g⁻¹, hK.conj_mem k hk g], simp, refl,
end⟩

@[to_additive]
lemma map_mk'_eq_top {K : subgroup G} (hNK : N ≤ K) : K.map (mk' N) = ⊤ ↔ K = ⊤ :=
⟨λ h, le_antisymm le_top (λ g _,
  have hg : (mk' N) g ∈ K.map (mk' N) := h.symm ▸ mem_top ((mk' N) g),
  exists.elim hg $ λ g' ⟨hg', (hg : ↑g' = ↑g)⟩, begin
    rw quotient_group.eq at hg,
    convert_to g' * (g'⁻¹ * g) ∈ K, { simp },
    exact mul_mem K hg' (hNK hg),
  end),
λ h, set_like.ext' $ h.symm ▸ set.image_univ_of_surjective (surjective_quot_mk _)⟩

@[to_additive]
lemma le_comap_mk' {K : subgroup (quotient N)} : N ≤ comap (mk' N) K :=
by conv_lhs { rw ←ker_mk N }; exact ker_le_comap

@[simp, to_additive]
lemma mk'_eq_one (x : G) : (mk' N) x = 1 ↔ x ∈ N :=
by rw [←mem_ker, ker_mk]

@[to_additive]
lemma subsingleton_quotient_iff : subsingleton (quotient N) ↔ N = ⊤ :=
⟨λ h, le_antisymm le_top (λ x _, ker_mk N ▸
  show mk' N x = 1, from @subsingleton.elim _ h (mk' N x) 1),
λ h, ⟨λ a b, quotient.induction_on₂' a b $ λ x y,
  show ↑x = ↑y, from quotient_group.eq.mpr $ by { rw h, trivial }⟩⟩

variables {H : Type*} [group H]
@[to_additive]
def equiv_quotient_of_equiv (e : G ≃* H) : quotient N ≃* quotient (N.map e.to_monoid_hom) :=
{ to_fun := lift _ ((mk' $ N.map e.to_monoid_hom).comp e.to_monoid_hom) (by simp),
  inv_fun := lift _ ((mk' N).comp e.symm.to_monoid_hom) (by simp),
  left_inv := λ x, by
    { apply x.induction_on', intro a, simp,
      change (lift _ _ _) (quotient.mk' (e a)) = _, simp, refl },
  right_inv := λ x, by
    { apply x.induction_on', intro a, simp,
      change (lift _ _ _) (quotient.mk' (e.symm a)) = _, simp, refl },
  map_mul' := by simp }

end quotient_group