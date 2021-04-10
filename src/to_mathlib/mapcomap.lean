/-
Translate a few missing lemmas to the subgroup API.
Author: Adrián Doña Mateo

These were contributed to mathlib in
[#6974](https://github.com/leanprover-community/mathlib/pull/6974/).

There are no name clashes in this file because the local version of the library is has not
been upgraded to this PR.
-/

import group_theory.subgroup

-- These lemmas were added to src/group_theory/subgroup.lean

variables {G N : Type*} [group G] [group N]

namespace subgroup
open set

@[to_additive]
lemma comap_mono {f : G →* N} {K K' : subgroup N} : K ≤ K' → comap f K ≤ comap f K' :=
preimage_mono

@[to_additive]
lemma map_mono {f : G →* N} {K K' : subgroup G} : K ≤ K' → map f K ≤ map f K' :=
image_subset _

open monoid_hom

variables {H : Type*} [group H]

@[to_additive]
lemma map_le_range (f : G →* H) (K : subgroup G) : map f K ≤ f.range :=
(range_eq_map f).symm ▸ map_mono le_top

@[to_additive]
lemma ker_le_comap (f : G →* H) (K : subgroup H) : f.ker ≤ comap f K :=
comap_mono bot_le

@[to_additive]
lemma map_comap_le (f : G →* H) (K : subgroup H) : map f (comap f K) ≤ K :=
(gc_map_comap f).l_u_le _

@[to_additive]
lemma le_comap_map (f : G →* H) (K : subgroup G) : K ≤ comap f (map f K) :=
(gc_map_comap f).le_u_l _

@[to_additive]
lemma map_comap_eq (f : G →* H) (K : subgroup H) :
  map f (comap f K) = f.range ⊓ K :=
set_like.ext' begin
  convert set.image_preimage_eq_inter_range,
  simp [set.inter_comm],
end

@[to_additive]
lemma comap_map_eq (f : G →* H) (K : subgroup G) :
  comap f (map f K) = K ⊔ f.ker :=
begin
  refine le_antisymm _ (sup_le (le_comap_map _ _) (ker_le_comap _ _)),
  intros x hx, simp only [exists_prop, mem_map, mem_comap] at hx,
  rcases hx with ⟨y, hy, hy'⟩,
  have : y⁻¹ * x ∈ f.ker, { rw mem_ker, simp [hy'] },
  convert mul_mem _ (mem_sup_left hy) (mem_sup_right this),
  simp,
end

@[to_additive]
lemma map_comap_eq_self {f : G →* H} {K : subgroup H} (h : K ≤ f.range) :
  map f (comap f K) = K :=
by rwa [map_comap_eq, inf_eq_right]

@[to_additive]
lemma map_comap_eq_self_of_surjective {f : G →* H} (h : function.surjective f) (K : subgroup H) :
  map f (comap f K) = K :=
map_comap_eq_self ((range_top_of_surjective _ h).symm ▸ le_top)

@[to_additive]
lemma comap_injective {f : G →* H} (h : function.surjective f) : function.injective (comap f) :=
λ K L hKL, by { apply_fun map f at hKL, simpa [map_comap_eq_self_of_surjective h] using hKL }

@[to_additive]
lemma comap_map_eq_self {f : G →* H} {K : subgroup G} (h : f.ker ≤ K) :
  comap f (map f K) = K :=
by rwa [comap_map_eq, sup_eq_left]

@[to_additive]
lemma comap_map_eq_self_of_injective {f : G →* H} (h : function.injective f) (K : subgroup G) :
  comap f (map f K) = K :=
comap_map_eq_self (((ker_eq_bot_iff _).mpr h).symm ▸ bot_le)

@[to_additive]
lemma map_injective {f : G →* H} (h : function.injective f) : function.injective (map f) :=
λ K L hKL, by { apply_fun comap f at hKL, simpa [comap_map_eq_self_of_injective h] using hKL }

@[to_additive]
lemma map_eq_comap_of_inverse {f : G →* H} {g : H →* G} (hl : function.left_inverse g f)
  (hr : function.right_inverse g f) (K : subgroup G) : map f K = comap g K :=
set_like.ext' $ by rw [coe_map, coe_comap, set.image_eq_preimage_of_inverse hl hr]

end subgroup

