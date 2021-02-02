import group_theory.subgroup
import ring_theory.subring

namespace subgroup

variables {G H K : Type*} [group G] [group H] [group K]

@[simp] lemma range_subtype (H : subgroup G) : H.subtype.range = H :=
ext' $ H.subtype.coe_range.trans subtype.range_coe

lemma map_eq_comap_of_inverse {f : G →* H} {g : H →* G} (hl : function.left_inverse g f)
  (hr : function.right_inverse g f) (K : subgroup G) : map f K = comap g K :=
ext' $ by rw [coe_map, coe_comap, set.image_eq_preimage_of_inverse hl hr]

lemma map_comp {f : G →* H} {g : H →* K} (G' : subgroup G) :
  map (g.comp f) G' = map g (map f G') := by library_search

end subgroup

#check set.image

namespace monoid_hom

@[simp] lemma range_one {G H : Type*} [group G] [group H] : (1 : G →* H).range = ⊥ :=
subgroup.ext $ λ x, ⟨
  λ ⟨y, hy⟩, subgroup.mem_bot.mpr (hy ▸ one_apply _),
  λ hx, ⟨1, (subgroup.mem_bot.mp hx).symm ▸ one_apply _⟩
⟩

end monoid_hom