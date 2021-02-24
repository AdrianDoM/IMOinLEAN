import group_theory.subgroup
import algebra.pointwise

namespace subgroup

variables {G H K : Type*} [group G] [group H] [group K]

@[simp] lemma range_subtype (H : subgroup G) : H.subtype.range = H :=
ext' $ H.subtype.coe_range.trans subtype.range_coe

lemma map_eq_comap_of_inverse {f : G →* H} {g : H →* G} (hl : function.left_inverse g f)
  (hr : function.right_inverse g f) (K : subgroup G) : map f K = comap g K :=
ext' $ by rw [coe_map, coe_comap, set.image_eq_preimage_of_inverse hl hr]

lemma map_comap_eq {f : G →* H} (hf : function.surjective f) (K : subgroup H) :
  map f (comap f K) = K :=
ext' $ by rw [coe_map, coe_comap, set.image_preimage_eq ↑K hf]

end subgroup

namespace monoid_hom

variables {G H : Type*} [group G] [group H]

@[simp] lemma range_one : (1 : G →* H).range = ⊥ :=
subgroup.ext $ λ x, ⟨
  λ ⟨y, hy⟩, subgroup.mem_bot.mpr (hy ▸ one_apply _),
  λ hx, ⟨1, (subgroup.mem_bot.mp hx).symm ▸ one_apply _⟩
⟩

lemma injective_iff_ker_eq_bot (f : G →* H) : function.injective f ↔ f.ker = ⊥ :=
iff.trans (injective_iff f)
  ⟨λ h, le_antisymm (λ x hx, subgroup.mem_bot.mpr $ h x $ (mem_ker f).mp hx) bot_le,
  λ h x hx, by { rwa [←mem_ker, h, subgroup.mem_bot] at hx }⟩

instance range_subsingleton (f : G →* H) [subsingleton G] : subsingleton f.range :=
⟨λ ⟨a, x, hx⟩ ⟨b, y, hy⟩, by simp only [←hx, ←hy, subsingleton.elim x y]⟩

end monoid_hom