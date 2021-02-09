import group_theory.subgroup

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

instance normal_inf (H N : subgroup G) [hN : N.normal] : ((H ⊓ N).comap H.subtype).normal :=
⟨λ x hx g, begin
  simp only [mem_inf, coe_subtype, mem_comap] at hx,
  simp only [coe_mul, mem_inf, coe_subtype, coe_inv, mem_comap],
  exact ⟨H.mul_mem (H.mul_mem g.2 hx.1) (H.inv_mem g.2), hN.1 x hx.2 g⟩,
end⟩

/- The inclusion homomorphism from a subgroup `H` contained in `K` to `K`. -/
def inclusion {H K : subgroup G} (h : H ≤ K) : H →* K :=
monoid_hom.mk' (λ ⟨x, hx⟩, ⟨x, h hx⟩) (λ ⟨a, ha⟩  ⟨b, hb⟩, rfl)

@[simp]
lemma coe_inclusion {H K : subgroup G} {h : H ≤ K} (a : H) : (inclusion h a : G) = a :=
by { cases a, simp only [inclusion, coe_mk, monoid_hom.coe_mk'] }

/- The internal product `HN` of a subgroup `H` and a normal subgroup `N` is a subgroup. -/
def prod_normal (H N : subgroup G) [hN : N.normal] : subgroup G :=
{ carrier := { g | ∃ (h ∈ H) (n ∈ N), g = h * n },
  one_mem' := ⟨1, H.one_mem, 1, N.one_mem, by rw mul_one⟩,
  mul_mem' := λ a b ⟨h, hh, n, hn, ha⟩ ⟨h', hh', n', hn', hb⟩,
    ⟨h * h', H.mul_mem hh hh',
    h'⁻¹ * n * h' * n', N.mul_mem (by simpa using hN.conj_mem _ hn h'⁻¹) hn',
    by simp [ha, hb, mul_assoc]⟩,
  inv_mem' := λ x ⟨h, hh, n, hn, hx⟩, 
    ⟨h⁻¹, H.inv_mem hh, 
    h * n⁻¹ * h⁻¹, hN.conj_mem _ (N.inv_mem hn) h,
    by rw [mul_assoc h, inv_mul_cancel_left, hx, mul_inv_rev]⟩}

lemma le_prod_normal_left {H N : subgroup G} [N.normal] : H ≤ H.prod_normal N :=
λ x hx, ⟨x, hx, 1, N.one_mem, by rw mul_one⟩

lemma le_prod_normal_right {H N : subgroup G} [N.normal] : N ≤ H.prod_normal N :=
λ x hx, ⟨1, H.one_mem, x, hx, by rw one_mul⟩

end subgroup

namespace monoid_hom

@[simp] lemma range_one {G H : Type*} [group G] [group H] : (1 : G →* H).range = ⊥ :=
subgroup.ext $ λ x, ⟨
  λ ⟨y, hy⟩, subgroup.mem_bot.mpr (hy ▸ one_apply _),
  λ hx, ⟨1, (subgroup.mem_bot.mp hx).symm ▸ one_apply _⟩
⟩

end monoid_hom