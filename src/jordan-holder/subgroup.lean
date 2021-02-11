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

section pointwise

@[to_additive]
lemma closure_mul_le (S T : set G) : closure (S * T) ≤ closure S ⊔ closure T :=
Inf_le $ λ x ⟨s, t, hs, ht, hx⟩, hx ▸ (closure S ⊔ closure T).mul_mem
    (le_def.mp le_sup_left $ subset_closure hs)
    (le_def.mp le_sup_right $ subset_closure ht)

@[to_additive]
lemma sup_eq_closure (H K : subgroup G) : H ⊔ K = closure (H * K) :=
le_antisymm
  (sup_le
    (λ h hh, subset_closure ⟨h, 1, hh, K.one_mem, mul_one h⟩)
    (λ k hk, subset_closure ⟨1, k, H.one_mem, hk, one_mul k⟩))
  (by conv_rhs { rw [← closure_eq H, ← closure_eq K] }; apply closure_mul_le)

@[to_additive]
private def mul_normal_aux (H N : subgroup G) [hN : N.normal] : subgroup G :=
{ carrier := (H : set G) * N,
  one_mem' := ⟨1, 1, H.one_mem, N.one_mem, by rw mul_one⟩,
  mul_mem' := λ a b ⟨h, n, hh, hn, ha⟩ ⟨h', n', hh', hn', hb⟩,
    ⟨h * h', h'⁻¹ * n * h' * n',
    H.mul_mem hh hh', N.mul_mem (by simpa using hN.conj_mem _ hn h'⁻¹) hn',
    by simp [← ha, ← hb, mul_assoc]⟩,
  inv_mem' := λ x ⟨h, n, hh, hn, hx⟩,
    ⟨h⁻¹, h * n⁻¹ * h⁻¹, H.inv_mem hh, hN.conj_mem _ (N.inv_mem hn) h,
    by rw [mul_assoc h, inv_mul_cancel_left, ← hx, mul_inv_rev]⟩ }

/-- The carrier of `H ⊔ N` is just `↑H * ↑N` (pointwise set product) when `N` is normal. -/
@[to_additive "The carrier of `H ⊔ N` is just `↑H + ↑N` (pointwise set addition)
when `N` is normal."]
lemma mul_normal (H N : subgroup G) [N.normal] : (↑(H ⊔ N) : set G) = H * N :=
set.subset.antisymm
  (show H ⊔ N ≤ mul_normal_aux H N,
    by { rw sup_eq_closure, apply Inf_le _, dsimp, refl })
  ((sup_eq_closure H N).symm ▸ subset_closure)

@[to_additive]
private def normal_mul_aux (N H : subgroup G) [hN : N.normal] : subgroup G :=
{ carrier := (N : set G) * H,
  one_mem' := ⟨1, 1, N.one_mem, H.one_mem, by rw mul_one⟩,
  mul_mem' := λ a b ⟨n, h, hn, hh, ha⟩ ⟨n', h', hn', hh', hb⟩,
    ⟨n * (h * n' * h⁻¹), h * h',
    N.mul_mem hn (hN.conj_mem _ hn' _), H.mul_mem hh hh',
    by simp [← ha, ← hb, mul_assoc]⟩,
  inv_mem' := λ x ⟨n, h, hn, hh, hx⟩,
    ⟨h⁻¹ * n⁻¹ * h, h⁻¹,
    by simpa using hN.conj_mem _ (N.inv_mem hn) h⁻¹, H.inv_mem hh,
    by rw [mul_inv_cancel_right, ← mul_inv_rev, hx]⟩ }

/-- The carrier of `N ⊔ H` is just `↑N * ↑H` (pointwise set product) when `N` is normal. -/
@[to_additive "The carrier of `N ⊔ H` is just `↑N + ↑H` (pointwise set addition)
when `N` is normal."]
lemma normal_mul (N H : subgroup G) [N.normal] : (↑(N ⊔ H) : set G) = N * H :=
set.subset.antisymm
  (show N ⊔ H ≤ normal_mul_aux N H,
    by { rw sup_eq_closure, apply Inf_le _, dsimp, refl })
  ((sup_eq_closure N H).symm ▸ subset_closure)

end pointwise

end subgroup

namespace monoid_hom

@[simp] lemma range_one {G H : Type*} [group G] [group H] : (1 : G →* H).range = ⊥ :=
subgroup.ext $ λ x, ⟨
  λ ⟨y, hy⟩, subgroup.mem_bot.mpr (hy ▸ one_apply _),
  λ hx, ⟨1, (subgroup.mem_bot.mp hx).symm ▸ one_apply _⟩
⟩

end monoid_hom