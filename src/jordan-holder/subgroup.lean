import group_theory.subgroup
import algebra.punit_instances

namespace subgroup

variables {G H K : Type*} [group G] [group H] [group K]

@[simp] lemma coe_inj {H : subgroup G} (x y : H) : (x : G) = y ↔ x = y := set_coe.ext_iff

@[simp] lemma range_subtype (H : subgroup G) : H.subtype.range = H :=
ext' $ H.subtype.coe_range.trans subtype.range_coe

variable (G)
def equiv_top : G ≃* (⊤ : subgroup G):=
{ to_fun := λ x, ⟨x, mem_top x⟩,
  inv_fun := λ x, x.val,
  left_inv := λ x, rfl,
  right_inv := λ x, subtype.ext_iff_val.mpr rfl,
  map_mul' := λ x y, rfl }

variable {G}
@[simp]
lemma equiv_top_symm_apply : (equiv_top G).symm.to_monoid_hom = subgroup.subtype ⊤ :=
monoid_hom.ext $ λ x, rfl

instance (N K : subgroup G) [hN : N.normal] [hK : K.normal] : normal (N ⊔ K) :=
⟨λ h (hh : h ∈ ↑(N ⊔ K)) g, show g * h * g⁻¹ ∈ ↑(N ⊔ K), begin
  rw mul_normal at *, rcases hh with ⟨n, k, hn, hk, rfl⟩,
  use [g * n * g⁻¹, g * k * g⁻¹, hN.conj_mem n hn g, hK.conj_mem k hk g],
  simp,
end⟩

instance (N K : subgroup G) [hN : N.normal] [hK : K.normal] : normal (N ⊓ K) :=
⟨λ h hh g, mem_inf.mpr ⟨hN.conj_mem _ (mem_inf.mp hh).1 _, hK.conj_mem _ (mem_inf.mp hh).2 _⟩⟩

instance (N : subgroup G) [N.normal] (e : G ≃* H) : normal (map e.to_monoid_hom N) := sorry

variables {f : G →* H} {g : H →* K}

open monoid_hom

lemma range_comp : (g.comp f).range = map g f.range :=
by rw [range_eq_map, ←map_map, range_eq_map]

lemma map_eq_comap_of_inverse {g : H →* G} (hl : function.left_inverse g f)
  (hr : function.right_inverse g f) (K : subgroup G) : map f K = comap g K :=
ext' $ by rw [coe_map, coe_comap, set.image_eq_preimage_of_inverse hl hr]

lemma map_comap_eq (hf : function.surjective f) (K : subgroup H) :
  map f (comap f K) = K :=
ext' $ by rw [coe_map, coe_comap, set.image_preimage_eq ↑K hf]

lemma ker_le_comap {K : subgroup H} : f.ker ≤ comap f K :=
(gc_map_comap f).monotone_u bot_le

lemma le_ker_iff_map {K : subgroup G} : K ≤ f.ker ↔ map f K = ⊥ :=
by rw [ker, eq_bot_iff, gc_map_comap]

lemma range_inclusion {H K : subgroup G} (h : H ≤ K) :
  (inclusion h).range = comap K.subtype H := sorry

lemma comap_subtype (H K : subgroup G) : comap K.subtype H = comap K.subtype (K ⊓ H) := sorry

lemma inclusion_injective {H K : subgroup G} {h : H ≤ K} : function.injective (inclusion h)
| ⟨_, _⟩ ⟨_, _⟩ := subtype.ext_iff_val.2 ∘ subtype.ext_iff_val.1

lemma subsingleton_subgroup_iff {H : subgroup G} : subsingleton H ↔ H = ⊥ :=
⟨λ h, le_antisymm (λ a ha, sorry) bot_le,
λ h, subsingleton.intro $ λ ⟨a, ha⟩ ⟨b, hb⟩, by { rw h at *, congr, rw [mem_bot.mp ha, mem_bot.mp hb] }⟩

lemma comap_subtype_top : comap (subgroup.subtype ⊤) = map (equiv_top G).to_monoid_hom :=
funext $ λ H, by rw [@map_eq_comap_of_inverse _ _ _ _ (equiv_top G).to_monoid_hom
  (equiv_top G).symm.to_monoid_hom (equiv_top G).left_inv (equiv_top G).right_inv,
  equiv_top_symm_apply]

end subgroup

namespace monoid_hom

open subgroup

variables {G H : Type*} [group G] [group H]

@[simp] lemma range_one : (1 : G →* H).range = ⊥ :=
subgroup.ext $ λ x, ⟨
  λ ⟨y, hy⟩, mem_bot.mpr (hy ▸ one_apply _),
  λ hx, ⟨1, (mem_bot.mp hx).symm ▸ one_apply _⟩
⟩

lemma injective_iff_ker_eq_bot (f : G →* H) : function.injective f ↔ f.ker = ⊥ :=
iff.trans (injective_iff f)
  ⟨λ h, le_antisymm (λ x hx, subgroup.mem_bot.mpr $ h x $ (mem_ker f).mp hx) bot_le,
  λ h x hx, by { rwa [←mem_ker, h, subgroup.mem_bot] at hx }⟩

instance range_subsingleton {f : G →* H} [subsingleton G] : subsingleton f.range :=
⟨λ ⟨a, x, hx⟩ ⟨b, y, hy⟩, by simp only [←hx, ←hy, subsingleton.elim x y]⟩

lemma range_subsingleton_eq_bot (f : G →* H) [subsingleton G] : f.range = ⊥ :=
by rw ←subsingleton_subgroup_iff.mp monoid_hom.range_subsingleton; apply_instance

lemma mem_range_self (f : G →* H) (x : G) : f x ∈ f.range := mem_range.mpr ⟨x, rfl⟩

def range_restrict (f : G →* H) : G →* f.range :=
f.cod_restrict f.range f.mem_range_self

end monoid_hom

namespace mul_equiv

variables {G H : Type*} [group G] [group H]
variables {f : G →* H}

def of_left_inverse {g : H → G} (h : function.left_inverse g f) : G ≃* f.range :=
{ to_fun := f.range_restrict,
  inv_fun := g ∘ f.range.subtype,
  left_inv := h,
  right_inv := λ x, subtype.ext $
    let ⟨x', hx'⟩ := monoid_hom.mem_range.mp x.prop in
    show f (g x) = x, by rw [←hx', h x'],
  .. f.range_restrict }

noncomputable def of_injective (h : function.injective f) : G ≃* f.range :=
of_left_inverse $ classical.some_spec h.has_left_inverse

def of_subsingleton (h : subsingleton G) : G ≃* punit :=
⟨λ _, punit.star, λ _, 1, λ x, subsingleton.elim _ _, λ x, subsingleton.elim _ _, λ _ _, rfl⟩

end mul_equiv

namespace subgroup

section maximal_normal_subgroup

variables {G : Type*} [group G]

/-- A maximal normal subgroup `N` of `G` is a normal proper subgroup that is not properly
contained in any other normal subgroups, except for `G` itself. -/
def maximal_normal_subgroup (N : subgroup G) : Prop :=
  N.normal ∧ N ≠ ⊤ ∧ ∀ (K : subgroup G) [K.normal], N ≤ K → K = N ∨ K = ⊤

lemma sup_maximal_normal_subgroup {N K : subgroup G} (hN : maximal_normal_subgroup N)
  (hK : maximal_normal_subgroup K) (h : N ≠ K) : N ⊔ K = ⊤ :=
begin
  haveI := hN.1, haveI := hK.1,
  have h1 := hN.2.2 (N ⊔ K) le_sup_left,
  have h2 := hK.2.2 (N ⊔ K) le_sup_right,
  cases h1, swap, { exact h1 },
  exfalso, apply h (le_antisymm _ (h1 ▸ le_sup_right)),
  cases h2, swap, { apply absurd _ hN.2.1, rw [←h1, h2] },
  exact h2 ▸ le_sup_left,
end

end maximal_normal_subgroup

end subgroup