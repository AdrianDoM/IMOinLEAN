import group_theory.subgroup

namespace add_subgroup

variables {G : Type*} [add_group G]

instance sup_normal (N K : add_subgroup G) [hN : N.normal] [hK : K.normal] : normal (N ⊔ K) :=
⟨λ h (hh : h ∈ ↑(N ⊔ K)) g, show g + h + -g ∈ ↑(N ⊔ K), begin
  rw add_normal at *, rcases hh with ⟨n, k, hn, hk, rfl⟩,
  use [g + n + -g, g + k + -g, hN.conj_mem n hn g, hK.conj_mem k hk g],
  simp [add_assoc, sub_eq_add_neg],
end⟩

end add_subgroup

namespace subgroup

variables {G H K : Type*} [group G] [group H] [group K]

@[simp, to_additive]
lemma coe_inj {H : subgroup G} (x y : H) : (x : G) = y ↔ x = y := set_coe.ext_iff

@[simp, to_additive]
lemma range_subtype (H : subgroup G) : H.subtype.range = H :=
ext' $ H.subtype.coe_range.trans subtype.range_coe

variable (G)
@[to_additive]
def equiv_top : G ≃* (⊤ : subgroup G):=
{ to_fun := λ x, ⟨x, mem_top x⟩,
  inv_fun := λ x, x.val,
  left_inv := λ x, rfl,
  right_inv := λ x, subtype.ext_iff_val.mpr rfl,
  map_mul' := λ x y, rfl }

variable {G}
@[simp, to_additive]
lemma equiv_top_symm_apply : (equiv_top G).symm.to_monoid_hom = subgroup.subtype ⊤ :=
monoid_hom.ext $ λ x, rfl

@[to_additive]
instance sup_normal (N K : subgroup G) [hN : N.normal] [hK : K.normal] : normal (N ⊔ K) :=
⟨λ h (hh : h ∈ ↑(N ⊔ K)) g, show g * h * g⁻¹ ∈ ↑(N ⊔ K), begin
  rw mul_normal at *, rcases hh with ⟨n, k, hn, hk, rfl⟩,
  use [g * n * g⁻¹, g * k * g⁻¹, hN.conj_mem n hn g, hK.conj_mem k hk g],
  simp,
end⟩

@[to_additive]
instance inf_normal (N K : subgroup G) [hN : N.normal] [hK : K.normal] : normal (N ⊓ K) :=
⟨λ h hh g, mem_inf.mpr ⟨hN.conj_mem _ (mem_inf.mp hh).1 _, hK.conj_mem _ (mem_inf.mp hh).2 _⟩⟩


open monoid_hom

@[to_additive]
lemma comap_mono {f : G →* H} {K K' : subgroup H} : K ≤ K' → comap f K ≤ comap f K' :=
set.preimage_mono

@[to_additive]
lemma map_mono {f : G →* H} {K K' : subgroup G} : K ≤ K' → map f K ≤ map f K' :=
set.image_subset _

@[to_additive]
lemma range_comp (f : G →* H) (g : H →* K) : (g.comp f).range = map g f.range :=
ext' $ set.range_comp g f

variables {f : G →* H} {g : H →* K}

@[to_additive]
lemma map_eq_comap_of_inverse {g : H →* G} (hl : function.left_inverse g f)
  (hr : function.right_inverse g f) (K : subgroup G) : map f K = comap g K :=
ext' $ by rw [coe_map, coe_comap, set.image_eq_preimage_of_inverse hl hr]

@[to_additive]
lemma map_comap_eq (hf : function.surjective f) (K : subgroup H) :
  map f (comap f K) = K :=
ext' $ by rw [coe_map, coe_comap, set.image_preimage_eq ↑K hf]

@[to_additive]
lemma comap_map_eq (hf : function.injective f) (K : subgroup G) :
  comap f (map f K) = K :=
ext' $ by rw [coe_comap, coe_map, set.preimage_image_eq ↑K hf]

@[to_additive]
lemma comap_injective (h : function.surjective f) : function.injective (comap f) :=
λ K L hKL, by { apply_fun map f at hKL, simpa [map_comap_eq h] using hKL }

@[to_additive]
lemma map_injective (h : function.injective f) : function.injective (map f) :=
λ K L hKL, by { apply_fun comap f at hKL, simpa [comap_map_eq h] using hKL }

@[to_additive]
lemma ker_le_comap {K : subgroup H} : f.ker ≤ comap f K :=
(gc_map_comap f).monotone_u bot_le

@[to_additive]
lemma le_ker_iff_map {K : subgroup G} : K ≤ f.ker ↔ map f K = ⊥ :=
by rw [ker, eq_bot_iff, gc_map_comap]

@[to_additive]
lemma range_inclusion {H K : subgroup G} (h : H ≤ K) :
  (inclusion h).range = comap K.subtype H :=
begin
  ext, split,
  { intro hx, simp [inclusion] at *, rcases hx with ⟨x', rfl⟩, exact x'.prop },
  intro hx, simp [inclusion] at *, use ⟨x.val, hx⟩, rw subtype.ext_iff_val, refl, 
end

@[to_additive]
lemma comap_subtype (H K : subgroup G) : comap K.subtype H = comap K.subtype (K ⊓ H) :=
le_antisymm (λ x hx, by simpa) ((gc_map_comap K.subtype).monotone_u inf_le_right)

@[to_additive]
lemma inclusion_injective {H K : subgroup G} {h : H ≤ K} : function.injective (inclusion h)
| ⟨_, _⟩ ⟨_, _⟩ := subtype.ext_iff_val.2 ∘ subtype.ext_iff_val.1

@[to_additive]
lemma subsingleton_subgroup_iff {H : subgroup G} : subsingleton H ↔ H = ⊥ :=
⟨λ h, le_antisymm (λ a ha, mem_bot.mpr $ subtype.mk_eq_mk.mp $
  @subsingleton.elim _ h ⟨a, ha⟩ ⟨1, one_mem H⟩) bot_le,
λ h, subsingleton.intro $ λ ⟨a, ha⟩ ⟨b, hb⟩, by { rw h at *, congr, rw [mem_bot.mp ha, mem_bot.mp hb] }⟩

@[to_additive]
lemma comap_subtype_top : comap (subgroup.subtype ⊤) = map (equiv_top G).to_monoid_hom :=
funext $ λ H, by rw [@map_eq_comap_of_inverse _ _ _ _ (equiv_top G).to_monoid_hom
  (equiv_top G).symm.to_monoid_hom (equiv_top G).left_inv (equiv_top G).right_inv,
  equiv_top_symm_apply]

@[to_additive]
lemma normal.mul_equiv_map {N : subgroup G} (hN : N.normal) (e : G ≃* H) :
  normal (map e.to_monoid_hom N) :=
by rw @map_eq_comap_of_inverse _ _ _ _
  e.to_monoid_hom e.symm.to_monoid_hom e.left_inv e.right_inv;
  apply_instance

@[to_additive]
instance (N : subgroup G) [hN : N.normal] (e : G ≃* H) :
  normal (map e.to_monoid_hom N) :=
normal.mul_equiv_map hN e

end subgroup

namespace monoid_hom

open subgroup

variables {G H : Type*} [group G] [group H]

@[simp, to_additive] lemma range_one : (1 : G →* H).range = ⊥ :=
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

@[to_additive]
lemma mem_range_self (f : G →* H) (x : G) : f x ∈ f.range := mem_range.mpr ⟨x, rfl⟩

@[to_additive]
def range_restrict (f : G →* H) : G →* f.range :=
f.cod_restrict f.range f.mem_range_self

end monoid_hom

namespace mul_equiv

variables {G H : Type*} [group G] [group H]
variables {f : G →* H}

@[to_additive]
def of_left_inverse {g : H → G} (h : function.left_inverse g f) : G ≃* f.range :=
{ to_fun := f.range_restrict,
  inv_fun := g ∘ f.range.subtype,
  left_inv := h,
  right_inv := λ x, subtype.ext $
    let ⟨x', hx'⟩ := monoid_hom.mem_range.mp x.prop in
    show f (g x) = x, by rw [←hx', h x'],
  .. f.range_restrict }

@[to_additive]
noncomputable def of_injective (h : function.injective f) : G ≃* f.range :=
of_left_inverse $ classical.some_spec h.has_left_inverse

@[to_additive]
def of_subsingleton (hG : subsingleton G) (hH : subsingleton H) : G ≃* H :=
{ to_fun := λ _, 1,
  inv_fun := λ _, 1,
  left_inv := λ x, @subsingleton.elim _ hG _ _,
  right_inv := λ y, @subsingleton.elim _ hH _ _,
  map_mul' := λ x y, (one_mul 1).symm }

end mul_equiv

namespace subgroup

section maximal_normal_subgroup

variables {G : Type*} [group G]

/-- A maximal normal subgroup `N` of `G` is a normal proper subgroup that is not properly
contained in any other normal subgroups, except for `G` itself. -/
@[to_additive]
def maximal_normal_subgroup (N : subgroup G) : Prop :=
  N.normal ∧ N ≠ ⊤ ∧ ∀ (K : subgroup G) [K.normal], N ≤ K → K = N ∨ K = ⊤

@[to_additive]
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