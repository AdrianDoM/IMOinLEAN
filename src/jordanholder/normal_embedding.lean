import algebra.punit_instances
import algebra.category.Group
import group_theory.subgroup
import group_theory.quotient_group
import .subgroup .quotient_group

open subgroup monoid_hom

structure normal_embedding (G H : Type*) [group G] [group H]
  extends φ : G →* H :=
(inj : function.injective φ)
(norm : φ.range.normal)

structure add_normal_embedding (G H : Type*) [add_group G] [add_group H]
  extends φ : G →+ H :=
(inj : function.injective φ)
(norm : φ.range.normal)

attribute [to_additive add_normal_embedding] normal_embedding

namespace normal_embedding

variables {G H K : Type*} [group G] [group H] [group K]

@[to_additive]
instance normal (f : normal_embedding G H) : f.φ.range.normal := f.norm

/- Coerce a normal embedding to a group homomorphism -/
@[to_additive]
instance : has_coe (normal_embedding G H) (G →* H) := ⟨normal_embedding.φ⟩

/- The unique normal embedding from the trivial group to any group -/
@[to_additive]
def from_subsingleton (hG : subsingleton G) (H : Type*) [group H] : normal_embedding G H :=
⟨1, λ x y _, subsingleton.elim x y, (@monoid_hom.range_one G H _ _).symm ▸ subgroup.bot_normal⟩

@[simp, to_additive]
lemma from_subsingleton_range {hG : subsingleton G} : (from_subsingleton hG H).φ.range = ⊥ :=
le_antisymm (by { rintros x ⟨y, rfl⟩, rw [subsingleton.elim y 1, map_one, mem_bot] }) bot_le

/- A group isomorphism induces a normal embedding -/
@[to_additive]
def of_mul_equiv (h : G ≃* H) : normal_embedding G H :=
⟨h.to_monoid_hom, h.left_inv.injective,
  suffices heq : h.to_monoid_hom.range = ⊤, from heq.substr subgroup.top_normal,
  set_like.ext' (h.to_monoid_hom.coe_range.trans $ h.surjective.range_eq)⟩

/- A normal embedding from `G` to `H` can be composed with a group isomorphism
`H ≃* K` to produce a normal embedding from `G` to `K` -/
@[to_additive]
def comp_mul_equiv (f : normal_embedding G H) (h : H ≃* K) : normal_embedding G K :=
{ φ := h.to_monoid_hom.comp f,
  inj := function.injective.comp h.left_inv.injective f.inj, 
  norm := by rw range_comp; exact normal.mul_equiv_map f.norm h }

open quotient_group

@[to_additive]
instance group_quotient (f : normal_embedding G H) : group (quotient f.φ.range) :=
by haveI := f.norm; apply_instance

@[to_additive]
def of_normal_subgroup (N : subgroup G) [N.normal] : normal_embedding N G :=
⟨N.subtype, λ x y hx, by simpa using hx, (range_subtype N).symm ▸ infer_instance⟩

@[simp, to_additive]
lemma range_of_normal_subgroup (N : subgroup G) [N.normal] :
  (of_normal_subgroup N).φ.range = N :=
by simp only [of_normal_subgroup, range_subtype]

@[to_additive]
def of_normal_subgroup_to_subgroup {K N : subgroup G} [N.normal] (h : N ≤ K) :
  normal_embedding N K :=
⟨inclusion h, inclusion_injective, by { rw range_inclusion, apply_instance }⟩

@[to_additive]
noncomputable def equiv_range (f : normal_embedding G H) : G ≃* f.φ.range :=
mul_equiv.of_injective f.inj

@[to_additive]
noncomputable def equiv_quotient_comp_mul_equiv (f : normal_embedding G H) (e : H ≃* K) :
  quotient (comp_mul_equiv f e).φ.range ≃* quotient f.φ.range :=
let ψ : K →* quotient f.φ.range := (mk' f.φ.range).comp e.symm.to_monoid_hom in
have hψ : function.surjective ψ := function.surjective.comp (surjective_quot_mk _) e.symm.surjective,
suffices h : ψ.ker = (comp_mul_equiv f e).φ.range,
  from (equiv_quotient_of_eq h.symm).trans (quotient_ker_equiv_of_surjective ψ hψ),
begin
  simp [ψ, comp_mul_equiv, ←comap_ker],
  have : comap e.symm.to_monoid_hom f.φ.range = map e.to_monoid_hom f.φ.range,
  { symmetry, apply map_eq_comap_of_inverse, exact e.left_inv, exact e.right_inv },
  rw this, simp [range_eq_map, ←map_map], refl,
end

@[to_additive]
noncomputable lemma fintype [fintype G] (f : normal_embedding H G)
  [decidable_pred (λ x, x ∈ f.φ.range)] : fintype H :=
fintype.of_equiv f.φ.range f.equiv_range.to_equiv.symm

variables (f : normal_embedding H G) (g : normal_embedding K G)

@[to_additive]
noncomputable def from_inf_range_left :
  normal_embedding ↥(f.φ.range ⊓ g.φ.range) H :=
comp_mul_equiv (of_normal_subgroup_to_subgroup inf_le_left) (equiv_range f).symm

@[to_additive]
noncomputable def from_inf_range_right :
  normal_embedding ↥(f.φ.range ⊓ g.φ.range) K :=
comp_mul_equiv (of_normal_subgroup_to_subgroup inf_le_right) (equiv_range g).symm

@[to_additive]
noncomputable def quotient_from_inf_range_left (h : f.φ.range ⊔ g.φ.range = ⊤) :
  quotient (from_inf_range_left f g).φ.range ≃* quotient g.φ.range :=
have h1 : quotient (from_inf_range_left f g).φ.range ≃*
  quotient (comap f.φ.range.subtype (f.φ.range ⊓ g.φ.range)),
by { apply (equiv_quotient_of_eq _).trans (equiv_quotient_of_equiv (equiv_range f).symm).symm,
  simp [from_inf_range_left, comp_mul_equiv, range_comp], congr,
  rw [comap_subtype, ←@range_inclusion _ _ _ f.φ.range inf_le_left], refl },
suffices h2 : quotient g.φ.range ≃* quotient (comap (f.φ.range ⊔ g.φ.range).subtype g.φ.range),
from h1.trans $ (quotient_inf_equiv_prod_normal_quotient _ _).trans h2.symm,
by { rw h, apply (equiv_quotient_of_equiv $ equiv_top G).trans (equiv_quotient_of_eq _),
  rw comap_subtype_top }

@[to_additive]
noncomputable def quotient_from_inf_range_right (h : f.φ.range ⊔ g.φ.range = ⊤) :
  quotient (from_inf_range_right f g).φ.range ≃* quotient f.φ.range :=
have h1 : quotient (from_inf_range_right f g).φ.range ≃*
  quotient (comap g.φ.range.subtype (f.φ.range ⊓ g.φ.range)),
by { apply (equiv_quotient_of_eq _).trans (equiv_quotient_of_equiv (equiv_range g).symm).symm,
  simp [from_inf_range_right, comp_mul_equiv, range_comp], congr,
  rw comap_subtype, conv_rhs { rw inf_comm },
  rw ←@range_inclusion _ _ _ g.φ.range inf_le_right, refl },
suffices h2 : quotient f.φ.range ≃* quotient (comap (f.φ.range ⊔ g.φ.range).subtype f.φ.range),
by { apply h1.trans (mul_equiv.trans _ h2.symm), rw sup_comm,
  apply (equiv_quotient_of_eq _).trans (quotient_inf_equiv_prod_normal_quotient _ _),
  rw inf_comm },
by { rw h, apply (equiv_quotient_of_equiv $ equiv_top G).trans (equiv_quotient_of_eq _),
  rw comap_subtype_top }

end normal_embedding
