import algebra.punit_instances
import algebra.category.Group
import group_theory.subgroup
import group_theory.quotient_group
import .subgroup

open subgroup monoid_hom

structure normal_embedding (G H : Type*) [group G] [group H]
  extends φ : monoid_hom G H :=
(inj : function.injective φ.to_fun)
(norm : φ.range.normal)

namespace normal_embedding

variables {G H K : Type*} [group G] [group H] [group K]

instance normal (f : normal_embedding G H) : f.φ.range.normal := f.norm

/- Coerce a normal embedding to a group homomorphism -/
instance : has_coe (normal_embedding G H) (G →* H) := ⟨normal_embedding.φ⟩

/- The unique normal embedding from the trivial group to any group -/
def from_subsingleton (hG : subsingleton G) (H : Type*) [group H] : normal_embedding G H :=
⟨1, λ x y _, subsingleton.elim x y, (@monoid_hom.range_one G H _ _).symm ▸ subgroup.bot_normal⟩

@[simp]
lemma from_subsingleton_range {hG : subsingleton G} : (from_subsingleton hG H).φ.range = ⊥ :=
le_antisymm (by { rintros x ⟨y, rfl⟩, rw [subsingleton.elim y 1, map_one, mem_bot] }) bot_le

/- A group isomorphism induces a normal embedding -/
def of_mul_equiv (h : G ≃* H) : normal_embedding G H :=
⟨h.to_monoid_hom, h.left_inv.injective,
  suffices heq : h.to_monoid_hom.range = ⊤, from heq.substr subgroup.top_normal,
  ext' (h.to_monoid_hom.coe_range.trans $ h.surjective.range_eq)⟩

/- A normal embedding from `G` to `H` can be composed with a group isomorphism
`H ≃* K` to produce a normal embedding from `G` to `K` -/
def comp_mul_equiv (f : normal_embedding G H) (h : H ≃* K) : normal_embedding G K :=
⟨h.to_monoid_hom.comp f, function.injective.comp h.left_inv.injective f.inj, 
  begin
    rw range_eq_map, convert normal.comap f.norm h.symm.to_monoid_hom,
    rw ← @map_eq_comap_of_inverse _ _ _ _ h.to_monoid_hom h.symm.to_monoid_hom h.left_inv h.right_inv,
    rw [← map_map, ← range_eq_map], refl
  end⟩

open quotient_group

instance group_quotient (f : normal_embedding G H) : group (quotient f.φ.range) :=
by haveI := f.norm; apply_instance

@[simp]
def of_normal_subgroup (N : subgroup G) [N.normal] : normal_embedding N G :=
⟨N.subtype, λ x y hx, by simpa using hx, (range_subtype N).symm ▸ infer_instance⟩

def of_normal_subgroup_to_subgroup {K N : subgroup G} [N.normal] (h : N ≤ K) :
  normal_embedding N K := sorry

noncomputable def equiv_range (f : normal_embedding G H) : G ≃* f.φ.range :=
mul_equiv.of_injective f.inj

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

noncomputable lemma fintype [fintype G] (f : normal_embedding H G)
  [decidable_pred f.φ.range.carrier] : fintype H :=
fintype.of_equiv f.φ.range f.equiv_range.to_equiv.symm

end normal_embedding
