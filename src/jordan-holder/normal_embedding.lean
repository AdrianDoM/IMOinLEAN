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

/- Coerce a normal embedding to a group homomorphism -/
instance : has_coe (normal_embedding G H) (G →* H) := ⟨normal_embedding.φ⟩

/- The unique normal embedding from the trivial group to any group -/
protected def from_punit : normal_embedding punit G :=
⟨1, λ _ _ _, subsingleton.elim _ _,
  (@monoid_hom.range_one punit G _ _).symm ▸ subgroup.bot_normal⟩

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

instance group_quotient (f : normal_embedding G H) : group (quotient_group.quotient f.φ.range) :=
  sorry -- apply the instance from quotient_group

end normal_embedding
