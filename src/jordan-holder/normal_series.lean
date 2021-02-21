import category_theory.isomorphism_classes
import group_theory.quotient_group
import .subgroup .normal_embedding .simple_group .trivial_class .quotient_group .fingroup

universe u

inductive normal_series : Group.{u} → Type (u+1)
| trivial {G : Group} (hG : subsingleton G) : normal_series G
| cons (H G : Group)
  (f : normal_embedding H G) (s : normal_series H) : normal_series G

namespace normal_series

variables {G H K : Group.{u}}

/- Given a normal series for G and an isomorphism G ≃* H, we can produce a normal series for H
by changing the last step from going into G to go into H. -/
def of_mul_equiv_right (h : G ≃* H) : normal_series G → normal_series H
| (trivial hG) := trivial $ @equiv.subsingleton.symm _ _ h.to_equiv hG
| (cons K G f s) := cons K H (normal_embedding.comp_mul_equiv f h) s

open category_theory quotient_group normal_embedding

/- The factors of a normal series are the quotient groups of consecutive elements in the series. -/
@[simp]
def factors : Π {G : Group.{u}}, normal_series G → multiset (isomorphism_classes.obj $ Cat.of Group)
| _ (trivial _) := 0
| _ (cons H G f s) := quotient.mk' (Group.of $ quotient_group.quotient f.φ.range) ::ₘ factors s

example (N : subgroup G) [N.normal] : group (quotient_group.quotient N) := by { apply_instance } 

def append : Π {N : subgroup G} [N.normal], normal_series (Group.of N) →
  normal_series (Group.of $ quotient_group.quotient N) → normal_series G
| (trivial h1) (trivial h2) := trivial (subsingleton_of_subgroup_quotient_subsingleton h1 h2)
| (trivial h1) τ := sorry
| σ (trivial h2) := sorry
| σ τ := sorry

/- A composition series is a normal series with simple and nontrivial factors. -/
def composition_series (G : Group.{u}) : Type (u+1) :=
{ σ : normal_series G // ∀ G' ∈ σ.factors, is_simple_class G' ∧ ¬ is_trivial_class G' }

/- The unique composition series for a simple group. -/
def composition_series_of_simple_of_not_subsingleton (h1 : is_simple G) (h2 : ¬ subsingleton G) :
  composition_series G :=
⟨cons (Group.of punit) G (from_subsingleton punit.subsingleton G) (trivial punit.subsingleton),
λ H hH, begin
  simp at hH, simp [hH], sorry
end⟩

def join {N : subgroup G} [hN : N.normal] : composition_series (Group.of N) →
  composition_series (Group.of $ quotient_group.quotient N) → composition_series G :=
λ σ τ, ⟨append σ.val τ.val, sorry⟩

lemma factors_join {N : subgroup G} [hN : N.normal] {σ : composition_series (Group.of N)}
  {τ : composition_series (Group.of $ quotient_group.quotient N)} : 
  (join σ τ).val.factors = sorry := sorry

variables [hG : fintype G]

local attribute [instance] classical.prop_decidable
-- set_option trace.class_instances true

/- Jordan-Hölder 1. Every finite group has a composition series. -/
noncomputable lemma exists_composition_series_of_finite :
  composition_series G :=
suffices h : ∀ (n : ℕ) (G : Group) (hG : fintype G),
  @fintype.card G hG = n → composition_series G,
  from h (@fintype.card G hG) G hG rfl,
λ N, N.strong_rec_on $ begin
  intros n ih H, introI hH, intro hn,
  by_cases h1 : subsingleton H,
  { existsi trivial h1, intro, simp },
  by_cases h2 : is_simple H,
  { exact composition_series_of_simple_of_not_subsingleton h2 h1 },
  apply classical.subtype_of_exists,
  rcases not_is_simple.mp h2 with ⟨N, hN, hNbot, hNtop⟩,
  haveI := hN, -- Add N.normal to instance cache
  suffices s : composition_series H, from ⟨s.val, s.property⟩,
  apply @join _ N hN,
  { apply ih (fintype.card N) (hn ▸ subgroup.card_lt hNtop),
    { simp only [Group.coe_of, eq_self_iff_true] },
    rw Group.coe_of, apply_instance },
  apply ih (fintype.card $ quotient_group.quotient N),
  { rw ←hn, apply quotient_group.card_quotient_lt hNbot },
  { simp only [Group.coe_of, eq_self_iff_true] },
  rw Group.coe_of, apply_instance,
end

/- Jordan-Hölder 2. Any two composition series for `G` have the same factors. -/
theorem eq_factors_of_composition_series (G : Group) [hG : fintype G] (σ τ : composition_series G) :
  σ.val.factors = τ.val.factors := sorry

end normal_series
