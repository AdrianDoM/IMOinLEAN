import category_theory.isomorphism_classes
import group_theory.quotient_group
import .subgroup .normal_embedding .simple_group .trivial_class .quotient_group .fingroup

universe u

inductive normal_series : Group.{u} → Type (u+1)
| trivial {G : Group} (hG : subsingleton G) : normal_series G
| cons (H G : Group)
  (f : normal_embedding H G) (s : normal_series H) : normal_series G

namespace normal_series

variables {G H K N : Group.{u}}

/- Given a normal series for G and an isomorphism G ≃* H, we can produce a normal series for H
by changing the last step from going into G to go into H. -/
def of_mul_equiv (h : G ≃* H) : normal_series G → normal_series H
| (trivial hG) := trivial $ @equiv.subsingleton.symm _ _ h.to_equiv hG
| (cons K G f s) := cons K H (normal_embedding.comp_mul_equiv f h) s

open category_theory quotient_group normal_embedding monoid_hom subgroup

/- The factors of a normal series are the quotient groups of consecutive elements in the series. -/
@[simp]
def factors : Π {G : Group.{u}}, normal_series G → multiset (isomorphism_classes.obj $ Cat.of Group)
| _ (trivial _) := 0
| _ (cons H G f s) := quotient.mk' (Group.of $ quotient_group.quotient f.φ.range) ::ₘ factors s

-- def append : Π {G : Group.{u}} (f : normal_embedding N G),
--   normal_series N → normal_series (Group.of f.quotient) → normal_series G
-- | G f (trivial hH) (trivial hG) :=
--   trivial $ subsingleton_of_subgroup_quotient_subsingleton (by { haveI := hH, apply_instance }) hG
-- | G f σ (trivial hG) :=
--   of_mul_equiv ((mul_equiv.of_injective f.inj).trans (@equiv_of_subsingleton_quotient _ _ _ f.norm hG)) σ
-- | G f (trivial hH) (cons K L g s) :=
--   of_mul_equiv begin
--     haveI := f.norm, have : f.φ.range = ⊥ := range_subsingleton_eq_bot f,
--     exact (equiv_quotient_of_eq this).trans quotient_bot,
--   end (cons K L g s)
-- | G f σ (cons K _ g s) := cons
--   (Group.of $ @subgroup.comap G _ f.quotient _ (@quotient_group.mk' G _ f.φ.range f.norm) g.φ.range)
--   G { to_fun := λ (x : ↥(subgroup.comap _ _)), x, map_one' := rfl, map_mul' := λ x y, rfl,
--     inj := λ x y h, by simpa using h,
--     norm := by { simp, } }
--   sorry

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
  composition_series (Group.of $ quotient_group.quotient N) → composition_series G := sorry
-- λ σ τ, ⟨append σ.val τ.val, sorry⟩

lemma factors_join {N : subgroup G} [hN : N.normal] {σ : composition_series (Group.of N)}
  {τ : composition_series (Group.of $ quotient_group.quotient N)} : 
  (join σ τ).val.factors = sorry := sorry

variables [hG : fintype G]

local attribute [instance] classical.prop_decidable

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

/- Jordan-Hölder 1. Every finite group has a composition series. -/
noncomputable lemma exists_composition_series_of_finite' :
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
  rcases exists_maximal_normal_subgroup h1 with ⟨N, hN⟩,
  haveI := hN.1, -- Add N.normal to instance cache
  have σ : composition_series (Group.of N) := ih (fintype.card N) (hn ▸ card_lt hN.2.1) _ _ _,
  swap, { rw Group.coe_of, apply_instance }, swap, { simp only [Group.coe_of] },
  rw maximal_normal_subgroup_iff at hN,
  existsi cons (Group.of N) H (of_normal_subgroup N) σ.val,
  intros G' hG', simp at hG',
  cases hG', swap, { exact σ.prop G' hG' },
  haveI : N.subtype.range.normal := (of_normal_subgroup N).norm,
  rw class_eq (equiv_quotient_of_eq (range_subtype N)) at hG',
  simp [hG'], exact hN,
end

/- Jordan-Hölder 2. Any two composition series for `G` have the same factors. -/
theorem eq_factors_of_composition_series (G : Group) [hG : fintype G] (σ τ : composition_series G) :
  σ.val.factors = τ.val.factors := sorry

end normal_series
