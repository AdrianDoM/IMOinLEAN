import category_theory.isomorphism_classes
import group_theory.quotient_group
import .subgroup .normal_embedding .simple_group .trivial_class .quotient_group .fingroup

universe u

open category_theory quotient_group normal_embedding monoid_hom subgroup (hiding subtype)

inductive normal_series : Group.{u} → Type (u+1)
| trivial {G : Group} (hG : subsingleton G) : normal_series G
| cons (H G : Group)
  (f : normal_embedding H G) (s : normal_series H) : normal_series G

inductive add_normal_series : AddGroup.{u} → Type (u+1)
| trivial {G : AddGroup} (hG : subsingleton G) : add_normal_series G
| cons (H G : AddGroup)
  (f : add_normal_embedding H G) (s : add_normal_series H) : add_normal_series G

attribute [to_additive add_normal_series] normal_series

namespace normal_series

variables {G H K N : Group.{u}}

/-- If `G ≃* H` then we can build a normal series for `H` from a normal series for `G` by undoing
the last step and going into `H` instead. -/
def of_mul_equiv (e : G ≃* H) : normal_series G → normal_series H
| (trivial hG) := trivial $ @equiv.subsingleton.symm _ _ e.to_equiv hG
| (cons K G f s) := cons K H (normal_embedding.comp_mul_equiv f e) s

/-- If `G` is not trivial, it must have a nontrivial normal series. -/
@[to_additive]
lemma exists_cons_of_not_subsingleton (h : ¬ subsingleton G) :
  Π (σ : normal_series G), ∃ H f s, σ = cons H G f s
| (trivial hG) := absurd hG h
| (cons H G f s) := ⟨H, f, s, rfl⟩

/-- The factors of a normal series are the quotient groups of consecutive elements in the series. -/
def factors : Π {G : Group}, normal_series G → multiset (isomorphism_classes.obj $ Cat.of Group)
| _ (trivial _) := 0
| _ (cons H G f s) := quotient.mk' (Group.of $ quotient f.φ.range) ::ₘ factors s

end normal_series

namespace add_normal_series

variables {G H K N : AddGroup.{u}}

/-- If `G ≃+ H` then we can build a normal series for `H` from a normal series for `G` by undoing
the last step and going into `H` instead. -/
def of_add_equiv (e : G ≃+ H) : add_normal_series G → add_normal_series H
| (trivial hG) := trivial $ @equiv.subsingleton.symm _ _ e.to_equiv hG
| (cons K G f s) := cons K H (add_normal_embedding.comp_add_equiv f e) s

attribute [to_additive] normal_series.of_mul_equiv

open quotient_add_group

/-- The factors of a normal series are the quotient groups of consecutive elements in the series. -/
def factors : Π {G : AddGroup}, add_normal_series G → multiset (isomorphism_classes.obj $ Cat.of AddGroup)
| _ (trivial _) := 0
| _ (cons H G f s) := quotient.mk' (AddGroup.of $ quotient f.φ.range) ::ₘ factors s

attribute [to_additive] normal_series.factors

end add_normal_series

variables {G H K N : Group.{u}}

namespace normal_series

@[simp, to_additive]
lemma factors_trivial {hG : subsingleton G} : (trivial hG).factors = 0 := rfl

@[simp, to_additive]
lemma factors_cons {f : normal_embedding H G} {s : normal_series H} :
  (cons H G f s).factors = quotient.mk' (Group.of $ quotient f.φ.range) ::ₘ factors s :=
rfl

@[simp, to_additive]
lemma factors_of_mul_equiv (e : G ≃* H) :
  Π (σ : normal_series G), (of_mul_equiv e σ).factors = σ.factors
| (trivial hG) := by simp [of_mul_equiv]
| (cons K G f s) := begin
  simp only [of_mul_equiv, multiset.cons_inj_left, factors_cons],
  exact class_eq (equiv_quotient_comp_mul_equiv _ _),
end

end normal_series

/-- A composition series is a normal series with simple and nontrivial factors. -/
@[to_additive add_composition_series]
def composition_series (G : Group.{u}) : Type (u+1) :=
{ σ : normal_series G // ∀ G' ∈ σ.factors, is_simple_class G' ∧ ¬ is_trivial_class G' }

namespace composition_series

open normal_series multiset fingroup

/-- Construct a composition series for `G` from a composition series for `H`, a normal embedding
of `H` into `G` and a proof that the new factor introduced is simple and nontrivial. -/
@[to_additive]
def cons' (σ : composition_series H) (f : normal_embedding H G) 
  (h : is_simple (quotient f.φ.range) ∧ ¬ subsingleton (quotient f.φ.range)) :
  composition_series G :=
⟨cons _ _ f σ.val, λ G' hG',
  by { simp at hG', cases hG', { simpa [hG'] }, exact σ.prop _ hG' }⟩

@[simp, to_additive]
def factors_of_cons' {f : normal_embedding H G} {σ : composition_series H}
  {h : is_simple (quotient f.φ.range) ∧ ¬ subsingleton (quotient f.φ.range)} :
  (cons' σ f h).val.factors = quotient.mk' (Group.of $ quotient f.φ.range) ::ₘ σ.val.factors :=
by simp [cons']

/-- A trivial normal series is always a composition series. -/
@[to_additive]
def of_subsingleton (h : subsingleton G) : composition_series G :=
⟨trivial h, λ G' hG', absurd hG' $ multiset.not_mem_zero _⟩

/-- Given a composition series whose underlying normal series is constructed with `cons`, we can
produce a composition series from the normal series used in `cons`. -/
@[to_additive]
def of_cons {σ : composition_series G} {f : normal_embedding H G} {s : normal_series H} :
  σ.val = cons H G f s → composition_series H :=
λ h, ⟨s, λ G' hG', σ.prop G' (show G' ∈ σ.val.factors, by { simp [h, hG'] })⟩

@[simp, to_additive]
lemma factors_of_cons {σ : composition_series G} {f : normal_embedding H G} {s : normal_series H}
  (h : σ.val = cons H G f s) : (of_cons h).val.factors = s.factors := rfl

@[to_additive]
def of_mul_equiv (e : G ≃* H) : composition_series G → composition_series H :=
λ σ, ⟨normal_series.of_mul_equiv e σ.val, λ G' hG', σ.prop G' (by simpa using hG')⟩

@[simp, to_additive]
lemma factors_of_mul_equiv (e : G ≃* H) (σ : composition_series G) :
  (of_mul_equiv e σ).val.factors = σ.val.factors :=
normal_series.factors_of_mul_equiv e σ.val

-- TODO: Fix punit has_add instance
/-- Any composition series for the trivial group has no factors, i.e., it is a trivial series. -/
@[to_additive]
lemma factors_of_subsingleton (hG : subsingleton G) :
  Π (s : composition_series G), s.val.factors = 0
| ⟨trivial _, _⟩ := rfl
| ⟨cons H G f s, h⟩ := begin
  exfalso, apply (h (quotient.mk' (1 : Group)) _).2 is_trivial_class_one,
  rw [factors_cons, mem_cons], left, apply class_eq,
  have : subsingleton (quotient f.φ.range) := @quotient.subsingleton _ hG _,
  exact (mul_equiv.of_subsingleton this).symm,
end

/-- The unique composition series for a simple group. -/
@[to_additive]
def of_simple (h1 : is_simple G) (h2 : ¬ subsingleton G) :
  composition_series G :=
⟨cons (Group.of punit) G (from_subsingleton punit.subsingleton G) (trivial punit.subsingleton),
λ H hH, begin
  simp only [factors, multiset.mem_singleton] at hH,
  have : quotient (from_subsingleton punit.subsingleton ↥G).φ.range ≃* G :=
    mul_equiv.trans (equiv_quotient_of_eq from_subsingleton_range) quotient_bot,
  rw class_eq this at hH, simp [hH], use [h1, h2],
end⟩

/-- Any composition series of a simple group `G` has `⟦G⟧` as its only composition factor. -/
@[to_additive]
lemma factors_of_simple (h1 : is_simple G) (h2 : ¬ subsingleton G) :
  Π (s : composition_series G), s.val.factors = quotient.mk' G ::ₘ 0
| ⟨trivial hG, h⟩ := absurd hG h2
| ⟨cons H G f s, h⟩ := begin
  simp, congr' 1,
  { apply class_eq',
    suffices : ∃ (h : quotient f.φ.range ≃* G), true, -- trick so we can use cases
      from classical.some this,
    cases h1 f.φ.range f.norm with h1 h1,
    { use [(equiv_quotient_of_eq h1).trans quotient_bot, trivial] },
    exfalso, apply (h (quotient.mk' $ Group.of (quotient f.φ.range)) (by simp)).2,
    simp, exact subsingleton_quotient_iff.mpr h1 },
  apply factors_of_subsingleton _ ⟨s, λ G' hG', h G' _⟩, swap,
  { rw [factors_cons, mem_cons], right, assumption },
  have h' := h (quotient.mk' $ Group.of (quotient_group.quotient f.φ.range)) _, swap,
  { rw [factors_cons, mem_cons], left, refl },
  cases h1 f.φ.range f.norm with h1 h1,
  { haveI := subsingleton_subgroup_iff.mpr h1, exact f.equiv_range.to_equiv.subsingleton },
  exfalso, apply h'.2, simp [h1, subsingleton_quotient_iff],
end

/-- The range of a normal embedding used in a composition series is a maximal normal subgroup. -/
@[to_additive]
lemma maximal_normal_subgroup_of_cons {σ : composition_series G}
  {f : normal_embedding H G} {s : normal_series H} :
  σ.val = cons H G f s → maximal_normal_subgroup f.φ.range :=
λ h, (maximal_normal_subgroup_iff _).mpr 
  (by simpa using
    σ.prop (quotient.mk' $ Group.of (quotient f.φ.range)) (by simp [←subtype.val_eq_coe, h]))

local attribute [instance] classical.prop_decidable
variables [hG : fintype G]
include hG

/-- The cardinality of succesive terms in the composition series is strictly descreasing. -/
@[to_additive]
lemma card_lt_of_cons {σ : composition_series G} {f : normal_embedding H G} {s : normal_series H} :
  σ.val = cons H G f s → @fintype.card H f.fintype < fintype.card G :=
λ h, @fintype.of_equiv_card _ _ f.fintype f.equiv_range.to_equiv ▸
  by convert card_lt (maximal_normal_subgroup_of_cons h).2.1

variable (G)
/-- Jordan-Hölder 1. Every finite group has a composition series. -/
@[to_additive]
noncomputable lemma exists_composition_series_of_finite :
  composition_series G :=
suffices h : ∀ (n : ℕ) (G : Group) (hG : fintype G),
  @fintype.card G hG = n → composition_series G,
  from h (fintype.card G) G hG rfl,
λ N, N.strong_rec_on $ begin
  intros n ih H, introI hH, intro hn,
  by_cases h1 : subsingleton H,
  { existsi trivial h1, intro, simp },
  by_cases h2 : is_simple H,
  { exact of_simple h2 h1 },
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

variable {G}
/-- Jordan-Hölder 2. Any two composition series for `G` have the same factors. -/
@[to_additive]
theorem eq_factors (σ τ : composition_series G) :
  σ.val.factors = τ.val.factors :=
suffices h : ∀ (n : ℕ) (G : Group) (hG : fintype G) (σ τ : composition_series G),
  @fintype.card G hG = n → σ.val.factors = τ.val.factors,
  from h (fintype.card G) G hG σ τ rfl,
λ n, n.strong_induction_on $ begin
  clear σ τ hG G n, intros n ih G, introI hG, intros σ τ hn,
  by_cases hG' : subsingleton G, { simp only [factors_of_subsingleton hG'] },
  rcases exists_cons_of_not_subsingleton hG' σ.val with ⟨H, f, s, hs⟩,
  rcases exists_cons_of_not_subsingleton hG' τ.val with ⟨K, g, t, ht⟩,
  simp [hs, ht],
  by_cases f.φ.range = g.φ.range,
  { congr' 1, { exact class_eq (equiv_quotient_of_eq h) },
    have : H ≃* K := f.equiv_range.trans ((mul_equiv.subgroup_congr h).trans g.equiv_range.symm),
    rw [←factors_of_cons hs, ←factors_of_cons ht, ←factors_of_mul_equiv this.symm],
    apply ih (@fintype.card H f.fintype) _ H f.fintype _ _ rfl,
    rw ←hn, exact card_lt_of_cons hs },
  have htop := sup_maximal_normal_subgroup (maximal_normal_subgroup_of_cons hs)
    (maximal_normal_subgroup_of_cons ht) h,
  have ρ := exists_composition_series_of_finite (Group.of ↥(f.φ.range ⊓ g.φ.range)),
  have := (maximal_normal_subgroup_iff _).mp (maximal_normal_subgroup_of_cons ht),
  let s' : composition_series H := cons' ρ (from_inf_range_left f g)
    ⟨(mul_equiv_is_simple_iff $ quotient_from_inf_range_left f g htop).mpr this.1,
    λ h, this.2 $ (quotient_from_inf_range_left f g htop).to_equiv.subsingleton_iff.mp h⟩,
  have := (maximal_normal_subgroup_iff _).mp (maximal_normal_subgroup_of_cons hs),
  let t' : composition_series K := cons' ρ (from_inf_range_right f g) 
    ⟨(mul_equiv_is_simple_iff $ quotient_from_inf_range_right f g htop).mpr this.1,
    λ h, this.2 $ (quotient_from_inf_range_right f g htop).to_equiv.subsingleton_iff.mp h⟩,
  have hs' := ih (@fintype.card H f.fintype) (hn ▸ card_lt_of_cons hs) H f.fintype s' (of_cons hs) rfl,
  have ht' := ih (@fintype.card K g.fintype) (hn ▸ card_lt_of_cons ht) K g.fintype t' (of_cons ht) rfl,
  rw [factors_of_cons hs, factors_of_cons'] at hs', rw ←hs',
  rw [factors_of_cons ht, factors_of_cons'] at ht', rw ←ht',
  conv_rhs { rw multiset.cons_swap }, congr' 1,
  { exact class_eq (quotient_from_inf_range_right f g htop).symm },
  congr' 1, exact class_eq (quotient_from_inf_range_left f g htop),
end

end composition_series

open composition_series