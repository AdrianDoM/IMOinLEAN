import group_theory.quotient_group
import group_theory.order_of_element
import .simple_group .quotient_group


namespace subgroup
variables {G : Type*} [group G] [fintype G]

@[to_additive]
lemma card_pos : fintype.card G > 0 := fintype.card_pos_iff.mpr ⟨1⟩

variables {H : subgroup G} [decidable_pred H.carrier]

@[to_additive]
lemma card_lt : H ≠ ⊤ → fintype.card H < fintype.card G :=
begin
  contrapose!, intro h, apply eq_top_of_card_eq H (le_antisymm _ h),
  apply fintype.card_subtype_le,
end

lemma eq_bot_of_card_eq_one : fintype.card H = 1 → H = ⊥ :=
λ h, le_antisymm (λ x hx, begin
  rcases fintype.card_eq_one_iff.mp h with ⟨y, hy⟩, rw mem_bot,
  simpa using (hy ⟨x, hx⟩).trans (hy ⟨(1 : G), H.one_mem⟩).symm,
end) bot_le

end subgroup

namespace add_subgroup

variables {G : Type*} [add_group G] [fintype G]
variables {H : add_subgroup G} [decidable_pred H.carrier]

/- The to_additive attribute doesn't work in this case because it also changes the 1
in the conclusion to a 0-/
lemma eq_bot_of_card_eq_one : fintype.card H = 1 → H = ⊥ :=
λ h, le_antisymm (λ x hx, begin
  rcases fintype.card_eq_one_iff.mp h with ⟨y, hy⟩, rw mem_bot,
  simpa using (hy ⟨x, hx⟩).trans (hy ⟨(0 : G), H.zero_mem⟩).symm,
end) bot_le

end add_subgroup

attribute [to_additive add_subgroup.eq_bot_of_card_eq_one] subgroup.eq_bot_of_card_eq_one

namespace fintype

/- TODO: push these to mathlib. -/

variables {α β : Type*} [fintype α] [fintype β]

lemma card_ge_of_surjective {f : α → β} (hf : function.surjective f) : card α ≥ card β :=
card_le_of_injective (function.surj_inv hf) (function.injective_surj_inv hf)

lemma card_quotient_le {s : setoid α} [decidable_rel s.r] :
  fintype.card (quotient s) ≤ fintype.card α :=
card_ge_of_surjective (surjective_quotient_mk _)

end fintype

namespace quotient_add_group

open add_subgroup

variables {G : Type*} [add_group G] [fintype G]
variables {N : add_subgroup G} [add_subgroup.normal N]
  [decidable_pred (λ a, a ∈ N)] [decidable_pred N.carrier]

/- TODO: add to_additive's in order_of_element.lean file. -/
lemma eq_bot_of_card_quotient_eq : fintype.card (quotient N) = fintype.card G → N = ⊥ :=
begin
  intro h, rw card_eq_card_quotient_mul_card_subgroup N at h,
  conv_lhs at h { rw ←nat.mul_one (fintype.card (quotient N)) },
  apply subgroup.eq_bot_of_card_eq_one,
  apply nat.eq_of_mul_eq_mul_left subgroup.card_pos h.symm,
end

end quotient_add_group

namespace quotient_group

variables {G : Type*} [group G] [fintype G]
variables {N : subgroup G} [subgroup.normal N] [decidable_pred (λ a, a ∈ N)] [decidable_pred N.carrier]

@[to_additive]
lemma eq_bot_of_card_quotient_eq : fintype.card (quotient N) = fintype.card G → N = ⊥ :=
begin
  intro h, rw card_eq_card_quotient_mul_card_subgroup N at h,
  conv_lhs at h { rw ←nat.mul_one (fintype.card (quotient N)) },
  apply subgroup.eq_bot_of_card_eq_one,
  apply nat.eq_of_mul_eq_mul_left subgroup.card_pos h.symm,
end

@[to_additive]
lemma card_quotient_lt :
  N ≠ ⊥ → fintype.card (quotient N) < fintype.card G :=
begin
  contrapose!, intro h, apply eq_bot_of_card_quotient_eq (le_antisymm _ h),
  apply fintype.card_quotient_le,
end

end quotient_group


namespace fingroup

open fintype

@[to_additive add_fingroup.strong_rec_on_card]
def strong_rec_on_card (G : Type*) [group G] [fintype G] 
  {p : Π (G : Type*) [group G] [fintype G], Sort _} :
  (Π (G : Type*) [group G] [fintype G],
    (Π (H : Type*) [group H] [fintype H], by exactI card H < card G → p H) →
    by exactI p G) →
  p G :=
λ ih, suffices h : ∀ (n : ℕ) (G : Type*) [group G] [fintype G], by exactI card G = n → p G,
  from h (card G) G rfl,
λ n, n.strong_rec_on $ begin
  intros n ih' G, introsI _ _, intro hn,
  apply ih G,
  intro H, introsI _ _, intro hH,
  exact ih' (card H) (hn ▸ hH) H rfl,
end

@[to_additive add_fingroup.strong_rec_on_card']
def strong_rec_on_card' (G : Group) [fintype G]
  {p : Π (G : Group) [fintype G], Sort _} :
  (Π (G : Group) [fintype G],
    (Π (H : Group) [fintype H], by exactI card H < card G → p H) →
    by exactI p G) →
  p G :=
λ ih, suffices h : ∀ (n : ℕ) (G : Group) [fintype G], by exactI card G = n → p G,
  from h (card G) G rfl,
λ n, n.strong_rec_on $ begin
  intros n ih' G, introI, intro hn,
  apply ih G, intro H, introI, intro hH,
  exact ih' (card H) (hn ▸ hH) H rfl,
end
  
end fingroup

lemma add_subgroup.not_subsingleton_of_prime_card {G : Type*} [add_group G] [fintype G] :
  nat.prime (fintype.card G) → ¬ subsingleton G :=
λ h1 h2,
have h : fintype.card G = 1 := fintype.card_eq_one_iff.mpr ⟨0, λ g, @subsingleton.elim _ h2 g 0⟩,
by { rw [h] at h1, exact nat.not_prime_one h1 }

lemma add_subgroup.is_simple_of_prime_card {G : Type*} [add_group G] [fintype G] :
  nat.prime (fintype.card G) → is_simple_add G :=
λ h N _, begin
  have hp := card_subgroup_dvd_card N, -- FIXME:
  rw nat.dvd_prime h at hp,
  cases hp,
  { left, exact eq_bot_of_card_eq_one hp },
  right, exact not_not.mp (not_imp_not.mpr card_lt (not_lt_of_ge $ ge_of_eq hp)),
end

namespace subgroup

open quotient_group

variables {G : Type*} [group G]

@[to_additive]
lemma not_subsingleton_of_prime_card [fintype G] : nat.prime (fintype.card G) → ¬ subsingleton G :=
λ h1 h2,
have h : fintype.card G = 1 := fintype.card_eq_one_iff.mpr ⟨1, λ g, @subsingleton.elim _ h2 g 1⟩,
by { rw [h] at h1, exact nat.not_prime_one h1 }

local attribute [instance] classical.prop_decidable

@[to_additive]
lemma is_simple_of_prime_card [fintype G] : nat.prime (fintype.card G) → is_simple G :=
λ h N _, begin
  have hp := card_subgroup_dvd_card N,
  rw nat.dvd_prime h at hp,
  cases hp,
  { left, exact eq_bot_of_card_eq_one hp },
  right, exact not_not.mp (not_imp_not.mpr card_lt (not_lt_of_ge $ ge_of_eq hp)),
end

@[to_additive]
lemma exists_maximal_normal_subgroup [fintype G] :
  ¬ subsingleton G → ∃ (N : subgroup G), maximal_normal_subgroup N :=
fingroup.strong_rec_on_card G begin
  intros G, introsI _ _, intros ih hG,
  by_cases h : is_simple G,
  { use [⊥, subgroup.bot_normal, λ h, hG (subsingleton_iff.mpr $ subsingleton_of_bot_eq_top h)],
    intros N hN _, exact h N hN },
  rcases not_is_simple.mp h with ⟨N, hN, hN'⟩, haveI := hN,
  rcases ih (quotient N) _ 
    (λ h, hN'.2 $ subsingleton_quotient_iff.mp h) with ⟨K, hK, hKtop, hKmax⟩,
  swap, { apply card_quotient_lt hN'.1 },
  use [comap (mk' N) K, normal.comap hK _], split,
  { intro h, apply hKtop, rw ←comap_top (mk' N) at h, apply_fun map (mk' N) at h,
    rw [map_comap_eq (mk'_surjective N), map_comap_eq (mk'_surjective N)] at h, exact h },
  intro L, introI hL, intro hLK,
  have hLK' := (gc_map_comap (mk' N)).monotone_l hLK, rw map_comap_eq (mk'_surjective N) at hLK',
  have hNL : N ≤ L := le_trans le_comap_mk' hLK,
  cases @hKmax (map (mk' N) L) (map_mk'_normal hNL) hLK',
  { left, exact le_antisymm ((gc_map_comap (mk' N)).le_u $ le_of_eq h_1) hLK },
  right, exact (map_mk'_eq_top hNL).mp h_1,
end

@[to_additive]
lemma maximal_normal_subgroup_iff (N : subgroup G) [N.normal] :
  maximal_normal_subgroup N ↔
  is_simple (quotient_group.quotient N) ∧ ¬ subsingleton (quotient_group.quotient N) :=
⟨λ hN, ⟨begin
  intro K, introI hK,
  have : N ≤ comap (mk' N) K, { convert ker_le_comap, rw ker_mk },
  cases hN.2.2 (comap (mk' N) K) this,
  { left, rw [←map_comap_eq (mk'_surjective N) K, ←map_comap_eq (mk'_surjective N) ⊥, h],
    change _ = map _ (mk' N).ker, rw ker_mk },
  right, rw [←map_comap_eq (mk'_surjective N) K, ←map_comap_eq (mk'_surjective N) ⊤, h, comap_top],
end,
  λ h, hN.2.1 (subsingleton_quotient_iff.mp h)⟩,
λ ⟨h1, h2⟩, ⟨infer_instance, λ h, h2 (subsingleton_quotient_iff.mpr h),
  begin
    intro K, introI hK, intro hNK,
    cases h1 _ (map_mk'_normal hNK),
    { left, apply le_antisymm _ hNK, rw ←ker_mk N, exact le_ker_iff_map.mpr h },
    right, apply (map_mk'_eq_top hNK).mp h,
  end⟩⟩

end subgroup
