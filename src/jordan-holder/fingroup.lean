import group_theory.quotient_group
import group_theory.order_of_element
import .simple_group


namespace subgroup
variables {G : Type*} [group G] [fintype G]

lemma card_pos : fintype.card G > 0 :=
fintype.card_pos_iff.mpr ⟨1⟩

variables {H : subgroup G} [decidable_pred H.carrier]

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

namespace fintype

/- TODO: push these to mathlib. -/

variables {α β : Type*} [fintype α] [fintype β]

lemma card_ge_of_surjective (f : α → β) (hf : function.surjective f) : card α ≥ card β :=
card_le_of_injective (function.surj_inv hf) (function.injective_surj_inv hf)

lemma card_quotient_le (s : setoid α) [decidable_rel s.r] :
  fintype.card (quotient s) ≤ fintype.card α :=
card_ge_of_surjective quotient.mk $ surjective_quotient_mk _

end fintype

namespace quotient_group

variables {G : Type*} [group G] [fintype G]
variables {N : subgroup G} [subgroup.normal N] [decidable_pred (λ a, a ∈ N)] [decidable_pred N.carrier]

lemma eq_bot_of_card_quotient_eq : fintype.card (quotient N) = fintype.card G → N = ⊥ :=
begin
  intro h, rw card_eq_card_quotient_mul_card_subgroup N at h,
  conv_lhs at h { rw ←nat.mul_one (fintype.card (quotient N)) },
  apply subgroup.eq_bot_of_card_eq_one,
  apply nat.eq_of_mul_eq_mul_left subgroup.card_pos h.symm,
end

lemma card_quotient_lt :
  N ≠ ⊥ → fintype.card (quotient N) < fintype.card G :=
begin
  contrapose!, intro h, apply eq_bot_of_card_quotient_eq (le_antisymm _ h),
  apply fintype.card_quotient_le,
end

end quotient_group

namespace fingroup

open fintype

#check nat.strong_rec_on

def strong_rec_on_card (G : Type*) (hGg : group G) (hGf : fintype G) 
  {p : Π (G : Type*), group G → fintype G → Sort _} :
  (Π (G : Type*) (hGg : group G) (hGf : fintype G),
    (Π (H : Type*) (hHg : group H) (hHf : fintype H), @card H hHf < @card G hGf → p H hHg hHf) →
    p G hGg hGf) → p G hGg hGf := sorry
  
end fingroup

#check @fingroup.strong_rec_on_card

namespace subgroup

variables {G : Type*} [group G]

def maximal_normal_subgroup (N : subgroup G) : Prop :=
  N.normal ∧ N ≠ ⊤ ∧ ∀ (K : subgroup G) [K.normal], N ≤ K → K = N ∨ K = ⊤

lemma exists_maximal_normal_subgroup_aux
  (G : Type*) (hGg : group G) (hGf : fintype G) (h : ¬ subsingleton G) :
  ∃ (N : subgroup G), maximal_normal_subgroup N :=
fingroup.strong_rec_on_card G hGg hGf sorry

lemma exists_maximal_normal_subgroup [fintype G] (h : ¬ subsingleton G) :
  ∃ (N : subgroup G), maximal_normal_subgroup N :=
exists_maximal_normal_subgroup_aux G infer_instance infer_instance h

lemma maximal_normal_subgroup_iff (N : subgroup G) [N.normal] :
  maximal_normal_subgroup N ↔
  is_simple (quotient_group.quotient N) ∧ ¬ subsingleton (quotient_group.quotient N) :=
sorry

end subgroup
