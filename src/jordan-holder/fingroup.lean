import group_theory.quotient_group
import group_theory.order_of_element

variables {G : Type*} [group G] [fintype G]

namespace subgroup

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