import group_theory.quotient_group

namespace subgroup

variables {G : Type*} [group G] [fintype G]

local attribute [instance] classical.prop_decidable

set_option trace.class_instances true

lemma card_lt {H : subgroup G} : H ≠ ⊤ → fintype.card H < fintype.card G := sorry

lemma card_quotient_lt {N : subgroup G} [N.normal] :
  N ≠ ⊥ → fintype.card (quotient_group.quotient N) < fintype.card G := sorry

end subgroup