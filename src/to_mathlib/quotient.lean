/-
Four natural lemmas missing from the quotient fintype API.
Author: Adrián Doña Mateo

These were contributed to mathlib in
[#6964](https://github.com/leanprover-community/mathlib/pull/6964/).

An apostrophe was added at the end of the names to avoid clashes.
-/

import data.fintype.basic

-- These lemmas were added to src/data/fintype/basic.lean.

variables {α β : Type*}

namespace fintype
variables [fintype α] [fintype β]

lemma card_le_of_surjective' (f : α → β) (h : function.surjective f) : card β ≤ card α :=
card_le_of_injective _ (function.injective_surj_inv h)

lemma card_lt_of_surjective_not_injective' [fintype α] [fintype β] (f : α → β)
  (h : function.surjective f) (h' : ¬function.injective f) : card β < card α :=
card_lt_of_injective_not_surjective _ (function.injective_surj_inv h) $ λ hg,
have w : function.bijective (function.surj_inv h) := ⟨function.injective_surj_inv h, hg⟩,
h' $ (injective_iff_surjective_of_equiv (equiv.of_bijective _ w).symm).mpr h

end fintype

theorem fintype.card_quotient_le' [fintype α] (s : setoid α) [decidable_rel ((≈) : α → α → Prop)] :
  fintype.card (quotient s) ≤ fintype.card α :=
fintype.card_le_of_surjective _ (surjective_quotient_mk _)

theorem fintype.card_quotient_lt' [fintype α] {s : setoid α} [decidable_rel ((≈) : α → α → Prop)]
  {x y : α} (h1 : x ≠ y) (h2 : x ≈ y) : fintype.card (quotient s) < fintype.card α :=
fintype.card_lt_of_surjective_not_injective _ (surjective_quotient_mk _) $ λ w,
h1 (w $ quotient.eq.mpr h2)