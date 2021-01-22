import data.multiset.gcd

namespace multiset

variables {α : Type*} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] [decidable_eq α]
variables {s : multiset α}

theorem lcm_ne_zero_iff : s.lcm ≠ 0 ↔ ∀ (a : α), a ∈ s → a ≠ 0 := 
begin
	apply multiset.induction_on s, { simp },
	intros b s ih, split,
	{	intros h a ha h0,
		rw [lcm_cons, ne.def, not_iff_not.mpr (lcm_eq_zero_iff _ _), decidable.not_or_iff_and_not] at h,
		rcases mem_cons.mp ha with rfl | ha, { exact h.1 h0 },
		exact ih.mp h.2 a ha h0 },
	intros h h0, rw [lcm_cons, lcm_eq_zero_iff] at h0,
	rcases h0 with rfl | h0, { exact h 0 (mem_cons_self _ _) (eq.refl _) },
	exact ih.mpr (λ a ha, h a (mem_cons_of_mem ha)) h0,
end

end multiset