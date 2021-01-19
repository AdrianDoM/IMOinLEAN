import data.nat.gcd

namespace nat

lemma gcd_eq_zero_iff {m n : ℕ} :
	m.gcd n = 0 ↔ m = 0 ∧ n = 0 :=
⟨λ h, ⟨eq_zero_of_gcd_eq_zero_left h, eq_zero_of_gcd_eq_zero_right h⟩,
	λ ⟨hm, hn⟩, hn ▸ hm.symm ▸ gcd_zero_left n⟩

lemma lcm_eq_zero_iff {m n : ℕ} :
	m.lcm n = 0 ↔ m = 0 ∨ n = 0 :=
begin
	split, swap,
	{	rintro (rfl | rfl), { rw lcm_zero_left }, rw lcm_zero_right },
	unfold lcm, intro h,
	by_contradiction hmn,
	push_neg at hmn,
	rw nat.div_eq_zero_iff at h, swap,
	{ apply nat.pos_of_ne_zero, simp [gcd_eq_zero_iff], intro, exact hmn.2 },
	apply (not_lt_of_ge _) h,
	rw ← nat.one_mul (m.gcd n),
	apply mul_le_mul (succ_le_of_lt $ nat.pos_of_ne_zero hmn.1) _ (zero_le _) (zero_le _),
	apply nat.le_of_dvd (nat.pos_of_ne_zero hmn.2) (gcd_dvd_right _ _),
end

#check nat.le_of_dvd
#check succ_le_of_lt

end nat