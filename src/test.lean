/-
Author: Adrián Doña Mateo.
-/

import imo2017_q6

open mv_polynomial (hiding X) int (hiding range) finset
open_locale big_operators

local notation `polyℤ` := mv_polynomial (fin 2) ℤ
local notation `ϕ` := nat.totient

theorem foo {p k : ℕ} (hp : p.prime) :
	∃ n (φ : polyℤ), 0 < n ∧ φ.is_homogeneous n ∧
	(∀ t, primitive_root t → eval (to_val t) φ ≡ 1 [ZMOD ↑(p ^ k)]) :=
begin
	rcases nat.prime.eq_two_or_odd hp with rfl | hodd,
	{	sorry },
	have p_gt_two : 2 < p := sorry,
	use [(p - 1) * ϕ (p ^ k), (X ^ (p - 1) + Y ^ (p - 1)) ^ (ϕ (p ^ k))], split,
	{ sorry }, split,
	{ sorry },
	intros t ht,
	rw eval_pow,
	apply modeq.pow_totient,
	conv { congr, simp [X, Y], change t.1 ^ (p - 1) + t.2 ^ (p - 1), skip, simp },
	apply is_coprime.pow_right,
	rw is_coprime_prime hp,
	rw [← modeq.modeq_zero_iff, ← nat.totient_prime hp],
	by_cases hx : ↑p ∣ t.1,
	{ by_cases hy : ↑p ∣ t.2,
		{	sorry },
		have : t.1 ^ p.totient ≡ 0 [ZMOD p] := modeq.modeq_zero_iff.mpr (dvd_pow hx $
			ne_of_gt (nat.totient_pos $ lt_trans (by norm_num) p_gt_two)),
		simp [← zmod.int_coe_eq_int_coe_iff] at *,
		rw [this, zero_add, ← cast_pow, ← cast_zero, zmod.int_coe_eq_int_coe_iff],
		have h1 : t.2 ^ p.totient ≡ 1 [ZMOD p] := modeq.pow_totient ((is_coprime_prime hp).mpr hy),
		intro h0,
		apply nat.prime.not_dvd_one hp,
		simp [← coe_nat_dvd, ← modeq.modeq_zero_iff],
		exact modeq.trans h1.symm h0 },
	have hx1 : t.1 ^ p.totient ≡ 1 [ZMOD p] := modeq.pow_totient ((is_coprime_prime hp).mpr hx),
	by_cases hy : ↑p ∣ t.2,
	{ have : t.2 ^ p.totient ≡ 0 [ZMOD p] := modeq.modeq_zero_iff.mpr (dvd_pow hy $
			ne_of_gt (nat.totient_pos $ lt_trans (by norm_num) p_gt_two)),
		simp [← zmod.int_coe_eq_int_coe_iff] at this,
		simp [← zmod.int_coe_eq_int_coe_iff],
		rw [this, add_zero, ← cast_pow, ← cast_zero, zmod.int_coe_eq_int_coe_iff],
		intro h0,
		apply nat.prime.not_dvd_one hp,
		simp [← coe_nat_dvd, ← modeq.modeq_zero_iff],
		exact modeq.trans hx1.symm h0 },
	have hy1 : t.2 ^ p.totient ≡ 1 [ZMOD p] := modeq.pow_totient ((is_coprime_prime hp).mpr hy),
	simp [← zmod.int_coe_eq_int_coe_iff] at *,
	simp [hx1, hy1],
	convert_to ¬ (↑2 : zmod p) = ↑0, { simp, ring },
	rw zmod.eq_iff_modeq_nat,
	apply (nat.modeq.not_modeq_lt_iff p_gt_two (nat.prime.pos hp)).mpr,
	norm_num,
end

#check nat.prime.pos


