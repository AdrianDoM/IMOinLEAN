/-
Collection of congruence lemmas
Author: Adrián Doña Mateo
-/

import data.nat.modeq
import data.zmod.basic

namespace nat

lemma sqrt_pred_lt (n : ℕ) (h : n ≠ 0) :
	sqrt (n - 1) * sqrt (n - 1) < n := lt_of_le_of_lt (sqrt_le _) (pred_lt h)

lemma le_succ_sqrt_pred (n : ℕ) (h : n ≠ 0) :
	n ≤ (sqrt (n - 1) + 1) * (sqrt (n - 1) + 1) := le_of_pred_lt (lt_succ_sqrt _)

namespace modeq

theorem not_modeq_of_lt {a b n : ℕ} (hb : b < n) :
	a < b → ¬ a ≡ b [MOD n] :=
begin
	intro ha,
	rw modeq_iff_dvd' (le_of_lt ha),
	intro hdvd,
	apply not_le_of_gt hb,
	calc n
			≤ b - a : le_of_dvd (nat.sub_pos_of_lt ha) hdvd
	... ≤ b     : sub_le b a,
end

theorem modeq_lt_iff {a b n : ℕ} (ha : a < n) (hb : b < n) :
	a ≡ b [MOD n] ↔ a = b :=
begin
	split, swap,
	{ intro h, rw h },
	by_cases h : a < b,
	{ intro hab,
		exfalso,
		exact not_modeq_of_lt hb h hab },
	intro hab,
	symmetry,
	by_contradiction hne,
	apply not_modeq_of_lt ha _ (modeq.symm hab),
	exact lt_of_le_of_ne (le_of_not_lt h) hne,
end

theorem not_modeq_lt_iff {a b n : ℕ} (ha : a < n) (hb : b < n) :
	¬ a ≡ b [MOD n] ↔ a ≠ b :=
not_iff_not.mpr (modeq_lt_iff ha hb)

theorem not_modeq_of_modeq {a b c n : ℕ} (hb : b < n) (hc : c < n) (ha : a ≡ b [MOD n]) :
	b ≠ c → ¬ a ≡ c [MOD n] :=
λ hbc hac, (not_modeq_lt_iff hb hc).mpr hbc (modeq.trans (modeq.symm ha) hac)

lemma modeq_add_mul_mod {a n : ℕ} (k : ℕ) : a ≡ a + n * k [MOD n] := by simp [modeq]

lemma add_mul_mod_of_modeq {a b n : ℕ} (hab : a ≤ b) (h : a ≡ b [MOD n]) :
	∃ k, a + n * k = b :=
begin
	rw modeq.modeq_iff_dvd' hab at h,
	cases h with k hk, use k,
	rw [← hk, nat.add_sub_cancel' hab],
end

end modeq
end nat

namespace zmod

theorem ne_iff_not_modeq_nat {n a b : ℕ} : (↑a : zmod n) ≠ ↑b ↔ ¬ a ≡ b [MOD n] :=
not_iff_not.mpr (eq_iff_modeq_nat n)

end zmod