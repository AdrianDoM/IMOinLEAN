/-
Collection of congruence lemmas
Author: Adrián Doña Mateo
-/

import data.nat.modeq
import data.zmod.basic

namespace nat

theorem pos_of_gt {a b : ℕ} (h : a < b) : 0 < b :=
lt_of_le_of_lt (zero_le a) h

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

end modeq
end nat