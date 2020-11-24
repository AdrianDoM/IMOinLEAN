/-
Collection of nat.sqrt lemmas
Author: Adrián Doña Mateo
-/

import data.nat.sqrt
import tactic

namespace nat

lemma sqrt_pred_lt (n : ℕ) (h : n ≠ 0) :
	sqrt (n - 1) * sqrt (n - 1) < n := lt_of_le_of_lt (sqrt_le _) (pred_lt h)

lemma le_succ_sqrt_pred (n : ℕ) (h : n ≠ 0) :
	n ≤ (sqrt (n - 1) + 1) * (sqrt (n - 1) + 1) := le_of_pred_lt (lt_succ_sqrt _)

/-- There are no perfect squares strictly between a² and (a+1)² -/
lemma no_middle_square {n a : ℕ} (hl : a * a < n) (hr : n < (a + 1) * (a + 1)):
	¬ ∃ t, t * t = n :=
begin
	rintro ⟨t, rfl⟩,
	have : a < t, from nat.mul_self_lt_mul_self_iff.mpr hl,
	have : t < a + 1, from nat.mul_self_lt_mul_self_iff.mpr hr,
	linarith,
end

/-- All perfect squares between a² and (a + b)² are of the form (a + k)² for some k ≤ b -/
lemma middle_squares {n a b : ℕ} (hl : a * a ≤ n) (hr : n ≤ (a + b) * (a + b)) :
	(∃ t, t * t = n) → ∃ k, k ≤ b ∧ (a + k) * (a + k) = n :=
begin
	intro hsq,
	induction b with b ih,
	{	use [0, le_refl 0], linarith },
	by_cases h1 : n ≤ (a + b) * (a + b),
	{	rcases ih h1 with ⟨k, hkb, hk⟩,
		use [k, le_succ_of_le hkb, hk] },
	by_cases h2 : n < (a + b.succ) * (a + b.succ),
	{	exfalso, exact no_middle_square (lt_of_not_ge h1) h2 hsq },
	use [b.succ, le_refl _],
	linarith,
end

end nat