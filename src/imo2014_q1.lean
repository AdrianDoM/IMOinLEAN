/-
Author: Adrián Doña Mateo.
-/

import algebra.big_operators
import data.pnat.basic
import tactic

import pnat

/-!
# IMO 2014 Q1

Let a₀ < a₁ < a₂ < ⋯ be an infinite sequence of positive integers.
Prove that there exists a unique n ≥ 1 such that

	aₙ < (a₀ + a₁ + ⋯ + aₙ) / n < aₙ₊₁.
-/

open_locale big_operators

noncomputable theory

constant a : ℕ → ℤ
constant hpos : ∀ n, 0 < a n
constant hinc : ∀ n, a n < a (n + 1)

def d (n : ℕ+) : ℤ := ∑ i : fin (n + 1), a i - n * (a n)

lemma first_ineq_iff {n : ℕ+} :
	(a n : ℚ) < (∑ i : fin (n + 1), a i) / n ↔ 0 < d n :=
begin
	sorry,
	-- split,
	-- {	intro h, simp [d],
	-- 	apply nat.sub_pos_of_lt,
	-- 	have : (a n : ℚ) * n < (∑ (i : fin (n + 1)), a i),
	-- 	{ rw ← rat.mul_one (a n : ℚ) at h,
	-- 		change ↑(a ↑n) / ↑1 < (∑ (i : fin (↑n + 1)), ↑(a ↑i)) / ↑n at h,
	-- 		rw [rat.div_lt_div_iff_mul_lt_mul _ _] at h,
	-- 		norm_cast at h,
	-- 		apply (rat.div_lt_div_iff_mul_lt_mul _ _).mp,} }
end

lemma second_ineq_iff {n : ℕ+} :
	((∑ i : fin (n + 1), a i) : ℚ) / n ≤ a (n + 1) ↔ d (n + 1) ≤ 0 :=
begin
	sorry
end

lemma ineq_iff {n : ℕ+} :
	(a n : ℚ) < (∑ i : fin (n + 1), a i) / n ∧ ((∑ i : fin (n + 1), a i) : ℚ) / n ≤ a (n + 1)
	↔ 0 < d n ∧ d (n + 1) ≤ 0 :=
⟨λ h, ⟨first_ineq_iff.1 h.1, second_ineq_iff.1 h.2⟩,
	λ h, ⟨first_ineq_iff.2 h.1, second_ineq_iff.2 h.2⟩⟩

lemma d_one : d 1 = a 0 :=
calc d 1
		= ∑ i : fin 2, a i - 1 * (a 1) : rfl
... = a 0 + (a 1 + 0) - 1 * (a 1)  : rfl
... = a 0                          : by ring

lemma ddes : ∀ n, d (n + 1) < d n :=
begin
	intro n,
	have : ↑n * (a n - a (n + 1)) < 0 :=
		mul_neg_iff.mpr (or.inl ⟨by simp, sub_lt_zero.mpr (hinc n)⟩),
	have hneg : d (n + 1) - d n < 0, from
		calc d (n + 1) - d n
				= ((∑ i : fin (n + 2), a i) - (n + 1) * (a (n + 1)))
					- ((∑ i : fin (n + 1), a i) - n * (a n))                       : rfl
		... = ((∑ i : fin (n + 1), a i) + a (n + 1) - (n + 1) * (a (n + 1)))
					- ((∑ i : fin (n + 1), a i) - n * (a n))                       : sorry
		... = a (n + 1) - (n + 1) * (a (n + 1)) + n * (a n)                  : by ring
		... = n * (a n - a (n + 1))                                          : by ring
		... < 0                                                              : this,
	linarith,
end

theorem cross_of_des {f : ℕ+ → ℤ} (hdes : ∀ n, f (n + 1) < f n) (x : ℤ) (hx : x < f 1) :
	∃ n, x < f n ∧ f (n + 1) ≤ x :=
begin
	have h : ∀ k : ℕ, f ⟨2 + k, by linarith⟩ < f 1 - k,
	{	intro k, induction k with k ih,
		{ simp, exact hdes 1 },
		change f ⟨2 + (k + 1), _⟩ < f 1 - (k + 1),
		have : 2 + (k + 1) = 2 + k + 1 := by rw add_assoc,
		simp [this, sub_add_eq_sub_sub],
		apply lt_of_lt_of_le (hdes ⟨2 + k, by linarith⟩),
		linarith },
	have : ∃ n, f (n + 1) ≤ x,
	{	have : 0 < 2 + (f 1 - x) := by linarith,
		cases pnat.from_int this with n hn,
		use n,
		apply le_trans (le_of_lt (hdes n)),
		apply le_of_lt,
		have : 0 ≤ f 1 - x := by linarith,
		cases int.eq_coe_of_zero_le this with m hm,
		convert h m,
		{ apply pnat.eq, simp,
			rw [← int.coe_nat_eq_coe_nat_iff, int.coe_nat_add, ← hm],
			norm_cast, simp [hn] },
		linarith },
	sorry,
end

theorem unique_cross_of_des {f : ℕ+ → ℤ} (hdes : ∀ n, f (n + 1) < f n) (x : ℤ) (n : ℕ+)
	(hcross : x < f n ∧ f (n + 1) ≤ x) : ∀ m, x < f m ∧ f (m + 1) ≤ x → m = n :=
begin
	sorry
end

theorem unique_n : ∃! n : ℕ+, 
	(a n : ℚ) < (∑ i : fin (n + 1), a i) / n ∧
	((∑ i : fin (n + 1), a i) : ℚ) / n ≤ a (n + 1) :=
begin
	cases cross_of_des ddes 0 _ with n hn, swap,
	{	rw d_one, exact hpos 0 },
	have h : _ := ineq_iff.mpr hn,
	use [n, h],
	have huniq : _ := unique_cross_of_des ddes 0 n hn,
	intros m hm,
	exact huniq m (ineq_iff.mp hm),
end