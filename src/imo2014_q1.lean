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
					- ((∑ i : fin (n + 1), a i) - n * (a n))                       : by simp [fin.sum_univ_cast_succ]
		... = a (n + 1) - (n + 1) * (a (n + 1)) + n * (a n)                  : by ring
		... = n * (a n - a (n + 1))                                          : by ring
		... < 0                                                              : this,
	linarith,
end

theorem lt_of_lt_of_des {f : ℕ+ → ℤ} (hdes : ∀ n, f (n + 1) < f n) {n m : ℕ+} (hnm : n < m) :
	f m < f n :=
begin
	have : ∀ k : ℕ, f (n + ⟨k + 1, by linarith⟩) < f n,
	{	intro k, induction k with k ih,
		{ exact hdes n },
		apply lt_trans _ ih,
		change f (n + ⟨k + 1, by linarith⟩ + 1) < _,
		exact hdes _ },
	convert this (↑(m - n) - 1),
	have : 1 ≤ ↑(m - n) := (pnat.coe_le_coe 1 _).mpr (pnat.one_le _),
	simp [nat.sub_add_cancel this],
	rw pnat.add_sub_of_lt hnm,
end

theorem no_middle_term {f : ℕ+ → ℤ} (hdes : ∀ n, f (n + 1) < f n) (n : ℕ+) :
	¬ ∃ m, f (n + 1) < f m ∧ f m < f n :=
begin
	rintro ⟨m, fn1m, fmn⟩,
	rcases lt_trichotomy m n with hmn | heq | hnm,
	{ linarith [lt_of_lt_of_des hdes hmn] },
	{ rw heq at fmn, linarith },
	by_cases h : n + 1 < m,
	{	linarith [lt_of_lt_of_des hdes h] },
	have h : m = n + 1 := le_antisymm (le_of_not_gt h) (nat.succ_le_of_lt hnm),
	rw h at fn1m, linarith,
end

theorem cross_of_des {f : ℕ+ → ℤ} (hdes : ∀ n, f (n + 1) < f n) (x : ℤ) (m : ℕ+) (hx : x < f m) :
	∃ n, m ≤ n ∧ x < f n ∧ f (n + 1) ≤ x :=
begin
	sorry
end

theorem unique_cross_of_des {f : ℕ+ → ℤ} (hdes : ∀ n, f (n + 1) < f n) (x : ℤ) (n : ℕ+)
	(hcross : x < f n ∧ f (n + 1) ≤ x) : ∀ m, x < f m ∧ f (m + 1) ≤ x → m = n :=
begin
	intros m hm,
	have : ∀ {n m}, f (n + 1) ≤ x → x < f m → m ≤ n,
	{ intros n m hfn1 hfm, by_contradiction hnm,
		have h1 : f (n + 1) < f m := lt_of_le_of_lt hfn1 hfm,
	  have h2 : f m < f n := lt_of_lt_of_des hdes (lt_of_not_ge hnm),
		exact no_middle_term hdes n ⟨m, h1, h2⟩ },
	exact le_antisymm (this hcross.2 hm.1) (this hm.2 hcross.1),
end

theorem unique_n : ∃! n : ℕ+, 
	(a n : ℚ) < (∑ i : fin (n + 1), a i) / n ∧
	((∑ i : fin (n + 1), a i) : ℚ) / n ≤ a (n + 1) :=
begin
	rcases cross_of_des ddes 0 1 _ with ⟨n, _, hn⟩, swap,
	{	rw d_one, exact hpos 0 },
	use [n, ineq_iff.mpr hn],
	have huniq : _ := unique_cross_of_des ddes 0 n hn,
	intros m hm,
	exact huniq m (ineq_iff.mp hm),
end