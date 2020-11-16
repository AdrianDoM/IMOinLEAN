/-
Copyright (c) 2020 Adrián Doña Mateo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adrián Doña Mateo.
-/

import algebra.archimedean
import data.nat.modeq
import data.nat.sqrt
import data.zmod.basic
import tactic
open nat

/-!
# IMO 2017 Q1

For each integer a₀ > 1, define a sequence a₀, a₁, a₂, ... by:
				 
	aₙ₊₁ = √aₙ if √aₙ is an integer, aₙ + 3 otherwise, for each n ≥ 0.

Determine all values of a₀ for which there is a number A such that aₙ = A for infinitely
many values of n.
-/

/-- The first order recurrence relation -/
def a (a₀ : ℕ) : ℕ → ℕ
| 0     := a₀
| (n+1) :=
	let k := sqrt (a n) in
	if k * k = a n then k else a n + 3

/-- The definition of periodicity -/
def periodic (a₀ : ℕ) : Prop :=
	∃ A, ∀ N, ∃ M, N ≤ M ∧ a a₀ M = A

/-- If two terms of the sequence are equal, so are all following terms -/
lemma rest_equal (a₀ : ℕ) (m n : ℕ) (h : a a₀ m = a a₀ n) :
	∀ k, a a₀ (m + k) = a a₀ (n + k) :=
begin
	intro k,
	induction k with k ih,
	{	simpa },
	simp [add_succ, a, ih],
end

/--	If two terms of the sequence are equal, then successive terms that are the same
distance appart will be equal -/
lemma periodic_term_of_term_equal (a₀ : ℕ) (m n : ℕ) (hmn : m ≤ n) (h : a a₀ m = a a₀ n) :
	∀ k, a a₀ (m + k * (n - m)) = a a₀ m :=
begin
	intro k,
	induction k with k ih,
	{	simp },
	calc a a₀ (m + k.succ * (n - m))
			= a a₀ (m + k * (n - m) + (n - m)) : by rw [succ_mul, add_assoc]
	... = a a₀ (m + (n - m))               : rest_equal a₀ (m + k * (n - m)) m ih (n - m)
	... = a a₀ n                           : by rw nat.add_sub_cancel' hmn
	... = a a₀ m                           : eq.symm h
end

/-- If two different terms of the sequence are equal, then it visits the same term
infinitely many times -/
lemma periodic_of_term_equal (a₀ : ℕ) (m n : ℕ) (hmn : m < n) (h : a a₀ m = a a₀ n) :
	periodic a₀ :=
begin
	use a a₀ m,
	intro N,
	by_cases hNm : N ≤ m,
	{	use [m, hNm] },
	have : 0 < n - m, from nat.sub_pos_of_lt hmn,
	cases archimedean.arch (N - m) this with k hk,
	simp at hk,
	let M := m + k * (n - m),
	have hM : N ≤ M, from
		calc N
				= N - m + m       : by rw nat.sub_add_cancel (le_of_not_ge hNm)
		... ≤ k * (n - m) + m : by simp [hk]
		... = m + k * (n - m) : by rw add_comm,
	use [M, hM],
	apply periodic_term_of_term_equal _ _ _ (le_of_lt hmn) h,
end

/-- A square is not congruent to 2 modulo 3 -/
lemma not_square_of_two_mod_three {n : ℕ} (h : n ≡ 2 [MOD 3]) :
	¬∃ m, m * m = n :=
begin
  rintro ⟨m, rfl⟩,
	have : ¬∃ (m : zmod 3), m * m = 2, dec_trivial,
  apply this,
  use m,
  norm_cast,
  rwa ←zmod.eq_iff_modeq_nat at h,
end

/--	If a term of the sequence is congruent to 2 modulo 3 then it is increasing
from that point on -/
lemma increasing_of_term_cong_two {a₀ n : ℕ} (h : a a₀ n ≡ 2 [MOD 3]) :
	∀ m, a a₀ (n + m) = a a₀ n + 3 * m :=
begin
	intro m,
	induction m with m ih,
	{	simp },
	have : a a₀ (n + m) ≡ 2 [MOD 3],
	{	rw [ih, modeq, add_mod, mul_mod, mod_self],
		simpa	},
	rw add_succ,
	simp [a],
	split_ifs with hsq,
	{	exfalso,
		apply not_square_of_two_mod_three this ⟨_, hsq⟩ },
	rw [ih, add_assoc, ←mul_succ],
end

#check nat.add_sub_cancel'

/-- If a term of the sequence is congruent to 2 modulo 3 then it is not periodic -/
lemma not_periodic_of_term_cong_two (a₀ n : ℕ) (h : a a₀ n ≡ 2 [MOD 3]) :
	¬ periodic a₀ :=
begin
	rintros ⟨A, hA⟩,
	have : ∀ k, ∃ N, ∀ M, N ≤ M → a a₀ n + k < a a₀ M,
	{ intro k,
		induction k with k ih,
		{	use n + 1,
			intros M hM,
			have : a a₀ (n + 1) ≤ a a₀ M,
			{ sorry },
			rw add_zero,
			have : a a₀ n < a a₀ (n + 1),
			{	rw increasing_of_term_cong_two h 1,
				linarith },
			apply lt_of_lt_of_le; assumption },
		cases ih with N hN,
		use N + 1,
		intros M hM,
		sorry, },
	cases this (A - a a₀ n) with N hN,
	cases hA N with M hM,
	have : a a₀ M = A, from hM.right,
	by_cases hnA : a a₀ n ≤ A,
	{ rw nat.add_sub_cancel' hnA at hN,
		have : A < a a₀ M, from hN M hM.left,
		linarith },
	have hnA : A < a a₀ n, from lt_of_not_ge hnA,
	rw [nat.sub_eq_zero_iff_le.mpr (le_of_lt hnA), add_zero] at hN,
	have : a a₀ n < a a₀ M, from hN M hM.left,
	linarith,
end

/-- There are no perfect squares strictly between a² and (a+1)² -/
lemma no_middle_square {a n : ℕ} (hl : a * a < n) (hr : n < (a + 1) * (a + 1)):
	¬ ∃ t, t * t = n :=
begin
	rintro ⟨t, rfl⟩,
	have : a < t, from nat.mul_self_lt_mul_self_iff.mpr hl,
	have : t < a + 1, from nat.mul_self_lt_mul_self_iff.mpr hr,
	linarith,
end

/- This long lemma takes care of each possibility for b and t mod 3.
Some parts involve repetitive computation so I suspect some refactoring is possible -/
lemma first_square_aux {b t : ℕ} {bm tm : zmod 3} (hb : bm = b) (hbm : bm ≠ 2) (ht : tm = t)
	(ht1 : t * t < b) (ht2 : b ≤ (t + 1) * (t + 1)) :
	∃ (j : fin 3) n, b + 3 * n = (t + 1 + j) * (t + 1 + j) ∧
	∀ k, k < n → ¬ ∃ r, r * r = b + 3 * k :=
begin
	have : bm * bm = bm,
	{	fin_cases bm; ring,
		contradiction },
	let j : fin 3 := if tm = 2 then bm else (if bm = 1 then 0 else (if tm = 0 then 2 else 1)),
	use j,
	have : bm = (t + 1 + j) * (t + 1 + j),
	{	simp [←ht, j],
		symmetry,
		split_ifs,
		{	rw h, convert ‹bm * bm = bm›; abel },
		{	rw h_1, ring, fin_cases tm; ring, contradiction },
		{	rw h_2, ring, fin_cases bm, abel, repeat {contradiction} },
		fin_cases tm,
		{	contradiction },
		{	fin_cases bm, dsimp, ring, repeat {contradiction} },
		contradiction },
	have : b ≤ (t + 1 + j) * (t + 1 + j),
	{	have : 0 ≤ ↑j, dec_trivial,
		have : t + 1 ≤ t + 1 + ↑j, linarith,
		apply le_trans ht2,
		apply mul_self_le_mul_self (nat.zero_le _) this },
	have : (3 : ℤ) ∣ (t + 1 + j) * (t + 1 + j) - b,
	{ apply (zmod.int_coe_zmod_eq_zero_iff_dvd _ 3).mp,
		simp [←hb],
		rw ‹bm = (t + 1 + j) * (t + 1 + j)›,
		ring },
	cases this with n hn,
	cases n with n,
	{	use n,
		have h : b + 3 * n = (t + 1 + ↑j) * (t + 1 + ↑j),
		{	apply (int.coe_nat_eq_coe_nat_iff _ _).mp,
			simp,
			rw [int.coe_nat_eq n, ←hn],
			ring },
		use h,
		intros k hk hr,
		have h1 : t * t < b + 3 * k, linarith,
		simp [j] at h,
		split_ifs at h,
		{ fin_cases bm,
			{ simp at h,
		 		have h2 : b + 3 * k < (t + 1) * (t + 1), linarith, 
				exact no_middle_square h1 h2 hr },
			{ simp at h,
				have h3 : (0 : zmod 3) = (t + 1) * (t + 1), rw [←ht, h_1], ring,
				by_cases b + 3 * k < (t + 1) * (t + 1),
				{ exact no_middle_square h1 h hr },
				have h1 : (t + 1) * (t + 1) < b + 3 * k,
				{	cases eq_or_lt_of_not_lt h with h h,
					{ exfalso,
						have : ↑(b + 3 * k) = (↑((t + 1) * (t + 1)) : zmod 3), rw h,
						simp at this,
						rw [←h3] at this,
						have h : (1 : zmod 3) ≠ 0, norm_num,
						exact h (eq.trans hb this) },
					exact h },
				have h2 : b + 3 * k < (t + 1 + 1) * (t + 1 + 1), linarith,
				exact no_middle_square h1 h2 hr },
			contradiction },
		{ simp at h,
			have h2 : b + 3 * k < (t + 1) * (t + 1), linarith,
			exact no_middle_square h1 h2 hr },
		{ simp at h,
			fin_cases bm,
			{ /- longest case. compare against (t + 1) * (t + 1) and (t + 2) * (t + 2) -/
				by_cases b + 3 * k < (t + 1) * (t + 1),
				{	exact no_middle_square h1 h hr },
				have h1 : (t + 1) * (t + 1) < b + 3 * k,
				{	cases eq_or_lt_of_not_lt h with h h,
					{ exfalso, 
						have h3 : (1 : zmod 3) = (t + 1) * (t + 1), rw [←ht, h_3], ring,
						have : ↑(b + 3 * k) = (↑((t + 1) * (t + 1)) : zmod 3), rw h,
						simp at this,
						rw [←h3] at this,
						exact h_2 (eq.trans hb this) },
					exact h },
				by_cases b + 3 * k < (t + 2) * (t + 2),
				{	exact no_middle_square h1 h hr },
				have h1 : (t + 2) * (t + 2) < b + 3 * k,
				{ cases eq_or_lt_of_not_lt h with h h,
					{ exfalso, 
						have h3 : (1 : zmod 3) = (t + 2) * (t + 2), rw [←ht, h_3], ring,
						have : ↑(b + 3 * k) = (↑((t + 2) * (t + 2)) : zmod 3), rw h,
						simp at this,
						rw [←h3] at this,
						exact h_2 (eq.trans hb this) },
					exact h },
				have h2 : b + 3 * k < (t + 3) * (t + 3), linarith,
				exact no_middle_square h1 h2 hr },
			{ contradiction },
			{ contradiction } },
		{ simp at h,
			fin_cases tm,
			{ contradiction },
			{ dsimp at ht,
				fin_cases bm,
				{ have h3 : (1 : zmod 3) = (t + 1) * (t + 1), rw ←ht, ring,
					by_cases b + 3 * k < (t + 1) * (t + 1),
					{ exact no_middle_square h1 h hr },
					have h1 : (t + 1) * (t + 1) < b + 3 * k,
					{	cases eq_or_lt_of_not_lt h with h h,
						{ exfalso,
							have : ↑(b + 3 * k) = (↑((t + 1) * (t + 1)) : zmod 3), rw h,
							simp at this,
							rw [←h3] at this,
							exact h_2 (eq.trans hb this) },
						exact h },
					have h2 : b + 3 * k < (t + 1 + 1) * (t + 1 + 1), linarith,
					exact no_middle_square h1 h2 hr },
				{ contradiction },
				{ contradiction } },
			{ contradiction } } },
	exfalso,
	have : (0 : ℤ) ≤ (t + 1 + j) * (t + 1 + j) - b,
	{	apply int.sub_nonneg_of_le,
		norm_cast,
		exact this },
	rw hn at this,
	have : 3 * -[1+ n] < 0,
	{	apply int.mul_neg_of_pos_of_neg,
		norm_num,
		apply int.neg_succ_lt_zero },
	linarith,
end

/-- If ¬ aₙ ≡ 2 [MOD 3] and aₙ > 9 then the next perfect square in the sequence is one of
t², (t+1)² or (t+2)², where t is the largest natural number such that t² ≤ aₙ -/
lemma first_square (a₀ n : ℕ) (h1 : ¬ a a₀ n ≡ 2 [MOD 3]) (h2 : 9 < a a₀ n) :
	let t := sqrt (a a₀ n - 1) in
	∃ (j : fin 3) m, n ≤ m ∧ a a₀ m = (t + 1 + j) * (t + 1 + j) ∧
	∀ k, n ≤ k → k < n → sqrt (a a₀ k) * sqrt (a a₀ k) ≠ a a₀ k :=
begin
	intro,
	sorry
end

/-- If ¬ aₙ ≡ 2 [MOD 3] and aₙ > 9 then there is an index m > n such that aₘ < aₙ -/
lemma foo (a₀ n : ℕ) (h1 : ¬ a a₀ n ≡ 2 [MOD 3]) (h2 : 9 < a a₀ n) :
	∃ m, m > n ∧ a a₀ m < a a₀ n :=
begin
	let t := sqrt (a a₀ n), -- floor sqrt
	have ht : 3 ≤ t,
	{	apply le_sqrt.mpr,
		apply le_of_lt h2 },
	have : ∃ j : zmod 3, (↑t + j) * (t + j) = a a₀ n, -- want find the first square after a a₀ n
	{ set an := (a a₀ n : zmod 3) with han,
		fin_cases an,
		{ set tm := (t : zmod 3) with htm,
			fin_cases tm,
	 		{ sorry },
			{ sorry },
			{ sorry } },
		{ change an = 1 at h, sorry },
		{ change an = 2 at h,
			exfalso,
			have : a a₀ n ≡ 2 [MOD 3],
			{	sorry },
			contradiction } },
	cases this with j hj,
	sorry,
end


/-- A multiple of 3 is always followed by a multiple of 3 -/
lemma mul_three_of_mul_three (a₀ n : ℕ) (h : a a₀ n ≡ 0 [MOD 3]) :
	∀ k, a a₀ (n + k) ≡ 0 [MOD 3] :=
begin
	intro k,
	induction k with k ih,
	{	simpa },
	rw add_succ,
	simp [a],
	split_ifs with hsq,
	{	rw [←hsq, modeq.modeq_zero_iff, prime.dvd_mul] at ih,
		{	cases ih;	{ apply modeq.modeq_zero_iff.mpr, exact ih } },
		norm_num },
	rw ←add_zero 0,
	apply modeq.modeq_add,
	{ assumption },
	simp [modeq],
end


/-- If aₙ ∈ {3,6,9}, then the sequence visits three infinitely many times -/
lemma periodic_of_three_six_nine (a₀ n : ℕ) (h : a a₀ n = 3 ∨ a a₀ n = 6 ∨ a a₀ n = 9) :
	periodic a₀ :=
begin
	use 3,
	have : a a₀ n = 9 → a a₀ (n+1) = 3,
	{ intro h,
		simp [a],
		split_ifs with h',
		{	rw h,
			refine sqrt_eq 3 },
		rw h at h',
		exfalso,
		apply h',
		show sqrt (3 * 3) * sqrt (3 * 3) = 9,
		rw sqrt_eq,
		refl },
	have : a a₀ n = 6 → a a₀ (n+1) = 9,
	{ intro h,
		simp [a],
		split_ifs with h',
		{ rw h at h',
			exfalso,
			apply @no_middle_square 2 6 _ _ ⟨sqrt 6, h'⟩; norm_num },
		rw h },
	have : a a₀ n = 3 → a a₀ (n+1) = 6,
	{	intro h,
		simp [a],
		split_ifs with h',
		{	rw h at h',
			exfalso,
			apply @no_middle_square 1 3 _ _ ⟨sqrt 3, h'⟩; norm_num },
		rw h },
	sorry,
end

/-- If aₙ ≡ 0 [MOD 3], then there is an index m > n such that aₘ = 3 -/
lemma term_equal_three_of_term_cong_zero (a₀ n : ℕ) (h : a a₀ n ≡ 0 [MOD 3]) :
	∃ m, m > n ∧ a a₀ m = 3 :=
begin
	sorry
end

/-- If aₙ ≡ 1 [MOD 3], then there is an index m > n such that aₘ ≡ 2 [MOD 3] -/
lemma term_cong_two_of_term_cong_one (a₀ n : ℕ) (h : a a₀ n ≡ 1 [MOD 3]) :
	∃ m, m > n ∧ a a₀ m ≡ 2 [MOD 3] :=
begin
	sorry
end