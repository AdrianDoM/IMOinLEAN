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