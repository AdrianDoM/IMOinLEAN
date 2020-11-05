/-
Copyright (c) 2020 Adrián Doña Mateo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adrián Doña Mateo.
-/

import data.nat.sqrt
import algebra.archimedean
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
	∃ A, ∀ N, ∃ M, N ≤ M ∧ a a₀ M = A :=
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

lemma not_square_of_two_mod_three (n : ℕ) (h : n % 3 = 2) :
	¬∃ m, m * m = n :=
begin
	by_contradiction hsq,
	cases hsq with m hm,
	have : (m % 3) * (m % 3) % 3 = 2, rwa [←mul_mod, hm],
	sorry
end