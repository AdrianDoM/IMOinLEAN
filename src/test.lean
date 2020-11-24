/-
Author: Adrián Doña Mateo.
-/

import algebra.archimedean
import data.nat.modeq
import data.nat.sqrt
import data.zmod.basic
import tactic

import modeq

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

theorem a_succ_of_sq {a₀ n : ℕ} (k : ℕ) (hk : k * k = a a₀ n) :
	a a₀ (n + 1) = k :=
begin
	have hsq : sqrt (a a₀ n) = k := by { rw ← hk, exact sqrt_eq k },
	simp [a],
	split_ifs,
	{ assumption },
	rw hsq at h,
	contradiction
end

theorem a_succ_of_not_sq {a₀ n : ℕ} (h : ¬ ∃ k, k * k = a a₀ n) :
	a a₀ (n + 1) = a a₀ n + 3 :=
begin
	simp [a],
	split_ifs with hsq, swap,
	{ refl },
	exfalso,
	exact h ⟨sqrt (a a₀ n), hsq⟩,
end

theorem a_no_squares {a₀ n k : ℕ} (h : ∀ i, i < k → ¬ ∃ t, t * t = a a₀ n + 3 * i) :
	∀ i, i ≤ k → a a₀ (n + i) = a a₀ n + 3 * i :=
begin
	induction k with k ih,
	{ intros i hik, rw le_zero_iff.mp hik, refl },
	intros i hik,
	have hk : ∀ i, i ≤ k → a a₀ (n + i) = a a₀ n + 3 * i :=
		ih (λ i hik, h i (lt_trans hik $ lt_succ_self k)),
	by_cases hi : i = k.succ, swap,
	{	exact hk i (le_of_lt_succ (lt_of_le_of_ne hik hi)) },
	rw [hi, add_succ, a_succ_of_not_sq _], swap,
	{	rw hk k (le_refl k), exact h k (lt_succ_self k) },
	rw [hk k (le_refl k), add_assoc, mul_succ],
end

theorem has_le_b {b : ℕ} (S : set ℕ) (hS : S.nonempty)
	(h : ∀ x ∈ S, b < x → ∃ y ∈ S, y < x) :	∃ x ∈ S, x ≤ b :=
begin
	rcases well_founded.has_min lt_wf S hS with ⟨x, xS, hx⟩,
	use [x, xS],
	by_contradiction hbx,
	rcases h x xS (lt_of_not_ge hbx) with ⟨y, yS, hy⟩,
	exact hx y yS hy,
end

theorem term_le_b {a₀ n b : ℕ}
	(h : ∀ m, n ≤ m → b < a a₀ m → ∃ k, m ≤ k ∧ a a₀ k < a a₀ m) :
	∃ m, n ≤ m ∧ a a₀ m ≤ b :=
begin
	let S := { x | ∃ m, n ≤ m ∧ a a₀ m = x },
	have hS : ∀ x ∈ S, b < x → ∃ y ∈ S, y < x,
	{	rintros x ⟨m, hnm, rfl⟩ hbx,
		rcases h m hnm hbx with ⟨k, hmk, hk⟩,
		use [a a₀ k, ⟨k, le_trans hnm hmk, rfl⟩, hk] },
	rcases has_le_b S ⟨a a₀ n, n, le_refl n, rfl⟩  hS with ⟨x, ⟨m, hnm, rfl⟩, hxb⟩,
	use [m, hnm, hxb],
end


/-- There are no perfect squares strictly between a² and (a+1)² -/
lemma no_middle_square {n a : ℕ} (hl : a * a < n) (hr : n < (a + 1) * (a + 1)):
	¬ ∃ t, t * t = n :=
begin
	rintro ⟨t, rfl⟩,
	have : a < t, from nat.mul_self_lt_mul_self_iff.mpr hl,
	have : t < a + 1, from nat.mul_self_lt_mul_self_iff.mpr hr,
	linarith,
end

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

lemma first_square_aux {b : ℕ} (hpos : b ≠ 0) (hb : b ≡ 0 [MOD 3] ∨ b ≡ 1 [MOD 3]) :
	let t := sqrt (b - 1) in
	∃ (j : fin 3) n, b + 3 * n = (t + 1 + j) * (t + 1 + j) ∧
	∀ k, k < n → ¬ ∃ r, r * r = b + 3 * k := sorry

#check nat.sub_lt_left_iff_lt_add 

/-- If ¬ aₙ ≡ 2 [MOD 3] and aₙ > 9 then the next perfect square in the sequence is one of
t², (t+1)² or (t+2)², where t is the largest natural number such that t² ≤ aₙ -/
lemma first_square {a₀ n : ℕ} (h1 : a a₀ n ≡ 0 [MOD 3] ∨ a a₀ n ≡ 1 [MOD 3]) (h2 : a a₀ n ≠ 0) :
	let t := sqrt (a a₀ n - 1) in
	∃ (j : fin 3) m, n ≤ m ∧ a a₀ m = (t + 1 + j) * (t + 1 + j) ∧
	∀ k, n ≤ k → k < m → ¬ ∃ r, r * r = a a₀ k :=
begin
	rcases first_square_aux h2 h1 with ⟨j, k, hsq, hfirst⟩,
	have hk : ∀ i, i ≤ k → a a₀ (n + i) = a a₀ n + 3 * i := a_no_squares hfirst,
	use [j, n + k, by linarith], split,
	{ rw ← hsq, exact hk k (le_refl k) },
	intros m hnm hmnk,
	have hm : m - n < k := (nat.sub_lt_left_iff_lt_add hnm).mpr hmnk,
	rw [← nat.add_sub_cancel' hnm, hk (m - n) (le_of_lt hm)],
	exact hfirst (m - n) hm,
end