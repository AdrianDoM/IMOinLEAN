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

#check lt_wf

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
	∀ k, k < n → ¬ ∃ r, r * r = b + 3 * k :=
begin
	intro t,
	have htb : t * t < b := sqrt_pred_lt b hpos,
	have hbt : ∀ j : fin 3, b ≤ (t + 1 + j) * (t + 1 + j) := λ j, le_trans (le_succ_sqrt_pred b hpos) _, swap,
	{	simp [← t], apply nat.mul_self_le_mul_self, fin_cases j; simp },
	cases hb with h0 h1,
	{	let tm : zmod 3 := t,
		fin_cases tm,
		{	-- Case : b ≡ 0 and t ≡ 0 [MOD 3]
			have ht1 : (↑1 : zmod 3) = ↑((t + 1) * (t + 1)) := by simp [← tm, h],
			have ht2 : (↑1 : zmod 3) = ↑((t + 2) * (t + 2)) := by { simp [← tm, h], ring },
			have ht3 : (↑0 : zmod 3) = ↑((t + 3) * (t + 3)) := by simp [← tm, h],
			rcases modeq.add_mul_mod_of_modeq (hbt 2) (modeq.trans h0 _) with ⟨n, hn⟩, swap,
			{	rwa ← zmod.eq_iff_modeq_nat 3 },
		  use [2, n, hn],
			change b + 3 * n = (t + 3) * (t + 3) at hn,
			intros k hkn hsq,
			-- Show that (t + 3)² is the first square by eliminating the intermediate ones
			rcases @middle_squares _ t 3 _ _ hsq with ⟨r, hlr, hr⟩, swap,
			{ linarith }, swap,
			{ rw ← hn, linarith },
			interval_cases r,
			{	linarith },
			{ apply @modeq.not_modeq_of_lt 0 1 3 (by norm_num) (by norm_num),
				apply modeq.trans (modeq.trans h0.symm $ modeq.modeq_add_mul_mod k),
				apply modeq.trans _ ((zmod.eq_iff_modeq_nat 3).mp ht1).symm,
				rwa hr },
			{	apply @modeq.not_modeq_of_lt 0 1 3 (by norm_num) (by norm_num),
				apply modeq.trans (modeq.trans h0.symm $ modeq.modeq_add_mul_mod k),
				apply modeq.trans _ ((zmod.eq_iff_modeq_nat 3).mp ht2).symm,
				rwa hr },
			{ rw ← hn at hr, linarith } },
		{	-- Case : b ≡ 0 and t ≡ 1 [MOD 3]
			have ht1 : (↑1 : zmod 3) = ↑((t + 1) * (t + 1)) := by { simp [← tm, h], ring },
			have ht2 : (↑0 : zmod 3) = ↑((t + 2) * (t + 2)) := by { simp [← tm, h], ring },
			rcases modeq.add_mul_mod_of_modeq (hbt 1) (modeq.trans h0 _) with ⟨n, hn⟩, swap,
			{	rwa ← zmod.eq_iff_modeq_nat 3 },
			use [1, n, hn],
			change b + 3 * n = (t + 2) * (t + 2) at hn,
			intros k hkn hsq,
			-- Show that (t + 2)² by eliminating the previous one
			rcases @middle_squares _ t 2 _ _ hsq with ⟨r, hlr, hr⟩, swap,
			{	linarith }, swap,
			{ rw ← hn, linarith },
			interval_cases r,
			{ linarith },
			{ apply @modeq.not_modeq_of_lt 0 1 3 (by norm_num) (by norm_num),
				apply modeq.trans (modeq.trans h0.symm $ modeq.modeq_add_mul_mod k),
				apply modeq.trans _ ((zmod.eq_iff_modeq_nat 3).mp ht1).symm,
				rwa hr },
			{ rw ← hn at hr, linarith } },
		{	-- Case : b ≡ 0 and t ≡ 2 [MOD 3]
			have ht1 : (↑0 : zmod 3) = ↑((t + 1) * (t + 1)) := by { simp [← tm, h], ring },
			rcases modeq.add_mul_mod_of_modeq (hbt 0) (modeq.trans h0 _) with ⟨n, hn⟩, swap,
			{ rwa ← zmod.eq_iff_modeq_nat 3 },
			use [0, n, hn],
			change b + 3 * n = (t + 1) * (t + 1) at hn,
			intros k hkn,
			-- There is no possible square before it, so (t + 1)² must be the first
			apply no_middle_square (lt_of_lt_of_le htb _),
			{	rw ← hn, linarith },
			linarith } },
	{	let tm : zmod 3 := t,
		fin_cases tm,
		{	-- Case : b ≡ 1 and t ≡ 0 [MOD 3]
			have ht1 : (↑1 : zmod 3) = ↑((t + 1) * (t + 1)) := by { simp [← tm, h] },
			rcases modeq.add_mul_mod_of_modeq (hbt 0) (modeq.trans h1 _) with ⟨n, hn⟩, swap,
			{	rwa ← zmod.eq_iff_modeq_nat 3 },
			use [0, n, hn],
			change b + 3 * n = (t + 1) * (t + 1) at hn,
			intros k hkn,
			-- There is no possible square before it, so (t + 1)² must be the first
			apply no_middle_square (lt_of_lt_of_le htb _),
			{	rw ← hn, linarith },
			linarith },
		{ -- Case : b ≡ 1 and t ≡ 1 [MOD 3]
			have ht1 : (↑1 : zmod 3) = ↑((t + 1) * (t + 1)) := by { simp [← tm, h], ring },
			rcases modeq.add_mul_mod_of_modeq (hbt 0) (modeq.trans h1 _) with ⟨n, hn⟩, swap,
			{	rwa ← zmod.eq_iff_modeq_nat 3 },
			use [0, n, hn],
			change b + 3 * n = (t + 1) * (t + 1) at hn,
			intros k hkn,
			-- There is no possible square before it, so (t + 1)² must be the first
			apply no_middle_square (lt_of_lt_of_le htb _),
			{	rw ← hn, linarith },
			linarith },
		{ -- Case : b ≡ 1 and t ≡ 2 [MOD 3]
			have ht1 : (↑0 : zmod 3) = ↑((t + 1) * (t + 1)) := by { simp [← tm, h], ring },
			have ht2 : (↑1 : zmod 3) = ↑((t + 2) * (t + 2)) := by { simp [← tm, h], ring },
			rcases modeq.add_mul_mod_of_modeq (hbt 1) (modeq.trans h1 _) with ⟨n, hn⟩, swap,
			{	rwa ← zmod.eq_iff_modeq_nat 3 },
			use [1, n, hn],
			change b + 3 * n = (t + 2) * (t + 2) at hn,
			intros k hkn hsq,
			-- Show that (t + 2)² by eliminating the previous one
			rcases @middle_squares _ t 2 _ _ hsq with ⟨r, hlr, hr⟩, swap,
			{	linarith }, swap,
			{ rw ← hn, linarith },
			interval_cases r,
			{ linarith },
			{ apply @modeq.not_modeq_of_lt 0 1 3 (by norm_num) (by norm_num),
				apply modeq.trans ((zmod.eq_iff_modeq_nat 3).mp ht1),
				apply modeq.trans _ (modeq.trans (modeq.modeq_add_mul_mod k).symm h1),
				rwa hr },
			{ rw ← hn at hr, linarith }	} },
end