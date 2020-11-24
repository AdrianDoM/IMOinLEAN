/-
Author: Adrián Doña Mateo.
-/

import algebra.archimedean
import data.nat.modeq
import data.nat.sqrt
import data.zmod.basic
import tactic

import modeq
import sqrt

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

/- Convenience lemmas for determining the next term of the sequence -/
lemma a_succ_of_sq {a₀ n : ℕ} (k : ℕ) (hk : k * k = a a₀ n) :
	a a₀ (n + 1) = k :=
begin
	have hsq : sqrt (a a₀ n) = k := by { rw ← hk, exact sqrt_eq k },
	simp [a],
	split_ifs,
	{ assumption },
	rw hsq at h,
	contradiction
end

lemma a_succ_of_not_sq {a₀ n : ℕ} (h : ¬ ∃ k, k * k = a a₀ n) :
	a a₀ (n + 1) = a a₀ n + 3 :=
begin
	simp [a],
	split_ifs with hsq, swap,
	{ refl },
	exfalso,
	exact h ⟨sqrt (a a₀ n), hsq⟩,
end

/- Convenience lemma for determine terms of the sequence in a run of not squares -/
lemma a_no_squares {a₀ n k : ℕ} (h : ∀ i, i < k → ¬ ∃ t, t * t = a a₀ n + 3 * i) :
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
lemma periodic_of_term_equal {a₀ m n : ℕ} (hmn : m < n) (h : a a₀ m = a a₀ n) :
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
	{	refl },
	have h2 : a a₀ (n + m) ≡ 2 [MOD 3] := modeq.trans (modeq.symm _) h, swap,
	{ rw ih, exact modeq.modeq_add_mul_mod m },
	rw [add_succ, a_succ_of_not_sq (not_square_of_two_mod_three h2), ih, add_assoc, mul_succ],
end

/-- If a term of the sequence is congruent to 2 modulo 3 then it is not periodic -/
lemma not_periodic_of_term_cong_two (a₀ n : ℕ) (h : a a₀ n ≡ 2 [MOD 3]) :
	¬ periodic a₀ :=
begin
	rintro ⟨A, hA⟩,
	rcases hA n with ⟨m₁, hnm₁, hm₁⟩,
	have : a a₀ m₁ ≡ 2 [MOD 3],
	{	apply modeq.trans _ h,
		have : (↑(a a₀ m₁) : zmod 3) = ↑(a a₀ n + 3 * (m₁ - n)), 
		{	congr,
			convert increasing_of_term_cong_two h (m₁ - n),
			rw nat.add_sub_cancel' hnm₁ },
		simp at this,
		rwa ←zmod.eq_iff_modeq_nat 3 },
	rcases hA (m₁ + 1) with ⟨m₂, hmm₂, hm₂⟩,
	have : a a₀ m₂ = A + 3 * (m₂ - m₁),
	{	rw ←hm₁,
		convert increasing_of_term_cong_two this (m₂ - m₁),
		rw nat.add_sub_cancel' (le_of_succ_le hmm₂) },
	rw hm₂ at this,
	have hmm₂ : 0 < m₂ - m₁, from nat.sub_pos_of_lt (lt_of_succ_le hmm₂),
	linarith, 
end

/- This long lemma takes care of each possibility for b and t mod 3. -/
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

/-- If ¬ aₙ ≡ 2 [MOD 3] and aₙ > 9 then there is an index m > n such that aₘ < aₙ -/
lemma term_lt_of_term_congr_0_or_1 {a₀ n : ℕ} (h : a a₀ n ≡ 0 [MOD 3] ∨ a a₀ n ≡ 1 [MOD 3]) (h9 : 9 < a a₀ n) :
	∃ m, m > n ∧ a a₀ m < a a₀ n :=
begin
	rcases first_square h (by linarith) with ⟨j, m, hnm, ham, hfirst⟩,
	use [m + 1, by linarith],
	rw a_succ_of_sq _ ham.symm,
	have h9 : 9 ≤ a a₀ n - 1 := le_pred_of_lt h2,
	have h3 : 3 ≤ sqrt (a a₀ n - 1) := le_sqrt.mpr h9,
	have h2 : 2 ≤ sqrt (a a₀ n - 1) := le_of_succ_le h3,
	calc sqrt (a a₀ n - 1) + 1 + ↑j
			≤ sqrt (a a₀ n - 1) + 3
		:	by { have : ↑j ≤ 2, from le_of_lt_succ (fin.is_lt j),	linarith }
	... ≤ sqrt (a a₀ n - 1) + sqrt (a a₀ n - 1)
		: by linarith
	... = 2 * sqrt (a a₀ n - 1)
		: by rw two_mul
	... ≤ sqrt (a a₀ n - 1) * sqrt (a a₀ n - 1)
		: by { apply mul_le_mul h2, refl, repeat {linarith} }
	... ≤ a a₀ n - 1
		: by apply sqrt_le
	... < a a₀ n
		:	by { rw ←pred_eq_sub_one, apply pred_lt, linarith }
end

/-- A multiple of 3 is always followed by a multiple of 3 -/
lemma mul_three_of_mul_three {a₀ n : ℕ} (h : a a₀ n ≡ 0 [MOD 3]) :
	∀ m, n ≤ m → a a₀ m ≡ 0 [MOD 3] :=
begin
	have : ∀ k, a a₀ (n + k) ≡ 0 [MOD 3],
	{ intro k,
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
		simp [modeq] },
	intros m hnm,
	convert this (m - n),
	rw nat.add_sub_cancel' hnm,
end


/-- If aₙ ∈ {3,6,9}, then the sequence visits three infinitely many times -/
lemma periodic_of_three_six_nine {a₀ n : ℕ} (h : a a₀ n = 3 ∨ a a₀ n = 6 ∨ a a₀ n = 9) :
	periodic a₀ :=
begin
	have h9 : ∀ n, a a₀ n = 9 → a a₀ (n+1) = 3,
	{ intros n h,
		apply a_succ_of_sq 3, rw h, refl },
	have h6 : ∀ n, a a₀ n = 6 → a a₀ (n+1) = 9,
	{	intros n h,
		convert a_succ_of_not_sq _,
		{	rw h },
		rw h,
		apply @no_middle_square 6 2; norm_num },
	have h3 : ∀ n, a a₀ n = 3 → a a₀ (n+1) = 6,
	{	intros n h,
		convert a_succ_of_not_sq _,
		{ rw h},
		rw h,
		apply @no_middle_square 3 1; norm_num },
	have hper : (∃ n, a a₀ n = 3) → periodic a₀,
	{	rintro ⟨n, hn⟩,
		apply @periodic_of_term_equal _ n (n + 3) (by linarith),
		rw [hn, h9 _ (h6 _ (h3 _ hn))] },
	rcases h with c3 | c6 | c9,
	{	exact hper ⟨n, c3⟩ },
	{ have : a a₀ (n+1) = 9, from h6 _ c6,
		have : a a₀ (n+2) = 3, from h9 _ this,
		exact hper ⟨n+2, this⟩ },
	{ have : a a₀ (n+1) = 3, from h9 _ c9,
		exact hper ⟨n+1, this⟩ },
end

lemma mul_three_le_9 {x : ℕ} (h9 : x ≤ 9) (h3 : 3 ∣ x) : x = 0 ∨ x = 3 ∨ x = 6 ∨ x = 9 :=
begin
    cases h3 with k h3k,
    have : k ≤ 3 := by linarith,
    interval_cases k; dec_trivial!,
end

/-- If aₙ ≡ 0 [MOD 3], then there is an index m > n such that aₘ = 3 -/
lemma periodic_of_term_cong_zero (a₀ n : ℕ) (h : a a₀ n ≡ 0 [MOD 3]) :
	periodic a₀ :=
begin
	have hlt : ∀ k, 9 ≤ a a₀ n - k → ∃ m, n ≤ m ∧ a a₀ m ≤ a a₀ n - k,
	{	intro k,
		induction k with k ih,
		{	intro, use [n, by refl], rw nat.sub_zero },
		intro hk,
		have hk' : 9 ≤ a a₀ n - k,
		{	rw sub_succ at hk,
			apply le_trans hk (pred_le _) },
		rcases ih hk' with ⟨m, hnm, hm⟩,
		by_cases h9 : a a₀ m ≤ 9,
		{	use [m, hnm, le_trans h9 hk] },
		have h0 : a a₀ m ≡ 0 [MOD 3] := mul_three_of_mul_three h m hnm,
		have hn2 : ¬ a a₀ m ≡ 2 [MOD 3] := by { apply modeq.not_modeq_of_modeq _ _ h0; norm_num },
		have h9 : 9 < a a₀ m, from lt_of_not_ge h9,
		rcases term_lt_of_term_not_congr_2 hn2 h9 with ⟨m', hnm', hm'⟩,
		use [m', le_trans hnm (le_of_lt hnm')],
		rw sub_succ,
		apply le_pred_of_lt,
		apply lt_of_lt_of_le hm' hm	},
	have : ∃ m, n ≤ m ∧ a a₀ m ≤ 9,
	{	by_cases h9 : a a₀ n ≤ 9,
		{ use [n, h9] },
		have : a a₀ n - (a a₀ n - 9) = 9, from nat.sub_sub_self (le_of_not_le h9),
		rcases hlt (a a₀ n - 9) (le_of_eq (eq.symm this)) with ⟨m, hnm, hm⟩,
		rw this at hm,
		use [m, hnm, hm] },
	rcases this with ⟨m, hnm, hm⟩,
	have : a a₀ m = 0 ∨ a a₀ m = 3 ∨ a a₀ m = 6 ∨ a a₀ m = 9,
	{	apply mul_three_le_9 hm,
		rw ←modeq.modeq_zero_iff,
		exact mul_three_of_mul_three h m hnm },
	cases this with h0 h369,
	{	apply @periodic_of_term_equal _ m (m + 1) (lt_succ_self m), 
		rw h0,
		simp [a],
		split_ifs,
		{	rw h0, refl },
		rw h0 at h_1,
		contradiction },
	apply periodic_of_three_six_nine h369,
end

lemma term_cong_two_of_four_seven {a₀ n : ℕ} (h : a a₀ n = 4 ∨ a a₀ n = 7) :
	∃ m, n < m ∧ a a₀ m ≡ 2 [MOD 3] :=
begin
	have h4 : ∀ n, a a₀ n = 4 → a a₀ (n+1) = 2 :=
		λ n hn, a_succ_of_sq 2 (by { rw hn, refl }),
	have h7 : ∀ n, a a₀ n = 7 → a a₀ (n+1) = 10,
	{ intros n han, convert a_succ_of_not_sq _, { rw han },
		rw han,	apply @no_middle_square 7 2; norm_num },
	have h10 : ∀ n, a a₀ n = 10 → a a₀ (n+1) = 13,
	{ intros n han, convert a_succ_of_not_sq _, { rw han },
		rw han, apply @no_middle_square 10 3; norm_num },
	have h13 : ∀ n, a a₀ n = 13 → a a₀ (n+1) = 16,
	{ intros n han, convert a_succ_of_not_sq _, { rw han },
		rw han, apply @no_middle_square 13 3; norm_num },
	have h16 : ∀ n, a a₀ n = 16 → a a₀ (n+1) = 4 :=
		λ n hn, a_succ_of_sq 4 (by { rw hn, refl }),
	cases h with c4 c7,
	{	use [n + 1, lt_succ_self n],
		have : a a₀ (n+1) = 2, from h4 _ c4,
		rw this },
	{ use [n + 5, by linarith],
		have : a a₀ (n+1) = 10, from h7 _ c7,
		have : a a₀ (n+2) = 13, from h10 _ this,
		have : a a₀ (n+3) = 16, from h13 _ this,
		have : a a₀ (n+4) = 4, from h16 _ this,
		have : a a₀ (n+5) = 2, from h4 _ this,
		rw this },
end

/-- All numbers ≤ 9 that are congruent to 1 mod 3 -/
lemma eq_1_4_7_of_cong_1_le_9 (x : ℕ) (h9 : x ≤ 9) (h1 : x ≡ 1 [MOD 3]) :
	x = 1 ∨ x = 4 ∨ x = 7 :=
begin
	by_cases h : x < 1,
	{	interval_cases x, contradiction },
	have hx1 : 1 ≤ x, from le_of_not_lt h,
	have : 3 ∣ x - 1, from (modeq.modeq_iff_dvd' hx1).mp (modeq.symm h1),
	cases this with k h3k,
	have : x = 3 * k + 1, { rw [←nat.sub_add_cancel hx1, h3k] },
	have : k ≤ 8, linarith,
	interval_cases k; dec_trivial!,
end

/-- If aₙ ≡ 1 [MOD 3], then there is an index m > n such that aₘ ≡ 2 [MOD 3] -/
lemma term_cong_two_of_term_cong_one (a₀ n : ℕ) (h : a a₀ n ≡ 1 [MOD 3]) :
	∃ m, m > n ∧ a a₀ m ≡ 2 [MOD 3] :=
begin
	by_contradiction hf,
	have h1 : ∀ k, a a₀ (n + k) ≡ 1 [MOD 3],
	{ intro k,
		induction k with k ih,
		{ assumption },
		rw add_succ,
		simp [a],
		split_ifs with h',
		{	apply (zmod.eq_iff_modeq_nat 3).mp,
			set t : zmod 3 := sqrt (a a₀ (n + k)) with ht,
			have h' : (↑(sqrt (a a₀ (n + k)) * sqrt (a a₀ (n + k))) : zmod 3) = ↑(a a₀ (n + k)),
			{	congr, assumption },
			simp [←ht] at h',
			have ih : (↑(a a₀ (n + k)) : zmod 3) = ↑1,
			{	apply (zmod.eq_iff_modeq_nat 3).mpr, assumption },
			rw ih at h',
			fin_cases t,
			{	have : t * t = ↑0, rw h_1, ring,
				have : ↑0 = ↑1, from eq.trans (eq.symm this) h',
				rw (zmod.eq_iff_modeq_nat 3) at this,
				have : 3 ∣ 1, from modeq.modeq_zero_iff.mp (eq.symm this),
				have : 3 ≤ 1, from le_of_dvd (by norm_num) this,
				contradiction },
			{ assumption },
			{	dsimp at h_1,
				have : a a₀ (n + k).succ = sqrt (a a₀ (n + k)),	{	simp [a], split_ifs, refl },
				have : t = ↑(a a₀ (n + k).succ), { rw this },
				exfalso,
				apply hf ⟨(n + k).succ, _, _⟩,
				{ apply lt_of_lt_of_le (lt_succ_self n),
					apply succ_le_succ,
					linarith },
				rw ←(zmod.eq_iff_modeq_nat 3),
				rwa ←this } },
		rw ←(zmod.eq_iff_modeq_nat 3),
		simp,
		rw ←(zmod.eq_iff_modeq_nat 3) at ih,
		assumption },
	have hlt : ∀ k, 9 ≤ a a₀ n - k → ∃ m, n ≤ m ∧ a a₀ m ≤ a a₀ n - k,
	{ intro k,
		induction k with k ih,
		{	intro, use [n, le_refl n, by refl] },
		intro hk,
		have hk' : 9 ≤ a a₀ n - k,
		{	rw sub_succ at hk,
			apply le_trans hk (pred_le _) },
		rcases ih hk' with ⟨m, hnm, hm⟩,
		by_cases h9 : a a₀ m ≤ 9,
		{	use [m, hnm, le_trans h9 hk] },
		have h1 : a a₀ m ≡ 1 [MOD 3],
		{ convert h1 (m - n),
			symmetry,
			apply nat.add_sub_cancel' hnm },
		have hn2 : ¬ a a₀ m ≡ 2 [MOD 3] := by { apply modeq.not_modeq_of_modeq _ _ h1; norm_num },
		have h9 : 9 < a a₀ m, from lt_of_not_ge h9,
		rcases term_lt_of_term_not_congr_2 hn2 h9 with ⟨m', hnm', hm'⟩,
		use [m', le_trans hnm (le_of_lt hnm')],
		rw sub_succ,
		apply le_pred_of_lt,
		apply lt_of_lt_of_le hm' hm },
	sorry
end