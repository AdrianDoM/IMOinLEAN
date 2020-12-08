/-
Author: Adrián Doña Mateo
-/

import data.real.basic

/-!
# IMO 2017 Q2

Let ℝ be the set of real numbers. Determine all functions f : ℝ → ℝ such that, for
all real numbers x and y,

	f (f x * f y) + f (x + y) = f (x * y).
-/

open real

/-- A predicate defining what it means for a function to be a solution -/
def sol (f : ℝ → ℝ) : Prop := ∀ x y, f (f x * f y) + f (x + y) = f (x * y)

/-- The negation of a function -/
def neg (f : ℝ → ℝ) : ℝ → ℝ := λ x, - f x

lemma neg_neg_f (f : ℝ → ℝ) : neg (neg f) = f := by simp [neg]

/-- The negation of a solution is also a solution -/
theorem sol_of_neg_sol {f : ℝ → ℝ} (h : sol f) : sol (neg f) :=
λ x y,
calc - f ((- f x) * (- f y)) + (- f (x + y))
		= - (f (f x * f y) + f (x + y)) : by rw [neg_mul_neg, neg_add]
... = - f (x * y)                   : by rw h

lemma sol_mul_eq_zero {f : ℝ → ℝ} (hf : sol f) (x : ℝ) (hx : x ≠ 1) :
	f (f x * f (x / (x - 1))) = 0 :=
begin
	have hxy : x + x / (x - 1) = x * (x / (x - 1)) :=
		calc x + x / (x - 1)
				= (x * (x - 1) + x) / (x - 1) : by { rw add_div', intro h,
																					rw sub_eq_zero.mp h at hx, contradiction }
		... = (x * x) / (x - 1)           : by ring
		... = x * (x / (x - 1))           : by rw mul_div_assoc,
	rw [← add_sub_cancel (f _) (f (x + x / (x - 1))), hf, hxy, sub_self],
end

/-- A solution has a root at (f 0)² -/
theorem sol_has_zero {f : ℝ → ℝ} (hf : sol f) : f (f 0 ^ 2) = 0 :=
by { convert sol_mul_eq_zero hf 0 (by norm_num), simp [pow_two] }

theorem zero_of_zero_at_zero {f : ℝ → ℝ} (hf : sol f) (h0 : f 0 = 0) : f = λ _, 0 :=
begin
	ext x,
	calc f x
			= f (f x * f 0) + f (x + 0) : by simp [h0]
	... = f 0                       : by rw [hf, mul_zero]
	... = 0                         : h0
end

/- 
From here on, we work on the consequences of assuming that f 0 < 0.
This is enough, because if f is a solution and f 0 < 0, then g = neg f is a solution with g 0 < 0.
-/

theorem of_neg_at_zero {f : ℝ → ℝ} (hf : sol f) (h0 : f 0 < 0) :
	f 1 = 0 ∧ (∀ a, f a = 0 → a = 1) ∧ f 0 = -1 :=
begin
	have ha : ∀ a, f a = 0 → a = 1,
	{ intros a ha, by_contradiction,
		apply ne_of_lt h0,
		convert sol_mul_eq_zero hf a h,
		rw [ha, zero_mul] },
	have hf02 : f 0 ^ 2 = 1 := ha _ (sol_has_zero hf),
	use [by rw [← hf02, sol_has_zero hf], ha],
	rw [pow_two, mul_self_eq_one_iff] at hf02,
	cases hf02 with h1 hn1, swap,
	{ assumption },
	linarith,
end

theorem sol_at_add_n {f : ℝ → ℝ} (hf : sol f) (h0 : f 0 < 0) : ∀ x (n : ℤ), f (x + n) = f x + n :=
begin
	rcases of_neg_at_zero hf h0 with ⟨hf1, _, hf0⟩,
	have hadd1 : ∀ x, f (x + 1) = f x + 1 :=
		λ x,
		calc f (x + 1)
			  = f (f x * f 1) + f (x + 1) + 1 : by simp [hf0, hf1]
		... = f x + 1                       : by rw [hf, mul_one],
	have haddn : ∀ x (n : ℕ), f (x + n) = f x + n,
	{ intros x n, induction n with n ih, { simp },
		simp, rw [← add_assoc, hadd1, ih, add_assoc] },
	intros x n,
	cases n with n n,
	{	exact haddn x n },
	dsimp,
	rw [← sub_eq_add_neg, ← sub_eq_add_neg, eq_sub_iff_add_eq],
	convert (haddn _ (n + 1)).symm, simp,
end

lemma root_of_nonneg_disc {a b : ℝ} (h : 0 ≤ a * a - 4 * b) :
	∃ x y, x + y = a ∧ x * y = b :=
begin
	set d := a * a - 4 * b with hd,
	use [(a + sqrt d) / 2, (a - sqrt d) / 2],
	split, { ring },
	rw div_mul_div,
	calc (a + sqrt d) * (a - sqrt d) / (2 * 2)
			= (a * a - (sqrt d) * (sqrt d)) / 4 : by ring
	... = (a * a - (a * a - 4 * b)) / 4     : by rw [mul_self_sqrt h]
	... = b                                 : by ring,
end

theorem f_injective {f : ℝ → ℝ} (hf : sol f) (h0 : f 0 < 0) : function.injective f :=
begin
	intros a b hfab, by_contradiction,
	have haddN : ∀ N : ℤ, f (a + N + ↑1) = f (b + N) + 1 :=
		λ N,
		calc f (a + N + ↑(1 : ℤ))
				= f (a + ↑(N + 1)) : by rw [add_assoc, int.cast_add]
		... = f a + ↑(N + 1)   : by rw sol_at_add_n hf h0
		... = f b + ↑(N + 1)   : by rw hfab
		... = f b + N + 1      : by { rw [int.cast_add, ← add_assoc], norm_cast }
		... = f (b + N) + 1    : by rw ← sol_at_add_n hf h0,
	simp at haddN,
	let N := ⌈-b - 1⌉,
	have hN : ↑N < -b := by { simp [N], convert ceil_lt_add_one (-b - 1), ring },
	have habN : 0 ≤ (a + N + 1) * (a + N + 1) - 4 * (b + N),
	{	rw sub_eq_add_neg, apply add_nonneg,
		{	exact mul_self_nonneg _ }, linarith },
	rcases root_of_nonneg_disc habN with ⟨x, y, hxy1, hxy2⟩,
	have hfxy : f x * f y = 0,
	{ rw [← add_sub_cancel (f x * f y) 1, sub_eq_zero],
		apply (of_neg_at_zero hf h0).2.1,
		have : _ :=
		calc f (f x * f y + ↑(1 : ℤ))
				= f (f x * f y) + 1                           : by { rw sol_at_add_n hf h0 _ 1, simp }
		... = (f (f x * f y) + f (x + y) - f (x + y)) + 1 : by rw add_sub_cancel
		... = (f (x * y) - f (x + y)) + 1                 : by rw hf
		... = f (x * y) + 1 - f (x + y)                   : by ring
		... = f (b + N) + 1 - f (a + N + 1)               : by rw [hxy1, hxy2]
		... = f (a + N + 1) - f (a + N + 1)               : by rw haddN N
		... = 0                                           : by rw sub_self,
		convert this, norm_cast },
	have hx1 : x ≠ 1,
	{	intro hx, rw [hx, one_mul] at hxy2, rw [hx, hxy2] at hxy1,
		have : a = b := by linarith, exact h this },
	have hy1 : y ≠ 1,
	{ intro hy, rw [hy, mul_one] at hxy2, rw [hy, hxy2] at hxy1,
		have : a = b := by linarith, exact h this },
	cases mul_eq_zero.mp hfxy with hx0 hy0,
	{	exact hx1 ((of_neg_at_zero hf h0).2.1 _ hx0) },
	{	exact hy1 ((of_neg_at_zero hf h0).2.1 _ hy0) },
end

lemma mul_sol_at_neg {f : ℝ → ℝ} (hf : sol f) (h0 : f 0 < 0) :
	∀ t, f t * f (-t) = -t * t + 1 :=
begin
	intro t,
	have : f t * f (-t) = -t * t + ↑(1 : ℤ),
	{ apply f_injective hf h0,
	  calc f (f t * f (-t))
				= f (f t * f (-t)) + f 0 + ↑(1 : ℤ)        : by simp [(of_neg_at_zero hf h0).2.2]
		... = f (f t * f (-t)) + f (t + -t) + ↑(1 : ℤ) : by rw add_neg_self
		... = f (t * -t) + ↑(1 : ℤ)                    : by rw hf
		... = f (-t * t) + ↑(1 : ℤ)                    : by rw mul_comm
		... = f (-t * t + ↑(1 : ℤ))                    : by rw ← sol_at_add_n hf h0 _ 1 },
	convert this, norm_cast,
end

lemma mul_sol_at_one_sub {f : ℝ → ℝ} (hf : sol f) (h0 : f 0 < 0) :
	∀ t, f t * f (1 - t) = t * (1 - t) :=
begin
	intro t,
	apply f_injective hf h0,
	calc f (f t * f (1 - t))
			= f (f t * f (1 - t)) + 0               : by rw add_zero
	... = f (f t * f (1 - t)) + f 1             : by rw (of_neg_at_zero hf h0).1
	... = f (f t * f (1 - t)) + f (t + (1 - t)) : by rw add_sub_cancel'_right
	... = f (t * (1 - t))                       : by rw hf,
end

theorem sol_of_neg_at_zero {f : ℝ → ℝ} (hf : sol f) (h0 : f 0 < 0) :
	f = λ t, t - 1 :=
begin
	ext t,
	calc f t
			= f t + (-t * t + 1) - (-t * t + 1)        : by rw add_sub_cancel
	... = f t + f t * f (-t) - (-t * t + 1)        : by rw mul_sol_at_neg hf h0
	... = f t * (1 + f (-t)) - (-t * t + 1)        : by ring
	... = f t * (f (-t) + ↑(1 : ℤ)) - (-t * t + 1) : by simp [add_comm]
	... = f t * f (-t + ↑(1 : ℤ)) - (-t * t + 1)   : by rw ← sol_at_add_n hf h0 _ 1
	... = f t * f (1 - t) - (-t * t + 1)           : by simp [add_comm, ← sub_eq_add_neg]
	... = t * (1 - t) - (-t * t + 1)               : by rw mul_sol_at_one_sub hf h0
	... = t - 1                                    : by ring,
end

theorem sol_iff (f : ℝ → ℝ) : sol f ↔ f = (λ _, 0) ∨ f = (λ x, x - 1) ∨ f = (λ x, 1 - x) :=
begin
	split, swap,
	{	intro h, rcases h with rfl | rfl | rfl,
		{	intros x y, simp },
		{ intros x y, simp, ring },
		{ intros x y, simp, ring } },
	rcases lt_trichotomy (f 0) 0 with hneg | h0 | hpos,
	{	intro hf, right, left, exact sol_of_neg_at_zero hf hneg },
	{	intro hf, left, exact zero_of_zero_at_zero hf h0 },
	{ intro hf, right, right,
		have hnegf : sol (neg f) := sol_of_neg_sol hf,
		have hnegf0 : neg f 0 < 0 := by simpa [neg],
		have : neg f = λ x, x - 1 := sol_of_neg_at_zero hnegf hnegf0,
		rw [← neg_neg_f f, this], simp [neg] },
end