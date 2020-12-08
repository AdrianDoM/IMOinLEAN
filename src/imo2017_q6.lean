/-
Author: Adrián Doña Mateo
-/

import data.int.gcd
import ring_theory.polynomial.homogeneous
import algebra.module.basic
import tactic
import int
import mv_polynomial

/-!
# IMO 2017 Q6

An ordered pair (x,y) of integers is a primitive root if the greatest common divisor
of x and y is 1. Given a finite set S of primitive points, prove that there exists a
positive integer n and integers a₀, a₁, ..., aₙ such that, for each (x,y) in S, we have:

	a₀xⁿ + a₁xⁿ⁻¹y + a₂xⁿ⁻²y² + ⋯ + aₙ₋₁xyⁿ⁻¹ + aₙyⁿ = 1.
-/

noncomputable theory

open mv_polynomial (hiding X)
open int
open_locale big_operators

/-- An ordered pair (x,y) of integers is a primitive root of the greatest commond divisor
of x and y is 1 -/
def primitive_root (p : ℤ × ℤ) : Prop := gcd p.fst p.snd = 1

local attribute [instance, priority 1000] semiring.to_semimodule

namespace primitive_root

lemma neg {p : ℤ × ℤ} (h : primitive_root p) : primitive_root (-p) :=
by { unfold primitive_root at *, simp, unfold gcd at *, simpa }

/-- If two primitive are multiples of each other they must either be the same primitive root
or the negation of each other -/
lemma of_mul_primitive {p : ℤ × ℤ} {n : ℤ} (h : primitive_root (n • p)) :
	primitive_root p ∧ (n = 1 ∨ n = -1) :=
begin
	have hn : n = 1 ∨ n = -1,
	{ simp [primitive_root] at h,
		have hn : n ∣ ↑1 := by { rw [← h], apply dvd_gcd; apply dvd_mul_right },
		exact dvd_one hn },
	split, swap, { exact hn },
	cases hn with h1 hn1,
	{	rw h1 at h, simp at h, assumption },
	rw hn1 at h, simp at h,
	rw ← neg_neg p,
	apply neg h,
end

end primitive_root

lemma sq_eq_one {φ : mv_polynomial (fin 2) ℤ} {xy : fin 2 → ℤ} :
	eval xy φ = 1 ∨ eval xy φ = -1 → eval xy (φ * φ) = 1 :=
λ h, by rwa [eval_mul, mul_self_eq_one_iff]

/-- In a homogeneous polynomial φ, all monomials have the same degree -/
theorem monomial_deg {φ : mv_polynomial (fin 2) ℤ} {n : ℕ} (hφ : is_homogeneous φ n) :
	∀ ⦃d⦄, coeff d φ ≠ 0 → d 0 + d 1 = n :=
begin
	intros d hcoeff,
	rw ← hφ hcoeff,
	show _ = d.sum (λ _ x, x),
	rw finsupp.sum_fintype,
	{	refl },
	intro, refl,
end

lemma even_iff_eq_zero_mod_two {n : ℕ} : even n ↔ n % 2 = 0 :=
by rw [even_iff_two_dvd, nat.dvd_iff_mod_eq_zero]

lemma not_even_iff_eq_one_mod_two {n : ℕ} : ¬ even n ↔ n % 2 = 1 :=
begin
	rw [not_iff_comm, even_iff_eq_zero_mod_two],
	split, swap,
	{ intros h hn, rw h at hn, contradiction },
	intro h,
	have : n % 2 < 2 := nat.mod_lt _ (by norm_num),
	interval_cases (n % 2), { assumption }, contradiction,
end

/-- If a homogeneous polynomial φ evaluates to an integer a at some (x, y), then it evaluates
to ±a at (-x, -y). This shows that it is enough to consider a set S where no two primitive roots
are multiples of each other -/
lemma eval_pm_of_homogeneous_at_neg {φ : mv_polynomial (fin 2) ℤ} {n : ℕ} {xy : fin 2 → ℤ}
	(hφ : is_homogeneous φ n) :
	eval (λ i, - xy i) φ = eval xy φ ∨ eval (λ i, - xy i) φ = - eval xy φ :=
begin
	rw [eval_eq', eval_eq'],
	have h : ∀ {d : fin 2 →₀ ℕ}, ∏ i, (-xy i) ^ d i = (-1) ^ (d 0 + d 1) * ∏ i, xy i ^ d i,
	{	intro d,
		show ((-xy 0) ^ _) * ((-xy 1) ^ _ * 1) = _ * (((xy 0) ^ _) * ((xy 1) ^ _ * 1)),
		set x := xy 0, set y := xy 1, simp,
		calc (-x) ^ d 0 * (-y) ^ d 1
		    = (-1 * x) ^ d 0 * (-1 * y) ^ d 1          : by simp
		... = (-1) ^ (d 0 + d 1) * (x ^ d 0 * y ^ d 1) : by ring_exp },
	by_cases hn : even n,
	{	left,	congr, ext d,
		by_cases hc : coeff d φ = 0, { simp [hc] },
		congr' 1,
		have hd : (d 0 + d 1) % 2 = 0 :=
			by rwa [monomial_deg hφ hc, ← even_iff_eq_zero_mod_two],
		rw [h, neg_one_pow_eq_pow_mod_two, hd, pow_zero, one_mul] },
	right,
	rw ← finset.sum_neg_distrib,
	congr, ext d,
	by_cases hc : coeff d φ = 0, { simp [hc] },
	rw neg_mul_eq_mul_neg, congr,
	have hd : (d 0 + d 1) % 2 = 1 :=
		by rwa [monomial_deg hφ hc, ← not_even_iff_eq_one_mod_two],
	rw [h, neg_one_pow_eq_pow_mod_two, hd, pow_one, ← neg_eq_neg_one_mul],
end

def to_val (p : ℤ × ℤ) : fin 2 → ℤ
| ⟨0, _⟩   := p.1
| ⟨1, _⟩   := p.2
| ⟨_, _⟩   := 0

lemma to_val_neg (p : ℤ × ℤ) : to_val (-p) = λ i, -to_val p i :=
begin
	ext i, fin_cases i,
	{	show (-p).1 = -p.1, simp },
	show (-p).2 = -p.2, simp,
end

def sol_aux (T : set (ℤ × ℤ)) (φ : mv_polynomial (fin 2) ℤ) : Prop :=
(∃ n, is_homogeneous φ n) ∧ ∀ t ∈ T, eval (to_val t) φ = 1 ∨ eval (to_val t) φ = -1

def sol (T : set (ℤ × ℤ)) (φ : mv_polynomial (fin 2) ℤ) : Prop :=
(∃ n, is_homogeneous φ n) ∧ ∀ t ∈ T, eval (to_val t) φ = 1

/-- The finite set of primitive roots -/
constant S : set (ℤ × ℤ)
constant hS : ∀ p ∈ S, primitive_root p
constant hfin : set.finite S

theorem sol_aux_of_T {T : set (ℤ × ℤ)} (hT : ∀ s ∈ S, ∃ t ∈ T, ∃ (n : ℤ), s = n • t)
	{φ : mv_polynomial (fin 2) ℤ} (hφ : sol_aux T φ) : sol_aux S φ :=
begin
	rcases hφ with ⟨⟨m, hhom⟩, hφT⟩,
	use ⟨m, hhom⟩,
	intros s hs,
	rcases hT s hs with ⟨t, ht, n, hn⟩,
	rcases (@primitive_root.of_mul_primitive t n $ hn ▸ hS s hs).2 with rfl | rfl,
	{	simp at hn, rw hn, exact hφT t ht },
	simp at hn, rw [hn, to_val_neg],
	cases hφT t ht with h1 hn1,
	{	rw ← h1, apply eval_pm_of_homogeneous_at_neg hhom },
	rw [← hn1, ← neg_neg (1 : ℤ), ← hn1, or_comm],
	apply eval_pm_of_homogeneous_at_neg hhom,
end

theorem sol_of_sol_aux {T : set (ℤ × ℤ)} {φ : mv_polynomial (fin 2) ℤ} :
	sol_aux T φ → sol T (φ * φ) :=
λ ⟨⟨n, hhom⟩, h⟩, ⟨⟨n + n, is_homogeneous.mul hhom hhom⟩, λ t ht, sq_eq_one (h t ht)⟩

/- From the past two theorems, we deduce that there is no harm in assuming that S has no
primitive roots that are multiples of another primitive root in S. Moreover, it suffices
to find a polynomial that evaluates to 1 or -1 at each point in S. -/

/-- Convenient names for the two variables in an xy_poly -/
def X : mv_polynomial (fin 2) ℤ := mv_polynomial.X 0
def Y : mv_polynomial (fin 2) ℤ := mv_polynomial.X 1
