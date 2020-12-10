/-
Author: Adrián Doña Mateo.
-/

import data.mv_polynomial.basic
import ring_theory.polynomial.homogeneous

noncomputable theory

open mv_polynomial (hiding X)
open finset

/-- Convenient names for the two variables in an xy_poly -/
def X : mv_polynomial (fin 2) ℤ := mv_polynomial.X 0
def Y : mv_polynomial (fin 2) ℤ := mv_polynomial.X 1

def l (p : ℤ × ℤ) : mv_polynomial (fin 2) ℤ := C p.2 * X - C p.1 * Y

lemma l_eval_aux (p : ℤ × ℤ) (xy : fin 2 → ℤ) : eval xy (l p) = p.2 * (xy 0) - p.1 * (xy 1) :=
begin
	unfold l, simp [eval_monomial], congr;
	{	simp [X, Y, eval_X] },
end

lemma l_is_homogeneous (p : ℤ × ℤ) : is_homogeneous (l p) 1 :=
begin
	unfold l,	apply is_homogeneous.add,
	{ unfold X mv_polynomial.X,
		rw C_mul_monomial,
		apply is_homogeneous_monomial,
		rw [finsupp.support_single_ne_zero (nat.one_ne_zero), sum_singleton], simp },
	unfold Y mv_polynomial.X,
	convert @is_homogeneous_monomial (fin 2) ℤ _ (finsupp.single 1 1) (-p.1) 1 _,
	{ conv_rhs { rw [← mul_one (-p.1), ← C_mul_monomial] }, simp },
	rw [finsupp.support_single_ne_zero (nat.one_ne_zero), sum_singleton], simp,
end


