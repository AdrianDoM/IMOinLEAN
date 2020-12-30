/-
Author: Adrián Doña Mateo
-/

import data.int.gcd
import data.nat.totient
import ring_theory.polynomial.homogeneous
import field_theory.finite.basic
import algebra.module.basic
import tactic
import int
import mv_polynomial
import finset
import homogeneous
import zmod
import coprime
import prime
import modeq

/-!
# IMO 2017 Q6

An ordered pair (x,y) of integers is a primitive root if the greatest common divisor
of x and y is 1. Given a finite set S of primitive points, prove that there exists a
positive integer n and integers a₀, a₁, ..., aₙ such that, for each (x,y) in S, we have:

	a₀xⁿ + a₁xⁿ⁻¹y + a₂xⁿ⁻²y² + ⋯ + aₙ₋₁xyⁿ⁻¹ + aₙyⁿ = 1.
-/

noncomputable theory

open mv_polynomial (hiding X) int (hiding range) finset
open_locale big_operators

/-- An ordered pair (x,y) of integers is a primitive root of the greatest commond divisor
of x and y is 1 -/
def primitive_root (p : ℤ × ℤ) : Prop := int.gcd p.fst p.snd = 1

local attribute [instance, priority 1000] semiring.to_semimodule

namespace primitive_root

lemma neg {p : ℤ × ℤ} (h : primitive_root p) : primitive_root (-p) :=
by { unfold primitive_root at *, simp, unfold int.gcd at *, simpa }

/-- If two primitive are multiples of each other they must either be the same primitive root
or the negation of each other -/
lemma of_mul_primitive {p : ℤ × ℤ} {n : ℤ} (h : primitive_root (n • p)) :
	primitive_root p ∧ (n = 1 ∨ n = -1) :=
begin
	have hn : n = 1 ∨ n = -1,
	{ simp [primitive_root] at h,
		have hn : n ∣ ↑1 := by { rw [← h], apply int.dvd_gcd; apply dvd_mul_right },
		exact dvd_one hn },
	split, swap, { exact hn },
	cases hn with h1 hn1,
	{	rw h1 at h, simp at h, assumption },
	rw hn1 at h, simp at h,
	rw ← neg_neg p,
	apply neg h,
end

end primitive_root

local notation `polyℤ` := mv_polynomial (fin 2) ℤ

lemma sq_eq_one {φ : polyℤ} {xy : fin 2 → ℤ} :
	eval xy φ = 1 ∨ eval xy φ = -1 → eval xy (φ * φ) = 1 :=
λ h, by rwa [eval_mul, mul_self_eq_one_iff]

/-- In a homogeneous polynomial φ, all monomials have the same degree -/
theorem monomial_deg {φ : polyℤ} {n : ℕ} (hφ : is_homogeneous φ n) :
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
lemma eval_pm_of_homogeneous_at_neg {φ : polyℤ} {n : ℕ} {xy : fin 2 → ℤ}
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

def sol_aux (T : set (ℤ × ℤ)) (φ : polyℤ) : Prop :=
(∃ n, is_homogeneous φ n) ∧ ∀ t ∈ T, eval (to_val t) φ = 1 ∨ eval (to_val t) φ = -1

def sol (T : set (ℤ × ℤ)) (φ : polyℤ) : Prop :=
(∃ n, is_homogeneous φ n) ∧ ∀ t ∈ T, eval (to_val t) φ = 1

theorem sol_aux_of_T {S T : set (ℤ × ℤ)} (hS : ∀ s ∈ S, primitive_root s) 
	(hT : ∀ s ∈ S, ∃ (t ∈ T) (n : ℤ), s = n • t)
	{φ : polyℤ} (hφ : sol_aux T φ) : sol_aux S φ :=
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

theorem sol_of_sol_aux {T : set (ℤ × ℤ)} {φ : polyℤ} :
	sol_aux T φ → sol T (φ * φ) :=
λ ⟨⟨n, hhom⟩, h⟩, ⟨⟨n + n, is_homogeneous.mul hhom hhom⟩, λ t ht, sq_eq_one (h t ht)⟩

/- From the past two theorems, we deduce that there is no harm in assuming that S has no
primitive roots that are multiples of another primitive root in S. Moreover, it suffices
to find a polynomial that evaluates to 1 or -1 at each point in S. The next theorem lets
us extract such a subset from any S. -/

theorem minimal_primitive_root_set {S : finset (ℤ × ℤ)} (hS : ∀ s ∈ S, primitive_root s) :
	∃ T : finset (ℤ × ℤ), T ⊆ S ∧ (∀ t ∈ T, primitive_root t) ∧
	(∀ t₁ t₂ ∈ T, (∃ n : ℤ, t₂ = n • t₁) → t₂ = t₁) ∧ (∀ s ∈ S, ∃ (t ∈ T) (n : ℤ), s = n • t) :=
begin
	apply S.induction_on',
	{	use ∅, simp },
	rintros a R haS hR hanR ⟨T, hTR, hTprim, hTmul, hT⟩,
	by_cases h : ∃ (r ∈ R) (n : ℤ), a = n • r,
	{	use [T, subset.trans hTR (subset_insert _ _), hTprim, hTmul],
		intros a ha,
		rcases mem_insert.mp ha with rfl | ha, swap,
		{	exact hT a ha },
		rcases h with ⟨r, hr, n, hn⟩,
		rcases hT r hr with ⟨t, ht, m, hm⟩,
		use [t, ht, n * m], rw [hn, hm, mul_smul] },
	use [insert a T, insert_subset_insert a hTR],
	repeat { split },
	{ intros t ht,
		rcases mem_insert.mp ht with rfl | ht,
		{	exact hS t haS },
		exact hTprim t ht }, swap,
	{	intros s hs,
		rcases mem_insert.mp hs with rfl | hs,
		{	use [s, mem_insert_self _ _, 1, by simp] },
		rcases hT s hs with ⟨t, ht, n, hn⟩,
		use [t, mem_insert_of_mem ht, n, hn] },
	intros t₁ t₂ ht₁ ht₂ hn,
	rcases mem_insert.mp ht₁ with rfl | ht₁', swap,
	{ rcases mem_insert.mp ht₂ with rfl | ht₂',
		{ exfalso, apply h, use [t₁, mem_of_subset hTR ht₁'], exact hn },
		exact hTmul t₁ t₂ ht₁' ht₂' hn },
	rcases mem_insert.mp ht₂ with rfl | ht₂',
	{ refl },
	exfalso,
	rcases hn with ⟨n, rfl⟩,
	apply h,
	use [n • t₁, mem_of_subset hTR ht₂', n],
	rw ← mul_smul,
	rcases primitive_root.of_mul_primitive (hTprim _ ht₂') with ⟨_, rfl | rfl⟩; simp,
end

/-- Convenient names for the two variables in an xy_poly -/
def X : polyℤ := mv_polynomial.X 0
def Y : polyℤ := mv_polynomial.X 1

section reduced

variable S : finset (ℤ × ℤ)
variable hSprim : ∀ s ∈ S, primitive_root s
variable hSmul : ∀ s₁ s₂ ∈ S, (∃ n : ℤ, s₂ = n • s₁) → s₂ = s₁

def l (p : ℤ × ℤ) : polyℤ := C p.2 * X - C p.1 * Y
def g (p : ℤ × ℤ) : polyℤ := ∏ s in S.erase p, l s

lemma l_eval (p q : ℤ × ℤ) : eval (to_val q) (l p) = p.2 * q.1 - p.1 * q.2 :=
begin
	unfold l, simp [eval_monomial],
	congr; { simp [X, Y], refl },
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

lemma g_is_homogeneous {s : ℤ × ℤ} : s ∈ S → is_homogeneous (g S s) (S.card - 1) :=
begin
	intro hs,
	rw [← nat.pred_eq_sub_one, ← card_erase_of_mem hs],
	unfold g,
	convert is_homogeneous.prod (S.erase s) (λ s, l s) (λ _, 1) (λ s _, l_is_homogeneous s),
	simp,
end

lemma exists_eval_one {p : ℤ × ℤ} (h : primitive_root p) :
	∃ φ : polyℤ, is_homogeneous φ 1 ∧ eval (to_val p) φ = 1 :=
begin
	rcases exists_mul_eq_gcd p.1 p.2 with ⟨a, b, hab⟩,
	unfold primitive_root at h, simp [h] at hab,
	use C a * X + C b * Y, split, swap,
	{ simp [eval_monomial],
		rw [mul_comm a, mul_comm b, ← hab],
		congr; { unfold X Y, simp, refl } },
	apply is_homogeneous.add;
	{ unfold X Y mv_polynomial.X,
		rw C_mul_monomial,
		apply is_homogeneous_monomial,
		rw [finsupp.support_single_ne_zero (nat.one_ne_zero), sum_singleton], simp },
end

include hSprim hSmul
lemma l_zero_iff {s t : ℤ × ℤ} (hs : s ∈ S) (ht : t ∈ S) : eval (to_val t) (l s) = 0 ↔ t = s :=
begin
	split, swap,
	{ rintro rfl, rw [l_eval], ring },
	intro heval,
	rw [l_eval, sub_eq_zero] at heval,
	rcases mul_of_coprime_mul (hSprim s hs) heval.symm with ⟨n, h2, h1⟩,
	apply hSmul s t hs ht,
	use n,
	rw prod.eq_iff_fst_eq_snd_eq, simp, use [h1, h2],
end

lemma g_zero_iff {s t : ℤ × ℤ} (hs : s ∈ S) (ht : t ∈ S) : eval (to_val t) (g S s) = 0 ↔ t ≠ s :=
begin
	unfold g,
	rw [eval_prod, prod_eq_zero_iff],
	split,
	{	rintro ⟨t', ht', heval⟩ rfl,
		rw l_zero_iff S hSprim hSmul (mem_of_mem_erase ht') ht at heval,
		rw heval at ht', exact not_mem_erase t' S ht' },
	intro hts,
	use [t, mem_erase_of_ne_of_mem hts ht],
	rw l_zero_iff S hSprim hSmul ht ht,
end

lemma exists_degree_ge {s : ℤ × ℤ} (hs : s ∈ S) {n : ℕ} (hn : S.card - 1 ≤ n) :
	∃ φ : polyℤ, φ.is_homogeneous n ∧ ∀ t ∈ S, eval (to_val t) φ = 0 ↔ t ≠ s :=
begin
	rcases exists_eval_one (hSprim s hs) with ⟨ψ, hψhom, hψeval⟩,
	use ψ ^ (n - (S.card - 1)) * g S s,
	split,
	{	convert @is_homogeneous.mul _ _ _ _ _ (n - (S.card - 1)) (S.card - 1) _ (g_is_homogeneous S hs),
		{ rw nat.sub_add_cancel hn },
		conv { congr, skip, rw ← nat.one_mul (n - _)},
		apply is_homogeneous.pow hψhom },
	intros t ht,
	rw [eval_mul, mul_eq_zero, g_zero_iff S hSprim hSmul hs ht],
	split, swap,
	{	intro h, right, exact h },
	rintros h rfl, cases h with h1 h2, swap,
	{	contradiction },
	rw [eval_pow, hψeval, one_pow] at h1,
	norm_num at h1,
end
omit hSprim hSmul

local notation `ϕ` := nat.totient

theorem exists_homogeneous_one_at_coprime_of_prime_power {p k : ℕ} (hp : p.prime) :
	∃ n (φ : polyℤ), 0 < n ∧ φ.is_homogeneous n ∧
	(∀ t, primitive_root t → eval (to_val t) φ ≡ 1 [ZMOD ↑(p ^ k)]) :=
begin
	rcases nat.prime.eq_two_or_odd hp with rfl | hodd,
	{	have two_pos : 0 < 2 := by norm_num,
    use [2 * ϕ (2 ^ k), (X ^ 2 + X * Y + Y ^ 2) ^ (ϕ (2 ^ k))], split,
		{ exact nat.mul_pos two_pos (nat.totient_pos $ pow_pos two_pos k) }, split,
		{ have hhom : (X ^ 2 + X * Y + Y ^ 2).is_homogeneous 2,
			{ rw [pow_two, pow_two],
        repeat { apply is_homogeneous.add };
        { apply is_homogeneous.mul; { unfold X Y, apply is_homogeneous_X } } },
      apply is_homogeneous.pow hhom },
    intros t ht,
    rw eval_pow,
    apply modeq.pow_totient,
    conv { congr, simp [X, Y], change t.1 ^ 2 + t.1 * t.2 + t.2 ^ 2, skip, simp },
    apply is_coprime.pow_right,
    rcases @modeq.exists_unique_equiv t.1 2 (by norm_num) with ⟨x, hx1, hx2, hx⟩,
    rcases @modeq.exists_unique_equiv t.2 2 (by norm_num) with ⟨y, hy1, hy2, hy⟩,
    interval_cases x,
    { interval_cases y,
      { have := int.dvd_gcd (modeq.modeq_zero_iff.mp hx.symm) (modeq.modeq_zero_iff.mp hy.symm),
        unfold primitive_root at ht, simp [ht] at this,
        cases dvd_one this; linarith },
			change is_coprime _ ↑2,
			rw int.is_coprime_prime nat.prime_two,
			intro hdvd,
			rw ← modeq.modeq_zero_iff at hdvd,
			change _ ≡ _ [ZMOD ↑2] at hx,
			change _ ≡ _ [ZMOD ↑2] at hy,
			rw ← zmod.int_coe_eq_int_coe_iff at *,
			simp [← hx, ← hy, zero_pow] at hdvd,
			exact hdvd },
		interval_cases y,
		{	change is_coprime _ ↑2,
			rw int.is_coprime_prime nat.prime_two,
			intro hdvd,
			rw ← modeq.modeq_zero_iff at hdvd,
			change _ ≡ _ [ZMOD ↑2] at hx,
			change _ ≡ _ [ZMOD ↑2] at hy,
			rw ← zmod.int_coe_eq_int_coe_iff at *,
			simp [← hx, ← hy, zero_pow] at hdvd,
			exact hdvd },
		change is_coprime _ ↑2,
		rw int.is_coprime_prime nat.prime_two,
		intro hdvd,
		rw ← modeq.modeq_zero_iff at hdvd,
		change _ ≡ _ [ZMOD ↑2] at hx,
		change _ ≡ _ [ZMOD ↑2] at hy,
		rw ← zmod.int_coe_eq_int_coe_iff at *,
		simp [← hx, ← hy] at hdvd,
		have : (1 : zmod 2) + 1 = 0 := by ring,
		simp [this] at hdvd,
		exact hdvd },
	have p_gt_two : 2 < p,
	{ by_contradiction h,
		have := le_of_not_gt h,
		interval_cases p,
		{ exact nat.not_prime_zero hp },
		{ exact nat.not_prime_one hp },
		simp at hodd, exact hodd },
	use [(p - 1) * ϕ (p ^ k), (X ^ (p - 1) + Y ^ (p - 1)) ^ (ϕ (p ^ k))], split,
	{ apply mul_pos (lt_trans nat.zero_lt_one _) (nat.totient_pos $ pow_pos _ _),
		{ rw ← nat.pred_eq_sub_one, change nat.pred 2 < p.pred,
			apply nat.pred_lt_pred _ p_gt_two, norm_num },
		exact lt_trans (by norm_num) p_gt_two }, split,
	{ apply is_homogeneous.pow (is_homogeneous.add _ _);
		{ conv { congr, skip, rw ← nat.one_mul (p - 1) },
			apply is_homogeneous.pow, unfold X Y, apply is_homogeneous_X } },
	intros t ht,
	rw eval_pow,
	apply modeq.pow_totient,
	conv { congr, simp [X, Y], change t.1 ^ (p - 1) + t.2 ^ (p - 1), skip, simp },
	apply is_coprime.pow_right,
	rw is_coprime_prime hp,
	rw [← modeq.modeq_zero_iff, ← nat.totient_prime hp],
	by_cases hx : ↑p ∣ t.1,
	{ by_cases hy : ↑p ∣ t.2,
		{	exfalso, apply nat.prime.not_dvd_one hp (coe_nat_dvd.mp _),
			unfold primitive_root at ht, rw ← ht,
			apply int.dvd_gcd hx hy },
		have : t.1 ^ p.totient ≡ 0 [ZMOD p] := modeq.modeq_zero_iff.mpr (dvd_pow hx $
			ne_of_gt (nat.totient_pos $ lt_trans (by norm_num) p_gt_two)),
		simp [← zmod.int_coe_eq_int_coe_iff] at *,
		rw [this, zero_add, ← cast_pow, ← cast_zero, zmod.int_coe_eq_int_coe_iff],
		have h1 : t.2 ^ p.totient ≡ 1 [ZMOD p] := modeq.pow_totient ((is_coprime_prime hp).mpr hy),
		intro h0,
		apply nat.prime.not_dvd_one hp,
		simp [← coe_nat_dvd, ← modeq.modeq_zero_iff],
		exact modeq.trans h1.symm h0 },
	have hx1 : t.1 ^ p.totient ≡ 1 [ZMOD p] := modeq.pow_totient ((is_coprime_prime hp).mpr hx),
	by_cases hy : ↑p ∣ t.2,
	{ have : t.2 ^ p.totient ≡ 0 [ZMOD p] := modeq.modeq_zero_iff.mpr (dvd_pow hy $
			ne_of_gt (nat.totient_pos $ lt_trans (by norm_num) p_gt_two)),
		simp [← zmod.int_coe_eq_int_coe_iff] at this,
		simp [← zmod.int_coe_eq_int_coe_iff],
		rw [this, add_zero, ← cast_pow, ← cast_zero, zmod.int_coe_eq_int_coe_iff],
		intro h0,
		apply nat.prime.not_dvd_one hp,
		simp [← coe_nat_dvd, ← modeq.modeq_zero_iff],
		exact modeq.trans hx1.symm h0 },
	have hy1 : t.2 ^ p.totient ≡ 1 [ZMOD p] := modeq.pow_totient ((is_coprime_prime hp).mpr hy),
	simp [← zmod.int_coe_eq_int_coe_iff] at *,
	simp [hx1, hy1],
	convert_to ¬ (↑2 : zmod p) = ↑0, { simp, ring },
	rw zmod.eq_iff_modeq_nat,
	apply (nat.modeq.not_modeq_lt_iff p_gt_two (nat.prime.pos hp)).mpr,
	norm_num,
end

#check is_homogeneous.add
#check nat.prime.pos
#check nat.totient_prime
#check ne_

end reduced
