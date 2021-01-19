/-
Author: Adrián Doña Mateo.
-/

import imo2017_q6
import data.multiset.basic
import bezout

open mv_polynomial (hiding X) int (hiding range gcd) finset (hiding gcd) euclidean_domain
open_locale big_operators

local notation `polyℤ` := mv_polynomial (fin 2) ℤ
local notation `ϕ` := nat.totient

def homogeneous_one_at_coprime {a : ℕ} (ha : 0 < a) :
	{ φn : polyℤ × ℕ // 0 < φn.2 ∧ φn.1.is_homogeneous φn.2 ∧
	∀ t, primitive_root t → eval (to_val t) φn.1 ≡ 1 [ZMOD a] } :=
begin
	apply classical.subtype_of_exists,
	by_cases ha1 : a ≤ 1,
	{	sorry /- copy from below -/ },
	let factors := nat.factors a,
	let primes : list (ℕ × ℕ) := factors.erase_dup.map (λ p, ⟨p, list.count p factors⟩),
	have hprimes : ∀ pk : ℕ × ℕ, pk ∈ primes → nat.prime pk.1,
	{ sorry /- copy from below -/ },
	let removepowers : list ℤ := primes.map (λ pk, a / pk.1 ^ pk.2),
	have hcoprime : (removepowers.foldl euclidean_domain.gcd 0).nat_abs = 1,
	{	sorry /- copy from below -/	},
	let bezout := abs_bezout_factors removepowers,
	let bezout_p : list polyℤ := bezout.map (λ a, C a),
	let φs : list (polyℤ × ℕ) :=
		primes.pmap (λ pk hp, homogeneous_one_at_coprime_of_prime_power pk.1 pk.2 hp) hprimes,
	let K : ℕ := list.foldr nat.lcm 1 (φs.map prod.snd),
	let ψs : list polyℤ := φs.map (λ φn, φn.1 ^ (K / φn.2)),
	use [list.sum (list.zip_with (*) bezout_p ψs), K], split,
	{ sorry /- copy from below -/ }, split,
	{ sorry /- copy from below -/ },
	sorry /- probably going to need more eval lemmas for sums with lists -/
end

#print sigma
#eval (nat.factors 100).erase_dup
#eval (-10 : ℤ) % 1
#eval int.lcm 1 37


/-
	by_cases ha1 : a ≤ 1,
	{	have : a = 1 := by linarith, rw this at *,
		use [⟨X + Y, 1⟩, by simp], split,
		{	apply is_homogeneous.add; { unfold X Y, apply is_homogeneous_X } },
		intros t ht, unfold int.modeq, simp },

	have hprimes : ∀ {pk : ℕ × ℕ}, pk ∈ primes → nat.prime pk.1,
	{ rintro ⟨p, k⟩ hpk, simp,
		simp [primes, list.mem_map] at hpk,
		rcases hpk with ⟨a, ha, rfl, _⟩,
		exact nat.mem_factors ha },

	have hcoprime : (removepowers.foldl euclidean_domain.gcd 0).nat_abs = 1,
	{	by_contradiction h,
		cases list.exists_mem_of_ne_nil (nat.factors_ne_nil $ lt_of_not_ge ha1) with p hmem,
		have h1 : 1 < (removepowers.foldl euclidean_domain.gcd 0).nat_abs,
		{	by_contradiction hn1, have := le_of_not_gt hn1,
			interval_cases (list.foldl euclidean_domain.gcd 0 removepowers).nat_abs, swap,
			{	exact h h_1 },
			rw [nat_abs_eq_zero, list_gcd_eq_zero] at h_1,
			simp [removepowers, primes, factors] at h_1,
			apply nat.div_factor_ne_zero a p hmem,
			apply_mod_cast h_1 p hmem },
		have hdvdr : ∀ x ∈ removepowers, ↑((list.foldl euclidean_domain.gcd 0 removepowers).nat_abs) ∣ x,
		{	intros x hx, rw nat_abs_dvd, apply list_gcd_dvd _ _ hx },
		have hdvdra : ∀ x ∈ removepowers, x ∣ ↑a,
		{ intros x hx, simp [removepowers, primes, factors] at hx, 
			rcases hx with ⟨p, hp, hx⟩,
			use p ^ list.count p a.factors,
			rw [← hx, int.div_mul_cancel _],
			norm_cast, apply nat.pow_count_factors_dvd },
		have hdvd : ((list.foldl euclidean_domain.gcd 0 removepowers).nat_abs : ℤ) ∣ a,
		{ cases @list.exists_mem_of_ne_nil _ removepowers _ with x hx, swap,
			{ simp [removepowers, primes, factors, nat.factors_ne_nil (lt_of_not_ge ha1)] },
			apply dvd.trans (hdvdr x hx) (hdvdra x hx) },
		norm_cast at hdvd,
		cases list.exists_mem_of_ne_nil (nat.factors_ne_nil $ h1) with p hp,
		have hpa := (nat.mem_factors_iff_dvd ha (nat.mem_factors hp)).mpr
			(dvd.trans (nat.mem_factors_dvd p hp) hdvd),
		have hpr : ↑a / ↑p ^ list.count p a.factors ∈ removepowers,
		{ simp [removepowers, primes, factors], 
			use [p, hpa], },
		apply nat.pow_gt_count_factors_not_dvd ha (nat.mem_factors hp)
			(list.count p a.factors).succ (nat.lt_succ_self _),
		have hpp : (p : ℤ) ∣ ↑a / ↑p ^ list.count p a.factors,
		{	apply dvd.trans _ (hdvdr _ hpr),
			norm_cast, apply nat.mem_factors_dvd _ hp },
		cases hpp with u hu,
		rw ← coe_nat_dvd,
		use u,
		rw [pow_succ, nat.mul_comm, int.coe_nat_mul, mul_assoc, ← hu, mul_comm],
		norm_cast,
		rw [nat.div_mul_cancel (nat.pow_count_factors_dvd _ _)] },

	{ -- Show that 0 < n
		apply list_lcm_pos, intros n hn,
		simp at hn, rcases hn with ⟨φ, p, k, hpk, hφn⟩,
		rcases subtype.coe_eq_iff.mp hφn with ⟨⟨hpos, _⟩, _⟩,
		exact hpos }, split,

	{ -- Show that the constructed polynomial is homogeneous		
		dsimp,
		convert is_homogeneous.zip_with_mul_sum_homogeneous bezout_p ψs 0 K _ _, { simp },
		{	intros φ hφ, rw [list.mem_map] at hφ,
			rcases hφ with ⟨a, _, rfl⟩,
			apply is_homogeneous_C },
		intros φ' hφ', simp [ψs, φs] at hφ',
		rcases hφ' with ⟨φ, n, ⟨p, k, hpk, hφ⟩, rfl⟩,
		rcases subtype.coe_eq_iff.mp hφ with ⟨⟨_, hhom, _⟩, _⟩,
		convert @is_homogeneous.pow _ _ _ φ n hhom _,
		rw [nat.mul_comm, nat.div_mul_cancel _],
		convert list_dvd_lcm _ n _,
		simp only [list.mem_pmap, list.mem_map, exists_eq_right, prod.exists],
		use [φ, p, k, hpk, hφ] },
-/
