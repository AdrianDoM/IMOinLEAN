/-
Author: Adrián Doña Mateo.
-/

import imo2017_q6
import data.multiset.basic
import data.list.forall2
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
	{	have : a = 1 := by linarith, rw this at *,
		use [⟨X + Y, 1⟩, by simp], split,
		{	apply is_homogeneous.add; { unfold X Y, apply is_homogeneous_X } },
		intros t ht, unfold int.modeq, simp },
	let factors := nat.factors a,
	let primes : list (ℕ × ℕ) := factors.erase_dup.map (λ p, ⟨p, list.count p factors⟩),
	have hprimes : ∀ {pk : ℕ × ℕ}, pk ∈ primes → nat.prime pk.1,
	{ rintro ⟨p, k⟩ hpk, simp,
		simp [primes, list.mem_map] at hpk,
		rcases hpk with ⟨a, ha, rfl, _⟩,
		exact nat.mem_factors ha },
	let removepowers : list ℤ := primes.map (λ pk, a / pk.1 ^ pk.2),
	have hdvdra : ∀ x ∈ removepowers, x ∣ ↑a,
	{ intros x hx, simp [removepowers, primes, factors] at hx, 
		rcases hx with ⟨p, hp, hx⟩,
		use p ^ list.count p a.factors,
		rw [← hx, int.div_mul_cancel _],
		norm_cast, apply nat.pow_count_factors_dvd },	
	have hcoprime : (removepowers.foldr euclidean_domain.gcd 0).nat_abs = 1,
	{	by_contradiction h,
		cases list.exists_mem_of_ne_nil (nat.factors_ne_nil $ lt_of_not_ge ha1) with p hmem,
		have h1 : 1 < (removepowers.foldr euclidean_domain.gcd 0).nat_abs,
		{	by_contradiction hn1, have := le_of_not_gt hn1,
			interval_cases (list.foldr euclidean_domain.gcd 0 removepowers).nat_abs, swap,
			{	exact h h_1 },
			rw [nat_abs_eq_zero, list_gcd_eq_zero] at h_1,
			simp [removepowers, primes, factors] at h_1,
			apply nat.div_factor_ne_zero a p hmem,
			apply_mod_cast h_1 p hmem },
		have hdvdr : ∀ x ∈ removepowers, ↑((list.foldr euclidean_domain.gcd 0 removepowers).nat_abs) ∣ x,
		{	intros x hx, rw nat_abs_dvd, apply list_gcd_dvd _ _ hx },
		have hdvd : ((list.foldr euclidean_domain.gcd 0 removepowers).nat_abs : ℤ) ∣ a,
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
	let bezout := abs_bezout_factors removepowers,
	let φs : list (polyℤ × ℕ) :=
		primes.pmap (λ pk hp, homogeneous_one_at_coprime_of_prime_power pk.1 pk.2 hp) @hprimes,
	let K : ℕ := list.foldr nat.lcm 1 (φs.map prod.snd),
	let coeffs : list polyℤ := list.zip_with (*) (bezout.map C) (removepowers.map C),
	let ψs : list polyℤ := φs.map (λ φn, φn.1 ^ (K / φn.2)),
	use [(list.zip_with (*) coeffs ψs).sum, K], split,
	{ -- Show that 0 < n
		apply list_lcm_pos, intros n hn,
		simp at hn, rcases hn with ⟨φ, p, k, hpk, hφn⟩,
		rcases subtype.coe_eq_iff.mp hφn with ⟨⟨hpos, _⟩, _⟩,
		exact hpos }, split,
	{ -- Show that the constructed polynomial is homogeneous
		convert is_homogeneous.zip_with_mul_sum_homogeneous coeffs ψs 0 K _ _, { simp },
		{	intros xy hxy, dsimp [coeffs] at hxy,
			simp only [list.mem_iff_nth, list.nth_zip_with_eq_some] at hxy,
			rcases hxy with ⟨n, x, y, hx, hy, rfl⟩,
			rcases list.mem_map.mp (list.mem_iff_nth.mpr ⟨n, hx⟩) with ⟨_, _, rfl⟩,
			rcases list.mem_map.mp (list.mem_iff_nth.mpr ⟨n, hy⟩) with ⟨_, _, rfl⟩,
			rw [← nat.add_zero 0],
			apply is_homogeneous.mul; apply is_homogeneous_C },
		intros φ' hφ', simp [ψs, φs] at hφ',
		rcases hφ' with ⟨φ, n, ⟨p, k, hpk, hφ⟩, rfl⟩,
		rcases subtype.coe_eq_iff.mp hφ with ⟨⟨_, hhom, _⟩, _⟩,
		convert @is_homogeneous.pow _ _ _ φ n hhom _,
		rw [nat.mul_comm, nat.div_mul_cancel _],
		convert list_dvd_lcm _ n _,
		simp only [list.mem_pmap, list.mem_map, exists_eq_right, prod.exists],
		use [φ, p, k, hpk, hφ] },
	intros t ht, dsimp [coeffs],
	have hmod :
		((removepowers.zip_with (*) (ψs.map (eval (to_val t)))).map coe : list (zmod a)) =
		removepowers.map coe,
	{	rw [← list.forall₂_eq_eq_eq, list.forall₂_iff_zip], split, { simp },
		intros qψ q h, dsimp [removepowers, ψs, φs] at h,
		conv at h
		{ congr, skip, congr, congr, skip, congr, skip,
			rw [← list.pmap_eq_map (λ _, true) _ _ (λ _ _, trivial), list.pmap_eq_map_attach], skip,
			rw [list.map_map, list.pmap_eq_map_attach, list.map_map], skip, congr, skip,
			rw [← list.pmap_eq_map (λ _, true) _ _ (λ _ _, trivial), list.pmap_eq_map_attach] },
		rw [list.zip_with_map', list.map_map, list.map_map, list.zip_map'] at h,
		simp at h, rcases h with ⟨p, k, ⟨hpk, rfl⟩, rfl⟩,
		rw [← cast_pow, ← cast_mul, zmod.int_coe_eq_int_coe_iff],
		have hdvd : (p : ℤ) ^ k ∣ ↑a,
		{ simp at hpk, rcases hpk with ⟨p, hp, rfl, rfl⟩, norm_cast, apply nat.pow_count_factors_dvd },
		conv { congr, rw [← int.div_mul_cancel hdvd], skip, skip,
			rw ← int.mul_one (↑a / ↑p ^ k) },
		apply modeq.modeq_mul_left', { norm_cast, apply zero_le },
		apply modeq.pow_modeq_one,
		rcases (homogeneous_one_at_coprime_of_prime_power p k (hprimes hpk)).property with ⟨_, _, h⟩,
		convert h t ht, norm_cast	},
	rw [eval_list_sum, eval_zip_with_mul, eval_zip_with_mul, list.map_map, list.map_map],
	conv in (bezout.map _)
	{ change bezout.map (λ x, eval (to_val t) (C x)),
		simp only [eval_C], change bezout.map id, rw [list.map_id] },
	conv in (removepowers.map _)
	{ change removepowers.map (λ x, eval (to_val t) (C x)),
		simp only [eval_C], change removepowers.map id, rw [list.map_id] },
	rw [list.zip_with_assoc mul_assoc, ← zmod.int_coe_eq_int_coe_iff, ← coe_cast_ring_hom,
		ring_hom.map_list_sum, list.map_zip_with],
	simp only [ring_hom.map_mul],
	rw [← list.zip_with_map, coe_cast_ring_hom, hmod, ← coe_cast_ring_hom],
	simp only [← ring_hom.map_mul, list.zip_with_map, ← ring_hom.map_mul, ← list.map_zip_with],
	rw [← ring_hom.map_list_sum, list.zip_with_comm mul_comm],
	dsimp [bezout], rw [abs_bezout_eq_gcd], congr, rw [abs_eq_nat_abs, hcoprime, int.coe_nat_one],
end