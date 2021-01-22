/-
Author: Adrián Doña Mateo.
-/

import imo2017_q6
import multiset

open mv_polynomial (hiding X) int (hiding range gcd lcm) multiset
open_locale big_operators

local notation `polyℤ` := mv_polynomial (fin 2) ℤ
local notation `ϕ` := nat.totient


def solution (S : finset (ℤ × ℤ)) (hS : ∀ t ∈ S, primitive_root t) :
	{ φn : polyℤ × ℕ // 0 < φn.2 ∧ φn.1.is_homogeneous φn.2 ∧ 
		∀ t ∈ S, eval (to_val t) φn.1 = 1 } :=
begin
	rcases minimal_primitive_root_set hS with ⟨T, hTS, hT, hTind, hTspan⟩,
	apply solution_of_minimal_set_solution hS hTspan,
	let a := (T.val.map (λ t, eval (to_val t) (g T t))).lcm.nat_abs,
	have ha : ∀ t ∈ T, eval (to_val t) (g T t) ∣ a :=
		λ t ht, dvd_nat_abs.mpr (dvd_lcm $ mem_map.mpr ⟨t, finset.mem_def.mp ht, rfl⟩),
	-- ψn.val.1 is a homogeneous polynomial that evaluates to 1 [ZMOD a] at any primitive root
	let ψm := @homogeneous_one_at_coprime a _, swap,
	{	apply nat_abs_pos_of_ne_zero, rw lcm_ne_zero_iff,
		intros x hx hg, rw mem_map at hx,
		rcases hx with ⟨y, hy, rfl⟩,
		rw g_zero_iff T hT hTind hy hy at hg, exact hg (eq.refl y) },
	let k := T.card / ψm.val.2 + 1,
	have hk : ψm.val.2 * k ≥ T.card - 1,
	{	apply nat.le_of_lt (nat.lt_of_le_of_lt (nat.pred_le T.card) _), rw mul_comm,
		exact nat.lt_mul_of_div_lt (nat.lt_succ_self _) ψm.property.1, },
	-- we construct our polynomial by subtracting the appropriate multiples of the g's from ψn.1
	-- ψn.1 - map
	use ψm.val.1 ^ k +
		(T.val.pmap
			(λ t ht, C ((eval (to_val t) (ψm.val.1 ^ k) - 1) / eval (to_val t) (g T t)) * (@g_degree_ge T hT hTind t ht _ hk).val)
			(λ _ x, x)).sum,
	use ψm.val.2 * k, split,
	{	exact nat.mul_pos ψm.property.1 (nat.succ_pos _) }, split,
	{ apply is_homogeneous.add (is_homogeneous.pow ψm.property.2.1 _),
		apply is_homogeneous.multiset_sum, intros φ hφ,
		rcases mem_pmap.mp hφ with ⟨t, ht, rfl⟩,
		convert is_homogeneous.mul
			(is_homogeneous_C _ _)
			(@g_degree_ge T hT hTind t ht _ hk).property.1,
		rw zero_add },
	intros t ht, rw [eval_add, eval_multiset_sum, map_pmap],
	simp only [eval_mul, eval_C],
	conv in (T.val) { rw ← cons_erase (finset.mem_def.mp ht) },
	rw [pmap_cons, sum_cons, ← add_assoc],
end

#check pmap
#check finset.mem_def