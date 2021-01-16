/-
Author: Adrián Doña Mateo.
-/

import imo2017_q6
import data.multiset.basic

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
	have hcoprime : removepowers.foldl euclidean_domain.gcd 0 = 1,
	{	simp [removepowers, primes],
		by_contradiction h,
		}
end

#print sigma
#eval (nat.factors 100).erase_dup
#eval (-10 : ℤ) % 1


