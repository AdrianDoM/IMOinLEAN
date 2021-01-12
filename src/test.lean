/-
Author: Adrián Doña Mateo.
-/

import imo2017_q6

open mv_polynomial (hiding X) int (hiding range) finset
open_locale big_operators

local notation `polyℤ` := mv_polynomial (fin 2) ℤ
local notation `ϕ` := nat.totient

theorem exists_homogeneous_one_at_coprime {a : ℕ} (ha : 0 < a) :
	∃ n (φ : polyℤ), 0 < n ∧ φ.is_homogeneous n ∧
	∀ t, primitive_root t → eval (to_val t) φ ≡ 1 [ZMOD a] :=
begin
	let factors := unique_factorization_monoid.factors a,
	
end


