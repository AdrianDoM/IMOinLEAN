/-
Collection of nat.sqrt lemmas
Author: Adrián Doña Mateo

These were contributed to mathlib in
[#5155](https://github.com/leanprover-community/mathlib/pull/5155/).

An apostrophe was added at the end of the names to avoid clashes.
-/

import data.nat.sqrt

-- These lemmas were added to src/data/nat/sqrt.lean.
namespace nat

theorem sqrt_mul_sqrt_lt_succ' (n : ℕ) : sqrt n * sqrt n < n + 1 :=
lt_succ_iff.mpr (sqrt_le _)

theorem succ_le_succ_sqrt' (n : ℕ) : n + 1 ≤ (sqrt n + 1) * (sqrt n + 1) :=
le_of_pred_lt (lt_succ_sqrt _)

/-- There are no perfect squares strictly between m² and (m+1)² -/
theorem not_exists_sq' {n m : ℕ} (hl : m * m < n) (hr : n < (m + 1) * (m + 1)) :
  ¬ ∃ t, t * t = n :=
begin
  rintro ⟨t, rfl⟩,
  have h1 : m < t, from nat.mul_self_lt_mul_self_iff.mpr hl,
  have h2 : t < m + 1, from nat.mul_self_lt_mul_self_iff.mpr hr,
  exact (not_lt_of_ge $ le_of_lt_succ h2) h1
end

end nat