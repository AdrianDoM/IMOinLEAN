/-
Collection of casts from int and nat into pnat
Author: Adrián Doña Mateo
-/

import data.pnat.basic
import tactic

local attribute [instance] classical.prop_decidable
noncomputable theory

namespace pnat

def from_int {x : ℤ} (h : 0 < x) : ∃ n : ℕ+, x = n :=
begin
	cases int.eq_coe_of_zero_le (le_of_lt h) with n hn,
	rw hn at h, norm_cast at h,
	use ⟨n, h⟩, assumption,
end

end pnat