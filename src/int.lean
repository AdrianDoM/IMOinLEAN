import data.int.basic

namespace int

theorem dvd_one {n : ℤ} (h : n ∣ 1) : n = 1 ∨ n = -1 :=
begin
	by_cases hn : 0 ≤ n,
	{	left, exact eq_one_of_dvd_one hn h },
	right, 
	rw ← neg_dvd at h,
	rw eq_neg_iff_eq_neg, symmetry,
	exact eq_one_of_dvd_one (neg_nonneg.mpr $ le_of_not_ge hn) h,
end

end int