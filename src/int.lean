import data.int.gcd
import tactic

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

section gcd

theorem exists_mul_eq_gcd (a b : ℤ) : ∃ x y, a * x + b * y = gcd a b :=
begin
	have : ∃ x y : ℤ, ↑(nat_abs a) * x + ↑(nat_abs b) * y = gcd a b,
	{	use [nat.gcd_a (nat_abs a) (nat_abs b), nat.gcd_b (nat_abs a) (nat_abs b)],
		rw ← nat.gcd_eq_gcd_ab, congr },
	rcases this with ⟨x, y, hxy⟩,
	cases nat_abs_eq a with ha ha,
	{	rw ← ha at hxy,
		cases nat_abs_eq b with hb hb,
		{	rwa ← hb at hxy, use [x, y, hxy] },
		use [x, -y], conv_lhs { rw hb }, simpa },
	cases nat_abs_eq b with hb hb,
	{	use [-x, y], conv_lhs { rw [ha, hb] }, simpa },
	use [-x, -y], conv_lhs { rw [ha, hb] }, simpa,
end

theorem mul_of_coprime_mul {a b c d : ℤ} (hab : gcd a b = 1) (h : a * c = b * d) :
	∃ n, c = n * b ∧ d = n * a  :=
begin
	rcases exists_mul_eq_gcd a b with ⟨x, y, hxy⟩,
	simp [hab] at hxy,
	use d * x + c * y, split,
	{ calc c
	      = c * (a * x + b * y)   : by rw [hxy, mul_one]
		... = a * c * x + c * b * y : by ring
		... = b * d * x + c * b * y : by rw h
		... = (d * x + c * y) * b   : by ring },
	{ calc d
		    = d * (a * x + b * y)   : by rw [hxy, mul_one]
		... = d * a * x + b * d * y : by ring
		... = d * a * x + a * c * y : by rw ← h
		... = (d * x + c * y) * a   : by ring },
end

end gcd

end int