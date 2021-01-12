import data.int.gcd
import data.list.zip
open int euclidean_domain list

lemma zip_with_mul_map_mul_right {α : Type*} [comm_ring α] (l₁ l₂ : list α) (r : α) :
	zip_with (*) l₁ (l₂.map ((*) r)) = (zip_with (*) l₁ l₂).map ((*) r) :=
begin
	induction l₁ with x₁ tl₁ ih₁ generalizing l₂, { simp },
	induction l₂ with x₂ tl₂ ih₂, { simp },
	simp, split,
	{	rw mul_left_comm },
	exact ih₁ tl₂,
end

/- Given a list of integers x₁,...,xₙ, it produces a list of integers a₁,...,aₙ such that
x₁ * a₁ + ⋯ + xₙ * aₙ = gcd (x₁,...,xₙ). -/
def bezout_factors : list ℤ → list ℤ
| []        := []
| (x :: tl) := let g := tl.foldr gcd 0 in gcd_a x g :: (bezout_factors tl).map ((*) (gcd_b x g))

lemma bezout_eq_gcd (l : list ℤ) : (l.zip_with (*) (bezout_factors l)).sum = l.foldr gcd 0 :=
begin
	induction l with x tl ih,
	{	simp },
	simp [bezout_factors],
	rw [zip_with_mul_map_mul_right, sum_map_mul_left],
	change _ + _ * (map id _).sum = _,
	rw [map_id, ih, gcd_eq_gcd_ab, mul_comm (gcd_b _ _)],
end

#eval (zip_with (*) [20, 15, 12] (bezout_factors [20, 15, 12])).sum