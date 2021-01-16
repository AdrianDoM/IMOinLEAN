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

#eval (zip_with (*) [-20, -15, -12] (bezout_factors [-20, -15, -12])).sum

lemma int.eq_gcd_iff (a b : ℤ) (n : ℕ) :
	a.gcd b = n ↔ ↑n ∣ a ∧ ↑n ∣ b ∧ ∀ m, m ∣ a → m ∣ b → m ∣ ↑n :=
begin
	split,
	{	rintro rfl, use [gcd_dvd_left a b, gcd_dvd_right a b],
		intros m hma hmb, apply int.dvd_gcd hma hmb },
	rintro ⟨hna, hnb, hm⟩,
	apply nat.dvd_antisymm,
	{	rw ← int.coe_nat_dvd,
		apply hm, exact gcd_dvd_left a b, exact gcd_dvd_right a b },
	rw ← int.coe_nat_dvd,
	apply int.dvd_gcd hna hnb,
end

lemma int.gcd_add_mul_self (m n k : ℤ) : m.gcd (n + k * m) = m.gcd n :=
begin
	rw int.eq_gcd_iff,
	use gcd_dvd_left m n, split,
	{	apply dvd_add, exact gcd_dvd_right m n,
		apply dvd_mul_of_dvd_right, exact gcd_dvd_left m n },
	intros a ham han,
	apply int.dvd_gcd ham,
	have hakm : a ∣ k * m := dvd_mul_of_dvd_right ham k,
	rwa ← dvd_add_left hakm,
end

lemma int.gcd_mod (a b : ℤ) : int.gcd a b = int.gcd (b % a) a :=
by rw [gcd_comm _ a, int.mod_def, sub_eq_add_neg, neg_mul_eq_mul_neg,
	mul_comm a, int.gcd_add_mul_self]

lemma int.gcd_eq_abs_gcd (a b : ℤ) : int.gcd a b = (euclidean_domain.gcd a b).nat_abs :=
gcd.induction a b (λ x, by simp) (λ a b ha ih, by rw [gcd_val, ← ih, int.gcd_mod])