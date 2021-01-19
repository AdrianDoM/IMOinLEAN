import data.list.basic
import data.list.erase_dup
import data.nat.gcd
import algebra.euclidean_domain
import nat

namespace list

variable {α : Type*}

lemma exists_mem_of_ne_nil {l : list α} (h : l ≠ nil) : ∃ a, a ∈ l :=
begin
	rcases exists_cons_of_ne_nil h with ⟨a, tl, rfl⟩,
	use a, simp,
end

lemma cons_sublist_of_cons_sublist_cons {s t : list α} {a b : α} (h : a ≠ b) :
	a :: s <+ b :: t → a :: s <+ t :=
begin
	intro hsub,	cases hsub,
	{	assumption },
	contradiction,
end

lemma pow_count_dvd_prod [comm_monoid α] [decidable_eq α] (l : list α) (a : α) :
	a ^ count a l ∣ l.prod :=
begin
	induction l with hd tl ih, { simp },
	simp [count_cons],
	split_ifs,
	{	rw [← h, pow_succ], apply mul_dvd_mul_left a ih },
	apply dvd.trans ih, apply dvd_mul_left,
end

/- data/list/erase_dup.lean -/

@[simp]
theorem erase_dup_eq_nil [decidable_eq α] {l : list α} :
	l.erase_dup = [] ↔ l = [] :=
begin
	split,
	{	intro h1, by_contradiction h2,
		cases exists_mem_of_ne_nil h2 with x hx,
		rw eq_nil_iff_forall_not_mem at h1,
		apply h1 x, rwa mem_erase_dup },
	intro h, simp [h],
end

lemma erase_dup_ne_nil [decidable_eq α] {l : list α} :
	l ≠ nil ↔ l.erase_dup ≠ nil :=
not_iff_not.mpr erase_dup_eq_nil.symm

end list

lemma list_gcd_eq_zero {l : list ℤ} :
	l.foldr euclidean_domain.gcd 0 = 0 ↔ ∀ n ∈ l, n = (0 : ℤ) :=
begin
	split,
	{	intro h, induction l with hd tl ih, { simp },
		intros n hn, rw list.mem_cons_iff at hn,
		rw [list.foldr_cons, euclidean_domain.gcd_eq_zero_iff] at h,
		cases hn with h1 h2,
		{	rw [h1, h.1] },
		exact ih h.2 n h2 },
	intro h, induction l with hd tl ih,	{ simp },
	rw [list.foldr_cons, euclidean_domain.gcd_eq_zero_iff],
	exact ⟨h hd (by simp), ih (λ n hn, h n (by simp [hn]))⟩,
end

lemma list_gcd_dvd {l : list ℤ} (a : ℤ):
	∀ x ∈ l, l.foldr euclidean_domain.gcd a ∣ x :=
begin
	induction l with hd tl ih generalizing a, { simp },
	intros x hx, rw list.mem_cons_iff at hx,
	rw list.foldr_cons,
	rcases hx with rfl | hxtl,
	{ apply euclidean_domain.gcd_dvd_left },
	apply dvd.trans (euclidean_domain.gcd_dvd_right _ _) (ih a x hxtl),
end

lemma list_dvd_lcm (l : list ℕ) : ∀ x ∈ l, x ∣ l.foldr nat.lcm 1 :=
begin
	induction l with hd tl ih, { simp },
	intros x hx, rw list.foldr_cons,
	rw list.mem_cons_iff at hx,
	rcases hx with rfl | hx,
	{	apply nat.dvd_lcm_left },
	apply dvd.trans (ih _ hx),
	apply nat.dvd_lcm_right, 
end

lemma list_lcm_pos {l : list ℕ} : (∀ x ∈ l, 0 < x) → 0 < l.foldr nat.lcm 1 :=
begin
	induction l with hd tl ih, { simp },
	intro h, rw list.foldr_cons,
	apply nat.pos_of_ne_zero (λ h0, _),
	rw nat.lcm_eq_zero_iff at h0,
	cases h0,
	{	exact ne_of_lt (h hd (by simp)) h0.symm },
	apply ne_of_lt (ih _) h0.symm,
	intros x hx, exact h x (by simp [hx]),
end

#check not_iff