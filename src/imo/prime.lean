import data.nat.prime
import data.nat.totient
import data.list.basic
import data.nat.gcd
import .list

namespace nat

open finset

theorem totient_prime {p : ℕ} (hp : p.prime) : p.totient = p - 1 :=
begin
	unfold totient,
	have hcoprime : ∀ x ∈ (range p).erase 0, p.coprime x,
	{ intros x hx, rw prime.coprime_iff_not_dvd hp,
		apply not_dvd_of_pos_of_lt (nat.pos_of_ne_zero $ ne_of_mem_erase hx),
		apply mem_range.mp (mem_of_mem_erase hx) },
	have hunion : range p = {0} ∪ (range p).erase 0,
	{	rw [← insert_eq, insert_erase], simp, exact prime.pos hp },
	rw [hunion, filter_union, filter_false_of_mem], swap,
	{	intros x hx, simp at hx, simp [hx], intro h1, exact not_prime_one (h1 ▸ hp) },
	rw [filter_true_of_mem hcoprime, empty_union, card_erase_of_mem, card_range],
	{ rw pred_eq_sub_one },
	simp [prime.pos hp],
end

theorem factors_ne_nil {n : ℕ} (hn : 1 < n) : n.factors ≠ list.nil :=
begin
	induction n with n ih,
	{	exfalso, exact (not_lt_of_gt nat.zero_lt_one) hn },
	induction n with n ih,
	{ exfalso, exact (lt_irrefl 1) hn },
	rw factors_add_two,
	intro h, injection h,
end

theorem pow_count_factors_dvd (n k : ℕ) : k ^ list.count k n.factors ∣ n :=
begin
	by_cases h0 : n = 0, { simp [h0] },
	conv { congr, skip, rw ← prod_factors (nat.pos_of_ne_zero h0) },
	apply list.pow_count_dvd_prod,
end

theorem pow_gt_count_factors_not_dvd {n p : ℕ} (hn : 0 < n) (hp : p.prime) :
  ∀ k, list.count p n.factors < k → ¬ p ^ k ∣ n :=
begin
	have aux : ∀ l, (∀ x : ℕ, x ∈ l → x.prime) → ∀ p : ℕ, p.prime →
		∀ k, list.count p l < k → ¬ p ^ k ∣ l.prod,
	{	intros l hl p hp,
		induction l with hd tl ih,
		{ intros k hk hdvd,
			rw [list.count_nil] at hk,
			rw [list.prod_nil, nat.dvd_one] at hdvd,
			have := pow_lt_pow (prime.one_lt hp) hk,
			rw [hdvd, pow_zero] at this,
			exact (lt_irrefl 1) this },
		intros k hk hdvd,
		have hkpos : 0 < k := lt_of_le_of_lt (zero_le _) hk,
		rw [list.count_cons] at hk,	split_ifs at hk,
		{ rw [← h, list.prod_cons, ← succ_pred_eq_of_pos hkpos, pow_succ] at hdvd,
			cases hdvd with w hw,
			rw [mul_assoc, mul_eq_mul_left_iff] at hw,
			cases hw with h1 h2, swap, { exact (prime.ne_zero hp) h2 },
			apply ih (λ x hx, hl x (by simp [hx])) k.pred (lt_pred_iff.mpr hk),
			use [w, h1] },
		rw [list.prod_cons] at hdvd,
		apply ih (λ x hx, hl x (by simp [hx])) k hk,
		apply coprime.dvd_of_dvd_mul_left _ hdvd,
		rw [← pow_one hd], apply coprime.pow,
		rwa coprime_primes hp (hl hd (by simp)) },
	have prod := prod_factors hn,
	conv in (¬ _ ∣ n) { rw ← prod },
	apply aux n.factors (λ x, mem_factors) p hp,
end

theorem mem_factors_dvd {n : ℕ} : ∀ p ∈ n.factors, p ∣ n :=
λ p hp, decidable.by_cases
	(by { intro hn, exfalso, simp [hn, factors] at hp, assumption })
	(λ hn, (mem_factors_iff_dvd (nat.pos_of_ne_zero hn) (mem_factors hp)).mp hp)

lemma list_pos_prod_pos {l : list ℕ} (hpos : ∀ x ∈ l, 0 < x) : 0 < l.prod :=
begin
	induction l with hd tl ih, { simp },
	simp, apply mul_pos,
	{	apply hpos, simp },
	apply ih, intros x hx, apply hpos, simp, right, exact hx,
end

lemma list_pos_prod_ge_sublist_prod {s t : list ℕ} (hpos : ∀ x ∈ s, 0 < x) (h : t <+ s) :
	t.prod ≤ s.prod :=
begin
	induction s with hd tl ih generalizing t,
	{	simp [list.eq_nil_of_sublist_nil h] },
	induction t with hd' tl' ih',
	{	have := succ_le_of_lt (list_pos_prod_pos hpos), simpa },
	have htlpos : ∀ x ∈ tl, 0 < x := λ x hx, by { apply hpos x, simp, right, exact hx },
	by_cases heq : hd = hd',
	{	simp [heq], apply nat.mul_le_mul_of_nonneg_left, apply ih htlpos,
		rw heq at h, apply list.sublist_of_cons_sublist_cons, exact h },
	have : hd' :: tl' <+ tl := list.cons_sublist_of_cons_sublist_cons (ne.symm heq) h,
	have := ih htlpos this,
	apply le_trans this,
	rw [← nat.one_mul tl.prod, list.prod_cons],
	have := succ_le_of_lt (hpos hd (by simp)),
	apply nat.mul_le_mul_of_nonneg_right, assumption,
end

theorem div_factor_ne_zero (n : ℕ) : ∀ p ∈ n.factors, n / p ^ list.count p n.factors ≠ 0 :=
begin
	by_cases h0 : n = 0,
	{	intros p hmem, exfalso, simp [h0, factors] at hmem, exact hmem },
	have hpos : 0 < n := nat.pos_of_ne_zero h0,
	have hfactorspos : ∀ x ∈ n.factors, 0 < x := λ x hx, prime.pos (mem_factors hx),
	intros p hmem h0,
	rw nat.div_eq_zero_iff at h0, swap,
	{	apply nat.pos_of_ne_zero, apply pow_ne_zero,
		intro h, apply not_prime_zero, rw ← h, exact mem_factors hmem },
	have hleft := prod_factors hpos,
	have hright : p ^ list.count p n.factors = (list.repeat p $ list.count p n.factors).prod := by simp,
	conv at h0 {congr, rw ← hleft, skip, rw hright },
	apply not_lt_of_ge (list_pos_prod_ge_sublist_prod hfactorspos _) h0,
	rw ← list.le_count_iff_repeat_sublist,
end

end nat