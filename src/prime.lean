import data.nat.prime
import data.nat.totient

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

end nat