import field_theory.finite.basic

namespace int

variables {n a b : ℤ} {m : ℕ}

namespace modeq

theorem modeq_pow (h : a ≡ b [ZMOD n]) : a ^ m ≡ b ^ m [ZMOD n] :=
begin
  induction m with m ih, {refl},
  rw [pow_succ, pow_succ],
  exact modeq_mul h ih,
end

theorem is_coprime_of_modeq (hcop : is_coprime a n) (hmodeq : a ≡ b [ZMOD n]) :
  is_coprime b n :=
begin
  cases modeq_iff_dvd.mp hmodeq with x hx,
  rw [sub_eq_iff_eq_add, add_comm] at hx,
  rwa [hx, is_coprime.add_mul_left_left_iff],
end

end modeq

theorem is_coprime_of_prime_not_dvd {p : ℕ} (hp : p.prime) : is_coprime a p ↔ ¬ ↑p ∣ a :=
begin
  rw ← int.gcd_eq_one_iff_coprime,
  split,
  { intros hcop hdvd,
    have := int.dvd_gcd hdvd (dvd_refl _),
    rw hcop at this,
    have peq1 := eq_one_of_dvd_one (coe_nat_nonneg p) this,
    norm_cast at peq1,
    rw peq1 at hp,
    exact nat.not_prime_one hp },
  intro hndvd,
  cases (nat.dvd_prime hp).mp (coe_nat_dvd.mp $ gcd_dvd_right a p) with h1 heqp,
  { assumption },
  exfalso, apply hndvd, rw ← heqp, apply gcd_dvd_left,
end

end int

local notation ` ϕ ` := nat.totient

lemma int.modeq.pow_totient {x : ℤ} {n : ℕ} (h : is_coprime x n) :
  x ^ ϕ n ≡ 1 [ZMOD n] :=
begin
  cases n, {simp},
  rcases @int.modeq.exists_unique_equiv_nat x ↑(n.succ) _ with ⟨y, hyn, hy⟩, swap,
  { simp, linarith },
  apply int.modeq.trans (int.modeq.modeq_pow hy.symm),
  convert_to ↑(y ^ n.succ.totient) ≡ ↑1 [ZMOD ↑(n.succ)], {simp},
  rw int.modeq.coe_nat_modeq_iff,
  apply nat.modeq.pow_totient,
  rw ←nat.is_coprime_iff_coprime,
  exact int.modeq.is_coprime_of_modeq h hy.symm,
end