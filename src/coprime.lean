import int
import ring_theory.coprime

theorem int.is_coprime_iff_gcd_eq_one {m n : ℤ} : is_coprime m n ↔ int.gcd m n = 1 :=
begin
	split,
	{ rintro ⟨a, b, hab⟩,
		have : ↑(int.gcd m n) ∣ (1 : ℤ) :=
			hab ▸ dvd_add
				(dvd_mul_of_dvd_right (int.gcd_dvd_left m n) a)
				(dvd_mul_of_dvd_right (int.gcd_dvd_right m n) b),
		cases int.dvd_one this with h1 hn1,
		{ assumption_mod_cast },
		exfalso,
		have : ↑(int.gcd m n) ≥ 0 := by apply nat.cast_nonneg,
		linarith },
	intro hgcd,
	rcases int.exists_mul_eq_gcd m n with ⟨a, b, hab⟩,
	simp [hgcd] at hab,
	use [a, b],
	conv_lhs { congr, rw mul_comm, skip, rw mul_comm },
	exact hab,
end

theorem int.is_coprime_prime {a : ℤ} {p : ℕ} (hp : p.prime) :
	is_coprime a p ↔ ¬ ↑p ∣ a :=
begin
	rw int.is_coprime_iff_gcd_eq_one,
	split,
	{	intros hgcd hdvd,
		apply_fun int.of_nat at hgcd, simp at hgcd,
		have : ↑p ∣ (1 : ℤ) := hgcd ▸ int.dvd_gcd hdvd (dvd_refl _),
		change ↑p ∣ ↑1 at this,
		rw int.coe_nat_dvd at this,
		exact nat.prime.not_dvd_one hp this },
	intro hndvd,
	have := int.gcd_dvd_right a p, rw int.coe_nat_dvd at this,
	cases (nat.dvd_prime hp).mp this with h1 heqp,
	{	assumption },
	exfalso,
	rw ← heqp at hndvd,
	exact hndvd (int.gcd_dvd_left a p),
end