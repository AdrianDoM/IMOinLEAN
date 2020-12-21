import ring_theory.polynomial.homogeneous
import finset

namespace mv_polynomial
variables {σ : Type*} {τ : Type*} {R : Type*} {S : Type*}

namespace is_homogeneous
variables [comm_semiring R] {φ ψ : mv_polynomial σ R} {m n : ℕ}

lemma pow (hφ : is_homogeneous φ n) (k : ℕ) :
	is_homogeneous (φ ^ k) (n * k) :=
begin
	rw [finset.pow_eq_prod_const],
	convert prod (finset.range k) (λ _, φ) (λ _, n) (λ _ _, hφ),
	simp [nat.mul_comm],
end

end is_homogeneous

end mv_polynomial