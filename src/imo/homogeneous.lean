import ring_theory.polynomial.homogeneous
import data.list.basic
import .finset

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

lemma multiset_sum (s : multiset (mv_polynomial σ R)) (n : ℕ) :
	(∀ φ ∈ s, is_homogeneous φ n) → is_homogeneous s.sum n :=
begin
	apply multiset.induction_on s, { simp [is_homogeneous_zero] },
	intros ψ s ih h, rw multiset.sum_cons,
	apply (h ψ (multiset.mem_cons_self _ _)).add (ih _),
	intros φ hφ, apply h φ (multiset.mem_cons_of_mem hφ),
end

lemma list_sum (l : list (mv_polynomial σ R)) (n : ℕ)	(h : ∀ φ ∈ l, is_homogeneous φ n) :
	is_homogeneous l.sum n :=
begin
	revert h,
	induction l with hd tl ih,
	{	intro, simp only [is_homogeneous_zero, list.sum_nil] },
	intro h, rw list.sum_cons,
	apply (h hd (list.mem_cons_self _ _)).add (ih _),
	intros φ hφ, apply h φ (list.mem_cons_of_mem _ hφ),
end

lemma zip_with_mul_sum_homogeneous (l₁ l₂ : list (mv_polynomial σ R)) (n₁ n₂ : ℕ)
	(h₁ : ∀ φ ∈ l₁, is_homogeneous φ n₁) (h₂ : ∀ φ ∈ l₂, is_homogeneous φ n₂) :
	is_homogeneous (list.zip_with (*) l₁ l₂).sum (n₁ + n₂) :=
begin
	apply list_sum, intros φ hφ,
	cases list.mem_iff_nth.mp hφ with i hi,
	rw list.nth_zip_with_eq_some at hi,
	rcases hi with ⟨φ₁, φ₂, hs₁, hs₂, rfl⟩,
	apply mul (h₁ _ _) (h₂ _ _);
	{ apply list.mem_iff_nth.mpr, use i, assumption }
end

#check list.nth_zip_with_eq_some

end is_homogeneous

end mv_polynomial
