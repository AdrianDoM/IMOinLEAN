import algebra.big_operators.basic

open_locale big_operators

namespace finset

theorem sum_one_range_eq (n : ℕ) : ∑ i in range n, 1 = n :=
sum_range_induction (λ _, 1) id rfl (λ _, rfl) n

end finset