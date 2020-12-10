import data.mv_polynomial.basic

universes u v
variables {R : Type u}

namespace mv_polynomial

variables {σ : Type*}

section comm_semiring

variables [comm_semiring R]

section eval

theorem eval_add (f g : mv_polynomial σ R) (x : σ → R) : eval x (f + g) = eval x f + eval x g :=
(eval x).map_add _ _

theorem eval_mul (f g : mv_polynomial σ R) (x : σ → R) : eval x (f * g) = eval x f * eval x g :=
(eval x).map_mul _ _

theorem eval_pow (f : mv_polynomial σ R) (n : ℕ) (x : σ → R) : eval x (f ^ n) = eval x f ^ n :=
(eval x).map_pow _ _


end eval
end comm_semiring
end mv_polynomial