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

theorem eval_multiset_sum (s : multiset (mv_polynomial σ R)) (g : σ → R) :
	eval g (s.sum) = (s.map (eval g)).sum :=
(eval g).map_multiset_sum _

theorem eval_list_sum (l : list (mv_polynomial σ R)) (g : σ → R) :
	eval g (l.sum) = (l.map (eval g)).sum :=
(eval g).map_list_sum _

theorem eval_zip_with_mul (l₁ l₂ : list (mv_polynomial σ R)) (g : σ → R) :
	list.map (eval g) (list.zip_with (*) l₁ l₂) = list.zip_with (*) (l₁.map (eval g)) (l₂.map (eval g)) :=
begin
	induction l₁ with hd₁ tl₁ ih₁ generalizing l₂, { simp },
	induction l₂ with hd₂ tl₂ ih₂, { simp },
	simp only [list.map_cons, list.zip_with_cons_cons], split,
	{	rw eval_mul },
	exact ih₁ tl₂,
end

end eval
end comm_semiring
end mv_polynomial