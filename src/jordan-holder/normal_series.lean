import group_theory.subgroup
import .subgroup .normal_embedding

universe u

inductive normal_series : Π (G : Type u) [group G], Type (u+1)
| trivial {G : Type u} [group G] : normal_series G
| cons {H G : Type u} [group H] [group G]
  (f : normal_embedding H G) (s : normal_series H) : normal_series G

namespace normal_series

variables {G H K : Type u} [group G] [group H] [group K]

def of_mul_equiv_right (h : H ≃* K) : normal_series H → normal_series K
| trivial := trivial
| (@cons H' H gH' _ f s) :=
  @cons H' _ gH' _ (@normal_embedding.comp_mul_equiv _ _ _ gH' _ _ f h) s

end normal_series