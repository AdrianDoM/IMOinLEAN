import category_theory.isomorphism_classes
import algebra.category.Group
import .subgroup .normal_embedding .simple_group .trivial_class

universe u

inductive normal_series : Group.{u} → Type (u+1)
| trivial {G : Group} : normal_series G
| cons (H G : Group)
  (f : normal_embedding H G) (s : normal_series H) : normal_series G

namespace normal_series

variables {G H K : Group.{u}}

/- Given a normal series for G and an isomorphism G ≃* H, we can produce a normal series for H
by changing the last step from going into G to go into H -/
def of_mul_equiv_right (h : G ≃* H) : normal_series G → normal_series H
| trivial := trivial
| (cons K G f s) := cons K H (normal_embedding.comp_mul_equiv f h) s

open category_theory

local attribute [instance] is_isomorphic_setoid

/- The factors of a normal series are the quotient groups of consecutive elements in the series -/
def factors : Π {G : Group.{u}}, normal_series G → multiset (isomorphism_classes.obj $ Cat.of Group)
| G trivial := ⟦G⟧ ::ₘ 0
| _ (cons H G f s) := ⟦Group.of (quotient_group.quotient f.φ.range)⟧ ::ₘ factors s

end normal_series

/- A composition series is a normal series with simple and nontrivial factors -/
structure composition_series (G : Group.{u}) : Type (u+1) :=
(series : normal_series G)
(simple : ∀ G' ∈ series.factors, is_simple_class G' ∧ ¬ is_trivial_class G')
