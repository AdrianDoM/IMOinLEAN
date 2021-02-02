import group_theory.subgroup
import data.nat.basic

def normal_in {G : Type*} [group G] (N H : subgroup G) : Prop :=
∀ n, n ∈ N → ∀ h, h ∈ H → h * n * h⁻¹ ∈ N

infix ` ◃ `:50 := normal_in

section normal_in

variables {G : Type*} [group G]

theorem normal_in_top {N : subgroup G} : N ◃ ⊤ ↔ N.normal :=
⟨λ h, ⟨λ n hn g, h n hn g (subgroup.mem_top _)⟩, λ h n hn g hg, h.conj_mem n hn g⟩

end normal_in

structure normal_series (G : Type*) [group G] :=
(series : list (subgroup G))
(nonempty : series ≠ [])
(head : series.head = ⊥)
(last : series.last nonempty = ⊤)
(normal : ∀ (i : ℕ) (h : i + 1 < series.length),
  series.nth_le i (nat.lt_of_succ_lt h) ◃ series.nth_le (i + 1) h)

namespace normal_series

end normal_series