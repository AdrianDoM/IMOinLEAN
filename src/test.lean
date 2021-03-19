#check ℕ
#check bool
#check char

constants (α : Type) (p : Prop)
#check ∀ p : Prop, p → p
#check ∀ α : Type, α → α
#check p → p
#check α → α
#check list

universe u
inductive vector (α : Type u) : ℕ → Type u
| nil {} : vector 0
| cons {n : ℕ} (a : α) (v : vector n) : vector (n+1)