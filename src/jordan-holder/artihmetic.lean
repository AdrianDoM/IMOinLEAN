import data.zmod.basic
import .normal_series

open list add_normal_embedding add_normal_series add_composition_series zmod nat

def normal_embedding_of_dvd {m n : ℕ} (h : m ∣ n) :
  add_normal_embedding (zmod $ n / m) (zmod n) :=
{ to_fun := λ x, x.val * m,
  map_zero' := by simp,
  map_add' := λ x y, sorry,
  inj := λ x y h, sorry,
  norm := infer_instance } 

def normal_series_of_factors {n : ℕ} {l : list ℕ} (hn : n > 0) (hl : l.prod = n) :
  add_normal_series (AddGroup.of $ zmod n) :=
begin
  induction l with m l ih generalizing n,
  { rw prod_nil at hl, rw ←hl, apply add_normal_series.trivial, simp, apply_instance },
  apply add_normal_series.cons (AddGroup.of $ zmod (n / m)) (AddGroup.of $ zmod n)
    (normal_embedding_of_dvd _) (@ih (n / m) _ _),
  repeat { sorry },
end

lemma factors_of_normal_series_of_factors {n : ℕ} {l : list ℕ} (hn : n > 0) (hl : l.prod = n) :
  (normal_series_of_factors hn hl).factors.map class_card = quotient.mk' l := sorry

def composition_series_of_prime_factors {n : ℕ} {l : list ℕ} (hn : n > 0) (hl : l.prod = n)
  (h : ∀ p ∈ l, nat.prime p) : add_composition_series (AddGroup.of $ zmod n) :=
⟨normal_series_of_factors hn hl, sorry⟩

theorem eq_prime_factors {n : ℕ} {s t : list ℕ}
  (hs1 : s.prod = n) (hs2 : ∀ p ∈ s, nat.prime p)
  (ht1 : t.prod = n) (ht2 : ∀ p ∈ s, nat.prime p) :
  (quotient.mk' s : multiset ℕ) = quotient.mk' t :=
sorry

