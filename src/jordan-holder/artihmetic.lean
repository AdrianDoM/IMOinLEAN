import data.zmod.basic
import .normal_series

lemma nat.prod_pos_of_cons {l : list ℕ} {n : ℕ} : 0 < (n :: l).prod → 0 < l.prod :=
λ h1, nat.pos_of_ne_zero $ λ h2, by simpa [h2] using h1

open list add_normal_embedding add_normal_series add_composition_series zmod nat

def normal_embedding_to_mul (m n : ℕ) :
  add_normal_embedding (zmod m) (zmod $ n * m) :=
{ to_fun := λ x, x.val * m,
  map_zero' := by simp,
  map_add' := λ x y, sorry,
  inj := λ x y h, sorry,
  norm := infer_instance } 

def normal_series_of_factors : Π {l : list ℕ} (hl : 0 < l.prod),
  add_normal_series (AddGroup.of $ zmod l.prod)
| [] _ := add_normal_series.trivial (by { simp, apply_instance })
| (m::l) hl := begin 
  apply add_normal_series.cons (AddGroup.of $ zmod l.prod) (AddGroup.of $ zmod (m::l).prod),
  { change add_normal_embedding (zmod l.prod) (zmod (m::l).prod),
    convert normal_embedding_to_mul l.prod m; rw prod_cons },
  exact normal_series_of_factors (prod_pos_of_cons hl),
end

local attribute [instance] classical.prop_decidable

lemma finite_factors : Π {l : list ℕ} (hl : l.prod > 0),
  ∀ G ∈ (normal_series_of_factors hl).factors, is_finite_add_class G
| [] _ := λ G hG, by { exfalso, simpa [normal_series_of_factors] using hG }
| (m::l) hl := λ G hG, begin
  simp [normal_series_of_factors] at hG, rcases hG with rfl | hG,
  { apply is_finite_add_class_mk', change fintype (quotient_add_group.quotient _),
    apply @quotient.fintype _ (@zmod.fintype _ hl) },
  exact finite_factors (prod_pos_of_cons hl) _ hG,
end

lemma card_factors_of_normal_series_of_factors : Π {l : list ℕ} (hl : 0 < l.prod),
  (normal_series_of_factors hl).factors.pmap add_class_card (finite_factors hl)
  = quotient.mk' l
| [] _ := by { simp [normal_series_of_factors], refl }
| (m::l) hl := show _ = m ::ₘ quotient.mk' l, begin
  simp [normal_series_of_factors, multiset.cons_eq_cons], left, split, swap,
  { exact card_factors_of_normal_series_of_factors (prod_pos_of_cons hl) },
  rw add_class_card_mk' _, swap,
  { change fintype (quotient_add_group.quotient _),
    apply @quotient.fintype _ (@zmod.fintype _ hl) },
  simp only [AddGroup.coe_of], sorry,
end

lemma card_factors {l : list ℕ} (hl : 0 < l.prod)
  (G : _) (hG : G ∈ (normal_series_of_factors hl).factors) :
  add_class_card G (finite_factors hl G hG) ∈ l :=
suffices h : add_class_card G (finite_factors hl G hG) ∈
  (normal_series_of_factors hl).factors.pmap add_class_card (finite_factors hl),
by { rw card_factors_of_normal_series_of_factors hl at h, exact h },
multiset.mem_pmap.mpr ⟨G, hG, rfl⟩

def composition_series_of_prime_factors {l : list ℕ} (hl : 0 < l.prod)
  (h : ∀ p ∈ l, nat.prime p) : add_composition_series (AddGroup.of $ zmod l.prod) :=
⟨normal_series_of_factors hl,
λ G hG, begin
  
end⟩

theorem eq_prime_factors {n : ℕ} {s t : list ℕ}
  (hs1 : s.prod = n) (hs2 : ∀ p ∈ s, nat.prime p)
  (ht1 : t.prod = n) (ht2 : ∀ p ∈ s, nat.prime p) :
  (quotient.mk' s : multiset ℕ) = quotient.mk' t :=
sorry

