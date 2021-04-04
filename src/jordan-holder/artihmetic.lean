import data.zmod.basic
import .normal_series

namespace nat

lemma pos_left_of_mul_pos {m n : ℕ} (h : 0 < m * n) : 0 < m :=
nat.pos_of_ne_zero $ λ h2, by simpa [h2] using h

lemma pos_right_of_mul_pos {m n : ℕ} (h : 0 < m * n) : 0 < n :=
by { rw mul_comm at h, exact pos_left_of_mul_pos h }

lemma prod_pos_of_cons {l : list ℕ} {n : ℕ} : 0 < (n :: l).prod → 0 < l.prod :=
λ h, by { rw list.prod_cons at h, exact pos_right_of_mul_pos h }

lemma modeq.modeq_mul_right'_iff {n a b c : ℕ} (hc : c ≠ 0) :
  a * c ≡ b * c [MOD n * c] ↔ a ≡ b [MOD n] :=
⟨λ h, begin
  rw modeq.modeq_iff_dvd at *,
  rcases h with ⟨q, hq⟩, use q,
  simp only [int.coe_nat_mul] at hq,
  rw [←sub_mul, mul_assoc, mul_comm ↑c, ←mul_assoc] at hq,
  have : (c : ℤ) ≠ 0 := by simp [hc],
  exact mul_right_cancel' this hq,
end, modeq.modeq_mul_right' c⟩

end nat

open list add_normal_embedding add_normal_series add_composition_series zmod nat

def normal_embedding_to_mul (l : list ℕ) (m : ℕ) (h : 0 < m * l.prod) :
  add_normal_embedding (zmod l.prod) (zmod (m :: l).prod) :=
have hl : 0 < l.prod := nat.pos_right_of_mul_pos h,
have hm : m ≠ 0 := ne_of_gt $ nat.pos_left_of_mul_pos h,
{ to_fun := λ x, ↑(x.val * m),
  map_zero' := by simp,
  map_add' := λ x y, begin
    rw [←nat.cast_add, ←add_mul, zmod.eq_iff_modeq_nat, prod_cons, mul_comm m],
    apply modeq.modeq_mul_right' m,
    rw [←zmod.eq_iff_modeq_nat, @zmod.val_add _ ⟨hl⟩, zmod.nat_cast_mod],
  end,
  inj := λ x y h1, begin
    rw [add_monoid_hom.coe_mk, eq_iff_modeq_nat, prod_cons, mul_comm m,
      modeq.modeq_mul_right'_iff hm, ←eq_iff_modeq_nat] at h1,
    simpa [@nat_cast_val _ _ _ ⟨hl⟩] using h1,
  end,
  norm := infer_instance }

def normal_series_of_factors : Π {l : list ℕ} (hl : 0 < l.prod),
  add_normal_series (AddGroup.of $ zmod l.prod)
| [] _ := add_normal_series.trivial (by { simp, apply_instance })
| (m::l) hl := add_normal_series.cons
  (AddGroup.of (zmod l.prod)) (AddGroup.of (zmod (m::l).prod))
  (normal_embedding_to_mul l m (by simpa using hl))
  (normal_series_of_factors (pos_right_of_mul_pos (by simpa using hl)))

local attribute [instance] classical.prop_decidable

lemma finite_factors : Π {l : list ℕ} (hl : l.prod > 0),
  ∀ G ∈ (normal_series_of_factors hl).factors, is_finite_add_class G
| [] _ := λ G hG, by { exfalso, simpa [normal_series_of_factors] using hG }
| (m::l) hl := λ G hG, begin
  simp [normal_series_of_factors] at hG, rcases hG with rfl | hG,
  { apply is_finite_add_class_mk', change fintype (quotient_add_group.quotient _),
    apply @quotient.fintype _ (@zmod.fintype _ ⟨hl⟩) },
  exact finite_factors (prod_pos_of_cons hl) _ hG,
end

lemma card_factors_of_normal_series_of_factors : Π {l : list ℕ} (hl : 0 < l.prod),
  (normal_series_of_factors hl).factors.pmap add_class_card (finite_factors hl)
  = quotient.mk' l
| [] _ := by { simp [normal_series_of_factors], refl }
| (m::l) hl := show _ = m ::ₘ quotient.mk' l, begin
  haveI : fact (0 < (m::l).prod) := ⟨hl⟩,
  simp [normal_series_of_factors, multiset.cons_eq_cons], left, split, swap,
  { exact card_factors_of_normal_series_of_factors (prod_pos_of_cons hl) },
  rw add_class_card_mk', simp only [AddGroup.coe_of], rw prod_cons at hl,
  have h := card_eq_card_quotient_mul_card_add_subgroup (normal_embedding_to_mul l m hl).φ.range,
  swap, { apply_instance }, rw zmod.card at h,
  suffices : fintype.card ↥((normal_embedding_to_mul l m hl).φ.range) = l.prod,
  { simp only [this, prod_cons, mul_eq_mul_right_iff] at h,
    cases h, { exact h.symm }, exact absurd h (ne_of_gt $ pos_right_of_mul_pos hl) },
  haveI : fact (0 < l.prod) := ⟨pos_right_of_mul_pos hl⟩,
  rw [←fintype.card_congr (normal_embedding_to_mul l m hl).equiv_range.to_equiv, zmod.card],
end

lemma card_factors {l : list ℕ} (hl : 0 < l.prod)
  {G : _} (hG : G ∈ (normal_series_of_factors hl).factors) :
  add_class_card G (finite_factors hl G hG) ∈ l :=
suffices h : add_class_card G (finite_factors hl G hG) ∈
  (normal_series_of_factors hl).factors.pmap add_class_card (finite_factors hl),
by { rw card_factors_of_normal_series_of_factors hl at h, exact h },
multiset.mem_pmap.mpr ⟨G, hG, rfl⟩

def composition_series_of_prime_factors {l : list ℕ} (h : ∀ p ∈ l, nat.prime p) :
  add_composition_series (AddGroup.of $ zmod l.prod) :=
have hl : 0 < l.prod := nat.pos_of_ne_zero $ prod_ne_zero (λ h0, nat.not_prime_zero $ h 0 h0),
⟨normal_series_of_factors hl, λ G hG,
  ⟨is_simple_add_class_of_prime_card (finite_factors hl _ hG) (h _ $ card_factors hl hG),
  not_is_trivial_add_class_of_prime_card (finite_factors hl _ hG) (h _ $ card_factors hl hG)⟩⟩

theorem eq_prime_factors {s t : list ℕ} (hs : ∀ p ∈ s, nat.prime p) (ht : ∀ p ∈ t, nat.prime p) :
  s.prod = t.prod → s ~ t :=
have hs' : 0 < s.prod := nat.pos_of_ne_zero $ prod_ne_zero (λ h0, nat.not_prime_zero $ hs 0 h0),
have ht' : 0 < t.prod := nat.pos_of_ne_zero $ prod_ne_zero (λ h0, nat.not_prime_zero $ ht 0 h0),
λ h, show setoid.r s t, begin
  rw [←quotient.eq', ←card_factors_of_normal_series_of_factors hs',
    ←card_factors_of_normal_series_of_factors ht'],
  let σ := composition_series_of_prime_factors hs,
  let τ := composition_series_of_prime_factors ht,
  conv in (normal_series_of_factors hs') { change σ.val },
  conv in (normal_series_of_factors ht') { change τ.val },
  haveI : fact (0 < s.prod) := ⟨hs'⟩,
  haveI : fact (0 < t.prod) := ⟨ht'⟩,
  have iso : (AddGroup.of (zmod t.prod)) ≃+ (AddGroup.of (zmod s.prod)) := by rw h,
  congr' 1, rw [←add_composition_series.factors_of_add_equiv iso τ, eq_factors],
end

