import data.fintype.basic
import algebra.group.basic

open fintype

variables {α β : Type*} [fintype α] [fintype β]

lemma card_ge_of_surjective {f : α → β} (hf : function.surjective f) : card α ≥ card β :=
card_le_of_injective (function.surj_inv hf) (function.injective_surj_inv hf)

lemma card_quotient_le {s : setoid α} [decidable_rel s.r] :
  fintype.card (quotient s) ≤ fintype.card α :=
card_ge_of_surjective (surjective_quotient_mk _)

def strong_rec_on_card (G : Type*) [group G] [fintype G] 
  {p : Π (G : Type*) [group G] [fintype G], Sort _} :
  (Π (G : Type*) [group G] [fintype G],
    (Π (H : Type*) [group H] [fintype H], by exactI card H < card G → p H) →
    by exactI p G) →
  p G :=
λ ih, suffices h : ∀ (n : ℕ) (G : Type*) [group G] [fintype G], by exactI card G = n → p G,
  from h (card G) G rfl,
λ n, n.strong_rec_on $ begin
  intros n ih' G, introsI _ _, intro hn,
  apply ih G,
  intro H, introsI _ _, intro hH,
  exact ih' (card H) (hn ▸ hH) H rfl,
end