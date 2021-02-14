import algebra.category.Group

universe u

lemma finite_group_strong_rec {C : Π (G : Group), fintype G → Sort u} :
  (∀ (G : Group) (hG : fintype G),
    (∀ (H : Group) (hH : fintype H), @fintype.card H hH < @fintype.card G hG → C H hH) → C G hG) → 
  ∀ (G : Group) (hG : fintype G), C G hG :=
λ ih, suffices h : ∀ n (G : Group) (hG : fintype G), @fintype.card G hG = n → C G hG,
  from λ G hG, h (@fintype.card G hG) G hG rfl,
λ N, N.strong_rec_on $ λ n h G hG hGcard, ih G hG $
  λ H hH hHcard, h (@fintype.card H hH) (hGcard ▸ hHcard) H hH rfl