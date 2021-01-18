import data.list.basic
import data.list.erase_dup

namespace list

variable {α : Type*}

lemma exists_mem_of_ne_nil {l : list α} (h : l ≠ nil) : ∃ a, a ∈ l :=
begin
	rcases exists_cons_of_ne_nil h with ⟨a, tl, rfl⟩,
	use a, simp,
end

lemma cons_sublist_of_cons_sublist_cons {s t : list α} {a b : α} (h : a ≠ b) :
	a :: s <+ b :: t → a :: s <+ t :=
begin
	intro hsub,	cases hsub,
	{	assumption },
	contradiction,
end

lemma pow_count_dvd_prod [comm_monoid α] [decidable_eq α] (l : list α) (a : α) :
	a ^ count a l ∣ l.prod :=
begin
	induction l with hd tl ih, { simp },
	simp [count_cons],
	split_ifs,
	{	rw [← h, pow_succ], apply mul_dvd_mul_left a ih },
	apply dvd.trans ih, apply dvd_mul_left,
end

/- data/list/erase_dup.lean -/

@[simp]
theorem erase_dup_eq_nil {l : list α} [decidable_eq α] : l.erase_dup = [] ↔ l = [] :=
begin
	split,
	{	intro h1, by_contradiction h2,
		cases exists_mem_of_ne_nil h2 with x hx,
		rw eq_nil_iff_forall_not_mem at h1,
		apply h1 x, rwa mem_erase_dup },
	intro h, simp [h],
end

end list