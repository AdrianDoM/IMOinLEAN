import data.zmod.basic
import .normal_series

open list

#print normal_series

def normal_series_of_factors {n : ℕ} {l : list ℕ} (hn : n > 0) (hl : l.prod = n) :
  add_normal_series (AddGroup.of $ zmod n) :=
begin
  induction l with hd tl ih generalizing n,
  { rw prod_nil at hl, rw ←hl, apply add_normal_series.trivial, simp, apply_instance },
  
end