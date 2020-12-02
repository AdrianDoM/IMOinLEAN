import data.mv_polynomial.basic

noncomputable theory

def X : mv_polynomial (fin 2) ℤ := mv_polynomial.X 0
def Y : mv_polynomial (fin 2) ℤ := mv_polynomial.X 1

#check X * Y

variables {p q : Prop}

#check @absurd -- absurd : Π {a : Prop} {b : Sort u_1}, a → ¬a → b

theorem contrapositive : (p → q) → (¬q → ¬p) :=
assume hpq hnq hp, absurd (hpq hp) hnq 
