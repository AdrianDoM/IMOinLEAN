/-
Author: Adrián Doña Mateo.
-/

import imo2017_q6
import data.list.forall2
import bezout

open mv_polynomial (hiding X) int (hiding range gcd) finset (hiding gcd) euclidean_domain
open_locale big_operators

local notation `polyℤ` := mv_polynomial (fin 2) ℤ
local notation `ϕ` := nat.totient

