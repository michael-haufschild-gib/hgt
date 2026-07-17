import Mathlib.Tactic

/-!
# The logarithmic pole is the unique expanding ramification fixed point

For a rational eigenvolume under a finite map, canonical-divisor pullback gives the local order
law `c + 1 = e * (c_next + 1)`.  After passing to an iterate which fixes a periodic divisor, an
expanding ramification index `e > 1` forces `c = -1`.  This file formalizes that exact arithmetic
core: expansion selects a simple logarithmic pole and excludes both zeros and higher poles.
-/

namespace GaloisForLFunctions

/-- The shifted order `c + 1` has only the zero fixed point under multiplication by `e > 1`. -/
theorem ramificationShift_fixed_eq_neg_one
    {c : ℤ} {e : ℕ} (he : 1 < e)
    (h : c + 1 = (e : ℤ) * (c + 1)) :
    c = -1 := by
  have hprod : ((e : ℤ) - 1) * (c + 1) = 0 := by
    calc
      ((e : ℤ) - 1) * (c + 1) = (e : ℤ) * (c + 1) - (c + 1) := by ring
      _ = 0 := by rw [← h]; ring
  have he0 : (e : ℤ) - 1 ≠ 0 := by omega
  have hc0 : c + 1 = 0 := (mul_eq_zero.mp hprod).resolve_left he0
  omega

/-- In unshifted divisor notation, `c = e*c + (e-1)` with `e > 1` forces a simple pole. -/
theorem ramificationPoleOrder_fixed_eq_neg_one
    {c : ℤ} {e : ℕ} (he : 1 < e)
    (h : c = (e : ℤ) * c + ((e : ℤ) - 1)) :
    c = -1 := by
  apply ramificationShift_fixed_eq_neg_one he
  calc
    c + 1 = ((e : ℤ) * c + ((e : ℤ) - 1)) + 1 :=
      congrArg (fun z : ℤ => z + 1) h
    _ = (e : ℤ) * (c + 1) := by ring

/-- A periodic eigen-`k`-canonical density has pole order exactly `-k` at expansion. -/
theorem ramificationPluriPoleOrder_fixed_eq_neg_weight
    {c : ℤ} {e k : ℕ} (he : 1 < e)
    (h : c = (e : ℤ) * c + (k : ℤ) * ((e : ℤ) - 1)) :
    c = -(k : ℤ) := by
  have hshift : c + (k : ℤ) = (e : ℤ) * (c + (k : ℤ)) := by
    calc
      c + (k : ℤ) =
          ((e : ℤ) * c + (k : ℤ) * ((e : ℤ) - 1)) + (k : ℤ) :=
        congrArg (fun z : ℤ => z + (k : ℤ)) h
      _ = (e : ℤ) * (c + (k : ℤ)) := by ring
  have hfixed := ramificationShift_fixed_eq_neg_one
    (c := c + (k : ℤ) - 1) he (by simpa using hshift)
  omega

end GaloisForLFunctions
