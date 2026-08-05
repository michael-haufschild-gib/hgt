import GaloisForLFunctions.HTGeometry.GammaFieldSumBoundary

/-!
# The diagonal monomial limit is one

The boundary laws are conditioned on a nonvanishing monomial limit.  The limit compares two Gamma
monomial data and returns a ratio of leading coefficients when they match in order, degree and
depth.  On the diagonal — the same datum compared with itself — all three match and the ratio is
one, so the nonvanishing hypothesis holds there for every nonzero numerator and denominator.
-/

open Polynomial

namespace GaloisForLFunctions

/-- **The diagonal monomial limit is one.** -/
theorem gammaMonomialLimit_self (j : ℕ) {p q : Polynomial ℂ} (hp : p ≠ 0) (hq : q ≠ 0) (D : ℕ) :
    gammaMonomialLimit j p q D j p q D = 1 := by
  have hcond : j = j ∧ (p * q).natDegree = (q * p).natDegree ∧ D = D :=
    ⟨rfl, by rw [mul_comm], rfl⟩
  rw [gammaMonomialLimit, if_pos hcond, mul_comm p q]
  refine div_self ?_
  exact Polynomial.leadingCoeff_ne_zero.mpr (mul_ne_zero hq hp)

/-- Hence the nonvanishing hypothesis of the boundary laws holds on the diagonal. -/
theorem gammaMonomialLimit_self_ne_zero (j : ℕ) {p q : Polynomial ℂ} (hp : p ≠ 0) (hq : q ≠ 0)
    (D : ℕ) : gammaMonomialLimit j p q D j p q D ≠ 0 := by
  rw [gammaMonomialLimit_self j hp hq D]
  exact one_ne_zero

/-- So a nonvanishing monomial limit exists at every order and depth. -/
theorem exists_gammaMonomialLimit_ne_zero (j D : ℕ) :
    ∃ (p q : Polynomial ℂ), gammaMonomialLimit j p q D j p q D ≠ 0 :=
  ⟨1, 1, gammaMonomialLimit_self_ne_zero j one_ne_zero one_ne_zero D⟩

end GaloisForLFunctions
