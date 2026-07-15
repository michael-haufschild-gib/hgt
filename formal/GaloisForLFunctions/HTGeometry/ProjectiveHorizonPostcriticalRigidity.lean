import GaloisForLFunctions.HTGeometry.ProjectiveHorizonPureTailFiber

/-!
# One-step postcritical rigidity of the pure horizon fiber

At critical order `L-1`, the pure `(m,n)` horizon fiber is the set of factorizations
`X₀ Y₀ = 1+t^L`.  Add one raw coefficient `u t^L` and one reciprocal coefficient `v t^L`.
The coefficient of `t^L` in the new inverse error is exactly

`1 + u Y₀(0) + v X₀(0)`.

In particular, at `u=0` the first postcritical reciprocal coefficient is `-X₀(0)⁻¹`.  It
distinguishes pure-fiber factors with different constant terms.  This is the explicit algebraic
witness used by the paper theorem that one postcritical coefficient breaks the atomic critical
Galois ambiguity.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Add the first postcritical raw coefficient to a pure critical left factor. -/
def pureCriticalPostLeft {K : Type*} [CommRing K]
    (m n : ℕ) (A : K[X]) (u : K) : K[X] :=
  pureCriticalLeftFactor m A + C u * X ^ (m + n)

/-- Add the first postcritical reciprocal coefficient to a pure critical right factor. -/
def pureCriticalPostRight {K : Type*} [CommRing K]
    (m n : ℕ) (B : K[X]) (v : K) : K[X] :=
  pureCriticalRightFactor n B + C v * X ^ (m + n)

/-- Exact first postcritical coefficient of the inverse error over a pure critical factorization. -/
theorem pureCritical_postcritical_error_coeff {K : Type*} [CommRing K]
    {m n : ℕ} (hL : 0 < m + n) (A B : K[X]) (u v : K)
    (hfac : pureCriticalLeftFactor m A * pureCriticalRightFactor n B =
      pureCriticalCyclicPolynomial (K := K) (m + n)) :
    (pureCriticalPostLeft m n A u * pureCriticalPostRight m n B v - 1).coeff (m + n) =
      1 + u * (pureCriticalRightFactor n B).coeff 0 +
        v * (pureCriticalLeftFactor m A).coeff 0 := by
  have herr :
      pureCriticalPostLeft m n A u * pureCriticalPostRight m n B v - 1 =
        X ^ (m + n) +
          C u * X ^ (m + n) * pureCriticalRightFactor n B +
          C v * X ^ (m + n) * pureCriticalLeftFactor m A +
          C u * C v * X ^ (2 * (m + n)) := by
    calc
      pureCriticalPostLeft m n A u * pureCriticalPostRight m n B v - 1 =
          (pureCriticalLeftFactor m A * pureCriticalRightFactor n B - 1) +
            C u * X ^ (m + n) * pureCriticalRightFactor n B +
            C v * X ^ (m + n) * pureCriticalLeftFactor m A +
            C u * C v * X ^ (2 * (m + n)) := by
              simp only [pureCriticalPostLeft, pureCriticalPostRight]
              ring
      _ = X ^ (m + n) +
          C u * X ^ (m + n) * pureCriticalRightFactor n B +
          C v * X ^ (m + n) * pureCriticalLeftFactor m A +
          C u * C v * X ^ (2 * (m + n)) := by
            rw [hfac]
            simp [pureCriticalCyclicPolynomial]
  have hucoeff :
      (C u * X ^ (m + n) * pureCriticalRightFactor n B).coeff (m + n) =
        u * (pureCriticalRightFactor n B).coeff 0 := by
    rw [mul_assoc, coeff_C_mul]
    congr 1
    simpa using coeff_X_pow_mul (pureCriticalRightFactor n B) (m + n) 0
  have hvcoeff :
      (C v * X ^ (m + n) * pureCriticalLeftFactor m A).coeff (m + n) =
        v * (pureCriticalLeftFactor m A).coeff 0 := by
    rw [mul_assoc, coeff_C_mul]
    congr 1
    simpa using coeff_X_pow_mul (pureCriticalLeftFactor m A) (m + n) 0
  have huvcoeff :
      (C u * C v * X ^ (2 * (m + n))).coeff (m + n) = 0 := by
    rw [← C_mul, coeff_C_mul, coeff_X_pow]
    simp [show m + n ≠ 2 * (m + n) by omega]
  rw [herr]
  simp [hucoeff, hvcoeff, huvcoeff]

/-- Compatibility through one more coefficient forces the exact top-coefficient equation. -/
theorem pureCriticalPost_topEquation {K : Type*} [CommRing K]
    {m n : ℕ} (hL : 0 < m + n) (A B : K[X]) (u v : K)
    (hfac : pureCriticalLeftFactor m A * pureCriticalRightFactor n B =
      pureCriticalCyclicPolynomial (K := K) (m + n))
    (hInv : X ^ (m + n + 1) ∣
      pureCriticalPostLeft m n A u * pureCriticalPostRight m n B v - 1) :
    1 + u * (pureCriticalRightFactor n B).coeff 0 +
        v * (pureCriticalLeftFactor m A).coeff 0 = 0 := by
  rw [← pureCritical_postcritical_error_coeff hL A B u v hfac]
  exact X_pow_dvd_iff.mp hInv (m + n) (by omega)

/-- With zero new raw coefficient, the first postcritical reciprocal coefficient is the negative
inverse constant term of the chosen left factor. -/
theorem pureCriticalPost_rightTop_eq_neg_inv {K : Type*} [Field K]
    {m n : ℕ} (hL : 0 < m + n) (A B : K[X]) (v : K)
    (hfac : pureCriticalLeftFactor m A * pureCriticalRightFactor n B =
      pureCriticalCyclicPolynomial (K := K) (m + n))
    (hx0 : (pureCriticalLeftFactor m A).coeff 0 ≠ 0)
    (hInv : X ^ (m + n + 1) ∣
      pureCriticalPostLeft m n A 0 * pureCriticalPostRight m n B v - 1) :
    v = -((pureCriticalLeftFactor m A).coeff 0)⁻¹ := by
  have heq := pureCriticalPost_topEquation hL A B 0 v hfac hInv
  simp only [zero_mul, add_zero] at heq
  have hmul : v * (pureCriticalLeftFactor m A).coeff 0 = -1 := by
    linear_combination heq
  calc
    v = (-1) / (pureCriticalLeftFactor m A).coeff 0 :=
      (eq_div_iff hx0).2 hmul
    _ = -((pureCriticalLeftFactor m A).coeff 0)⁻¹ := by
      rw [div_eq_mul_inv]
      ring

end

end GaloisForLFunctions.HTGeometry
