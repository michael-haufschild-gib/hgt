import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Three-point correlation matrices

This file isolates the exact scalar wall for a real three-point correlation matrix.  The
positive-semidefinite criterion is proved directly from an `LDL*` square decomposition, and a
far-separated chamber is discharged without spectral or determinant assumptions.
-/

open Matrix
open scoped BigOperators Matrix

namespace HilbertMetric

/-- The real symmetric correlation matrix for three ordered points.  The entries `p`, `q`, and
`r` correspond respectively to the first adjacent gap, the second adjacent gap, and the full
gap. -/
def threePointCorrelationMatrix (d p q r : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![d, p, r; p, d, q; r, q, d]

/-- The cubic determinant wall for `threePointCorrelationMatrix`. -/
def threePointCorrelationDeterminant (d p q r : ℝ) : ℝ :=
  d ^ (3 : ℕ) + 2 * p * q * r - d * (p ^ (2 : ℕ) + q ^ (2 : ℕ) + r ^ (2 : ℕ))

private theorem threePointCorrelationMatrix_isHermitian (d p q r : ℝ) :
    Matrix.IsHermitian (threePointCorrelationMatrix d p q r) := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [threePointCorrelationMatrix]

/-- With a positive diagonal and a strictly smaller nonnegative first adjacent correlation,
positive semidefiniteness is exactly the single cubic determinant inequality. -/
theorem threePointCorrelationMatrix_posSemidef_iff
    {d p q r : ℝ} (hd : 0 < d) (hp0 : 0 ≤ p) (hp : p < d) :
    Matrix.PosSemidef (threePointCorrelationMatrix d p q r) ↔
      0 ≤ threePointCorrelationDeterminant d p q r := by
  let A : ℝ := d ^ (2 : ℕ) - p ^ (2 : ℕ)
  let B : ℝ := d * q - p * r
  have hA : 0 < A := by
    dsimp [A]
    nlinarith
  have hAraw : 0 < d ^ (2 : ℕ) - p ^ (2 : ℕ) := by simpa [A] using hA
  have hAne : d ^ (2 : ℕ) - p ^ (2 : ℕ) ≠ 0 := hAraw.ne'
  constructor
  · intro hM
    let v : Fin 3 → ℝ := ![p * B - r * A, -d * B, d * A]
    have hq := hM.dotProduct_mulVec_nonneg v
    have heq :
        star v ⬝ᵥ (threePointCorrelationMatrix d p q r).mulVec v =
          d ^ (2 : ℕ) * A * threePointCorrelationDeterminant d p q r := by
      simp [v, threePointCorrelationMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
        A, B, threePointCorrelationDeterminant]
      ring
    rw [heq] at hq
    exact nonneg_of_mul_nonneg_right hq (mul_pos (sq_pos_of_pos hd) hA)
  · intro hD
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (threePointCorrelationMatrix_isHermitian d p q r)
    intro v
    have hform :
        star v ⬝ᵥ (threePointCorrelationMatrix d p q r).mulVec v =
          d * (v 0 + (p / d) * v 1 + (r / d) * v 2) ^ (2 : ℕ) +
          (A / d) * (v 1 + (B / A) * v 2) ^ (2 : ℕ) +
          (threePointCorrelationDeterminant d p q r / A) * (v 2) ^ (2 : ℕ) := by
      simp [threePointCorrelationMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
        A, B, threePointCorrelationDeterminant]
      field_simp [hd.ne', hAne]
      ring
    rw [hform]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg hd.le (sq_nonneg _))
        (mul_nonneg (div_nonneg hA.le hd.le) (sq_nonneg _)))
      (mul_nonneg (div_nonneg hD hA.le) (sq_nonneg _))

private theorem threePointCorrelationDeterminant_nonneg_of_le_left
    {d p q r : ℝ}
    (hd0 : 0 ≤ d) (hp0 : 0 ≤ p) (hq0 : 0 ≤ q) (hr0 : 0 ≤ r)
    (hqd : q ≤ d) (hpq : p ≤ q) (hrp : r ≤ p)
    (hfar : p ^ (2 : ℕ) + q ^ (2 : ℕ) ≤ d ^ (2 : ℕ)) :
    0 ≤ threePointCorrelationDeterminant d p q r := by
  have hzero :
      0 ≤ threePointCorrelationDeterminant d p q 0 := by
    dsimp [threePointCorrelationDeterminant]
    nlinarith
  by_cases hpzero : p = 0
  · have hrzero : r = 0 := by linarith
    simpa [hrzero] using hzero
  · have hppos : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpzero)
    have hdq : 0 ≤ d - q := sub_nonneg.mpr hqd
    have haux0 : 0 ≤ (d - q) * (d + 2 * q) := by positivity
    have haux : 0 ≤ d * (d + q) - 2 * p ^ (2 : ℕ) := by
      have hpq_sq : p ^ (2 : ℕ) ≤ q ^ (2 : ℕ) := by nlinarith
      nlinarith
    have hend :
        0 ≤ threePointCorrelationDeterminant d p q p := by
      rw [show threePointCorrelationDeterminant d p q p =
          (d - q) * (d * (d + q) - 2 * p ^ (2 : ℕ)) by
        simp [threePointCorrelationDeterminant]
        ring]
      exact mul_nonneg hdq haux
    have hpr : 0 ≤ p - r := sub_nonneg.mpr hrp
    have hchord :
        p * threePointCorrelationDeterminant d p q r =
          (p - r) * threePointCorrelationDeterminant d p q 0 +
            r * threePointCorrelationDeterminant d p q p +
              p * d * r * (p - r) := by
      simp [threePointCorrelationDeterminant]
      ring
    have hprod : 0 ≤ p * threePointCorrelationDeterminant d p q r := by
      rw [hchord]
      positivity
    exact nonneg_of_mul_nonneg_right hprod hppos

/-- A nonnegative, radially ordered three-point packet is automatically positive in the
far-separated chamber where the two adjacent correlations have squared sum at most the squared
diagonal. -/
theorem threePointCorrelationDeterminant_nonneg_of_far_chamber
    {d p q r : ℝ}
    (hd0 : 0 ≤ d) (hp0 : 0 ≤ p) (hq0 : 0 ≤ q) (hr0 : 0 ≤ r)
    (hrp : r ≤ p) (hrq : r ≤ q)
    (hfar : p ^ (2 : ℕ) + q ^ (2 : ℕ) ≤ d ^ (2 : ℕ)) :
    0 ≤ threePointCorrelationDeterminant d p q r := by
  have hpd : p ≤ d := by
    nlinarith [sq_nonneg q]
  have hqd : q ≤ d := by
    nlinarith [sq_nonneg p]
  rcases le_total p q with hpq | hqp
  · exact threePointCorrelationDeterminant_nonneg_of_le_left
      hd0 hp0 hq0 hr0 hqd hpq hrp hfar
  · have h := threePointCorrelationDeterminant_nonneg_of_le_left
      hd0 hq0 hp0 hr0 hpd hqp hrq (by nlinarith [hfar])
    simpa [threePointCorrelationDeterminant, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using h

/-- Every nonnegative radially ordered packet in the far-separated chamber has a positive
semidefinite correlation matrix, including the zero-diagonal and rank-deficient boundary cases. -/
theorem threePointCorrelationMatrix_posSemidef_of_far_chamber
    {d p q r : ℝ}
    (hd0 : 0 ≤ d) (hp0 : 0 ≤ p) (hq0 : 0 ≤ q) (hr0 : 0 ≤ r)
    (hrp : r ≤ p) (hrq : r ≤ q)
    (hfar : p ^ (2 : ℕ) + q ^ (2 : ℕ) ≤ d ^ (2 : ℕ)) :
    Matrix.PosSemidef (threePointCorrelationMatrix d p q r) := by
  have hpd : p ≤ d := by
    nlinarith [sq_nonneg q]
  have hdet : 0 ≤ threePointCorrelationDeterminant d p q r :=
    threePointCorrelationDeterminant_nonneg_of_far_chamber
      hd0 hp0 hq0 hr0 hrp hrq hfar
  by_cases hd : d = 0
  · have hp : p = 0 := by linarith
    have hq : q = 0 := by nlinarith [sq_nonneg p, sq_nonneg q]
    have hr : r = 0 := by linarith
    subst d
    subst p
    subst q
    subst r
    have hzero : threePointCorrelationMatrix 0 0 0 0 =
        (0 : Matrix (Fin 3) (Fin 3) ℝ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [threePointCorrelationMatrix]
    rw [hzero]
    exact Matrix.PosSemidef.zero
  · have hdpos : 0 < d := lt_of_le_of_ne hd0 (Ne.symm hd)
    by_cases hp : p < d
    · exact (threePointCorrelationMatrix_posSemidef_iff hdpos hp0 hp).2 hdet
    · have hpeq : p = d := le_antisymm hpd (le_of_not_gt hp)
      have hqzero : q = 0 := by nlinarith
      have hrzero : r = 0 := by linarith
      subst p
      subst q
      subst r
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
        (threePointCorrelationMatrix_isHermitian d d 0 0)
      intro v
      simp [threePointCorrelationMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      nlinarith [sq_nonneg (v 0 + v 1), sq_nonneg (v 2)]

end HilbertMetric
