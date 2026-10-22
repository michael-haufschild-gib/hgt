import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinPolynomialWhittakerTail

/-!
# Square-root-normalized completed Eisenstein Whittaker tails

The literal nonconstant Eisenstein mode contains `sqrt(Y)`.  Integer-height jet admission alone
therefore does not yet identify its normalization.  Factoring

`sqrt(Y) * Y^m = (sqrt(Y)/Y) * Y^(m+1)`

reduces the exact square-root-normalized tail to the preceding polynomial tail.  The scalar ratio
tends to zero because it equals `1/sqrt(Y)` on the positive cusp.  Thus every actual
`sqrt(Y) n^j Y^m K_nu(2*pi*nY)` packet vanishes for arbitrary fixed degrees.

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [HC94] [SQRT WHITTAKER TAIL]`
-/

open Complex Real Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Literal square-root-normalized Eisenstein Bessel tail. -/
def d4BMCompletedEisensteinSqrtPolynomialBesselJetTail
    (u nu : ℂ) (indexDegree heightDegree : ℕ) (Y : ℝ) : ℂ :=
  ∑' N : ℕ,
    (d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
      ((N + 1 : ℕ) : ℂ) ^ indexDegree) *
      (Real.sqrt Y : ℂ) * (Y : ℂ) ^ heightDegree *
      GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
        (2 * Real.pi * ((N : ℝ) + 1) * Y) nu

/-- On the positive cusp, square-root normalization factors through the next integer-height jet. -/
theorem d4BM_sqrtPolynomialBesselJetTail_eq_ratio_mul
    (u nu : ℂ) (indexDegree heightDegree : ℕ) {Y : ℝ} (hY : 0 < Y) :
    d4BMCompletedEisensteinSqrtPolynomialBesselJetTail
        u nu indexDegree heightDegree Y =
      ((Real.sqrt Y / Y : ℝ) : ℂ) *
        d4BMCompletedEisensteinPolynomialBesselJetTail
          u nu indexDegree (heightDegree + 1) Y := by
  rw [d4BMCompletedEisensteinSqrtPolynomialBesselJetTail,
    d4BMCompletedEisensteinPolynomialBesselJetTail, ← tsum_mul_left]
  apply tsum_congr
  intro N
  rw [pow_succ]
  push_cast
  field_simp [hY.ne']

/-- The literal square-root normalization divided by height tends to zero at the cusp. -/
theorem d4BM_tendsto_sqrt_div_self_atTop_zero :
    Tendsto (fun Y : ℝ => Real.sqrt Y / Y) atTop (𝓝 0) := by
  have hinv : Tendsto (fun Y : ℝ => (Real.sqrt Y)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  apply hinv.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
  have hsqrt : Real.sqrt Y ≠ 0 := (Real.sqrt_pos.2 hY).ne'
  rw [div_eq_mul_inv]
  field_simp [hsqrt, hY.ne']
  exact (Real.sq_sqrt hY.le).symm

/-- Every literal square-root-normalized polynomial-index Eisenstein Whittaker tail vanishes. -/
theorem tendsto_d4BMCompletedEisensteinSqrtPolynomialBesselJetTail_atTop_zero
    (u nu : ℂ) (indexDegree heightDegree : ℕ) :
    Tendsto
      (d4BMCompletedEisensteinSqrtPolynomialBesselJetTail
        u nu indexDegree heightDegree) atTop (𝓝 0) := by
  have hratio : Tendsto (fun Y : ℝ => ((Real.sqrt Y / Y : ℝ) : ℂ)) atTop (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp d4BM_tendsto_sqrt_div_self_atTop_zero
  have htail := tendsto_d4BMCompletedEisensteinPolynomialBesselJetTail_atTop_zero
    u nu indexDegree (heightDegree + 1)
  have hprod := hratio.mul htail
  simp only [mul_zero] at hprod
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
  exact (d4BM_sqrtPolynomialBesselJetTail_eq_ratio_mul
    u nu indexDegree heightDegree hY).symm

end

end RHTower
