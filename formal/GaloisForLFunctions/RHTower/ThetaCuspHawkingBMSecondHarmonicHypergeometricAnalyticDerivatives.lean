import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicHypergeometricFormalODE

/-!
# Analytic derivatives of the BM complementary hypergeometric factor

The BM complementary `++` hypergeometric series has radius one. Formal-multilinear-series
differentiation therefore supplies its first derivative everywhere in the open unit disk. Radius
monotonicity for the derivative series and continuous-linear evaluation at `1` supply the second
derivative on the same disk.

This module removes the local regularity gap before converting the formal Euler identity to the
analytic Gauss ODE.
-/

open Complex Real Set Filter Topology Nat FormalMultilinearSeries

namespace RHTower

noncomputable section

/-- First derivative-series value of the complementary `++` hypergeometric factor. -/
def d4BMPlusPlusComplementaryHypergeometricFirstDerivative
    (n : ℕ) (chi z : ℂ) : ℂ :=
  ((d4BMPlusPlusComplementaryHypergeometricSeries n chi).derivSeries.sum z) 1

/-- Second derivative-series value of the complementary `++` hypergeometric factor. -/
def d4BMPlusPlusComplementaryHypergeometricSecondDerivative
    (n : ℕ) (chi z : ℂ) : ℂ :=
  (((d4BMPlusPlusComplementaryHypergeometricSeries n chi).derivSeries.derivSeries.sum z)
    1) 1

/-- The first derivative-series value is the actual derivative throughout the open unit disk. -/
theorem hasDerivAt_d4BMPlusPlusComplementaryHypergeometricFactor
    (n : ℕ) (chi z : ℂ) (hchi : chi.re ≠ 0) (hz : ‖z‖ₑ < 1) :
    HasDerivAt (d4BMPlusPlusComplementaryHypergeometricFactor n chi)
      (d4BMPlusPlusComplementaryHypergeometricFirstDerivative n chi z) z := by
  let p := d4BMPlusPlusComplementaryHypergeometricSeries n chi
  have hzp : ‖z‖ₑ < p.radius := by
    rw [d4BMPlusPlusComplementaryHypergeometricSeries_radius_eq_one n chi hchi]
    exact hz
  change HasDerivAt p.sum ((p.derivSeries.sum z) 1) z
  exact (p.hasFDerivAt_sum hzp).hasDerivAt

/-- The second derivative-series value differentiates the first throughout the open unit disk. -/
theorem hasDerivAt_d4BMPlusPlusComplementaryHypergeometricFirstDerivative
    (n : ℕ) (chi z : ℂ) (hchi : chi.re ≠ 0) (hz : ‖z‖ₑ < 1) :
    HasDerivAt
      (d4BMPlusPlusComplementaryHypergeometricFirstDerivative n chi)
      (d4BMPlusPlusComplementaryHypergeometricSecondDerivative n chi z) z := by
  let p := d4BMPlusPlusComplementaryHypergeometricSeries n chi
  let q := p.derivSeries
  have hzp : ‖z‖ₑ < p.radius := by
    rw [d4BMPlusPlusComplementaryHypergeometricSeries_radius_eq_one n chi hchi]
    exact hz
  have hzq : ‖z‖ₑ < q.radius :=
    lt_of_lt_of_le hzp p.radius_le_radius_derivSeries
  have hq := q.hasFDerivAt_sum hzq
  have heval := hq.clm_apply (hasFDerivAt_const (1 : ℂ) z)
  change HasDerivAt (fun w : ℂ => (q.sum w) 1)
    (((q.derivSeries.sum z) 1) 1) z
  simpa using heval.hasDerivAt

/-- Complementary `++` hypergeometric factor is twice differentiable inside its unit disk. -/
theorem d4BMPlusPlusComplementaryHypergeometricFactor_twiceDifferentiableAt
    (n : ℕ) (chi z : ℂ) (hchi : chi.re ≠ 0) (hz : ‖z‖ₑ < 1) :
    DifferentiableAt ℂ (d4BMPlusPlusComplementaryHypergeometricFactor n chi) z ∧
      DifferentiableAt ℂ
        (d4BMPlusPlusComplementaryHypergeometricFirstDerivative n chi) z := by
  exact ⟨(hasDerivAt_d4BMPlusPlusComplementaryHypergeometricFactor
      n chi z hchi hz).differentiableAt,
    (hasDerivAt_d4BMPlusPlusComplementaryHypergeometricFirstDerivative
      n chi z hchi hz).differentiableAt⟩

/-- Every Xi-fibre complementary `++` factor is twice differentiable in the open unit disk. -/
theorem d4BMXiPlusPlusComplementaryHypergeometricFactor_twiceDifferentiableAt
    (n : ℕ) (q : XiZeroCopy) (z : ℂ) (hz : ‖z‖ₑ < 1) :
    DifferentiableAt ℂ
        (d4BMPlusPlusComplementaryHypergeometricFactor
          n (d4BMXiMixedHorizonAngularMomentum q)) z ∧
      DifferentiableAt ℂ
        (d4BMPlusPlusComplementaryHypergeometricFirstDerivative
          n (d4BMXiMixedHorizonAngularMomentum q)) z := by
  exact d4BMPlusPlusComplementaryHypergeometricFactor_twiceDifferentiableAt
    n _ z (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q) hz

end

end RHTower
