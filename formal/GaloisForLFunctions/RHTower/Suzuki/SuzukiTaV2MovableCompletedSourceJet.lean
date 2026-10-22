import GaloisForLFunctions.RHTower.Suzuki.SuzukiMovableSchurCovariantSecondJet
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaV2ActualSecondDefectIntegral

/-!
# Literal completed-source form of movable Suzuki covariant jet

The movable Schwarz--Pick jet is rewritten here as a quotient built only from Fourier readouts of
Suzuki's actual completed finite-aperture covariance source.  Prime, polar, and Gamma terms remain
coupled inside the quotient before scalarization.
-/

open Complex

namespace RHTower

noncomputable section

/-- Livšic quotient formed directly from the literal completed covariance Fourier source. -/
def suzukiTaV2CompletedCovarianceLivsic
    (a : SuzukiPositiveAperture) (z : ℂ) : ℂ :=
  ((z - I) * suzukiTaV2CompletedCovarianceFourier a z) /
    ((z + I) * suzukiTaV2CompletedCovarianceFourier a (-z))

/-- The source quotient is exactly Suzuki's actual finite-aperture Livšic characteristic. -/
theorem suzukiTaV2CompletedCovarianceLivsic_eq_actual
    (a : SuzukiPositiveAperture) :
    suzukiTaV2CompletedCovarianceLivsic a = suzukiTaV2Livsic a := by
  funext z
  rw [suzukiTaV2CompletedCovarianceLivsic, suzukiTaV2Livsic,
    GaloisForLFunctions.RHTower.suzukiLivsicQuotient,
    suzukiTaV2CharacteristicA, suzukiTaV2CharacteristicE,
    suzukiTaPhysicalFourier_minusDeficiency_reflection,
    suzukiTaPhysicalFourier_plus_eq_completedCovarianceFourier,
    suzukiTaPhysicalFourier_plus_eq_completedCovarianceFourier]

/-- Source Gram numerator of the movable Schur defect.  Both channels are read from the same
completed finite-aperture covariance carrier before forming their signed difference. -/
def suzukiTaV2CompletedCovarianceSchurDefectNumerator
    (a : SuzukiPositiveAperture) (z : ℂ) : ℂ :=
  let N := (z - I) * suzukiTaV2CompletedCovarianceFourier a z
  let E := (z + I) * suzukiTaV2CompletedCovarianceFourier a (-z)
  (starRingEnd ℂ) E * E - (starRingEnd ℂ) N * N

/-- The source numerator is exactly the signed gap of the two characteristic Gram energies. -/
theorem suzukiTaV2CompletedCovarianceSchurDefectNumerator_eq_norm_gap
    (a : SuzukiPositiveAperture) (z : ℂ) :
    suzukiTaV2CompletedCovarianceSchurDefectNumerator a z =
      ((‖(z + I) * suzukiTaV2CompletedCovarianceFourier a (-z)‖ ^ (2 : ℕ) -
        ‖(z - I) * suzukiTaV2CompletedCovarianceFourier a z‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [suzukiTaV2CompletedCovarianceSchurDefectNumerator]
  rw [← Complex.normSq_eq_conj_mul_self,
    ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  norm_cast

/-- Strict source positivity of the completed covariance Gram gap throughout the upper
half-plane.  This is the literal source numerator, not positivity imposed on a scalar reporter. -/
theorem suzukiTaV2CompletedCovarianceSchurDefectNumerator_re_pos
    (a : SuzukiPositiveAperture) {z : ℂ} (hz : 0 < z.im) :
    0 < (suzukiTaV2CompletedCovarianceSchurDefectNumerator a z).re := by
  have hlt := GaloisForLFunctions.RHTower.norm_lt_of_suzukiAllAngleRealZeros
    (differentiable_suzukiTaV2CharacteristicA a).continuous
    (differentiable_suzukiTaV2CharacteristicE a).continuous
    (suzukiTaV2CharacteristicA_I a) (suzukiTaV2_allAngleRealZeros a) hz
  rw [suzukiTaV2CharacteristicA, suzukiTaV2CharacteristicE,
    suzukiTaPhysicalFourier_minusDeficiency_reflection,
    suzukiTaPhysicalFourier_plus_eq_completedCovarianceFourier,
    suzukiTaPhysicalFourier_plus_eq_completedCovarianceFourier] at hlt
  rw [suzukiTaV2CompletedCovarianceSchurDefectNumerator_eq_norm_gap]
  change 0 <
    ‖(z + I) * suzukiTaV2CompletedCovarianceFourier a (-z)‖ ^ (2 : ℕ) -
      ‖(z - I) * suzukiTaV2CompletedCovarianceFourier a z‖ ^ (2 : ℕ)
  nlinarith [norm_nonneg
    ((z - I) * suzukiTaV2CompletedCovarianceFourier a z),
    norm_nonneg
      ((z + I) * suzukiTaV2CompletedCovarianceFourier a (-z))]

/-- Exact completed-source quotient for the movable Schur defect.  Denominator nonvanishing and
numerator positivity both follow from Suzuki's finite all-angle spectral theorem. -/
theorem suzukiTaV2CompletedCovarianceLivsic_schurDefect_eq_sourceRatio
    (a : SuzukiPositiveAperture) {z : ℂ} (hz : 0 < z.im) :
    1 - (starRingEnd ℂ) (suzukiTaV2CompletedCovarianceLivsic a z) *
          suzukiTaV2CompletedCovarianceLivsic a z =
      suzukiTaV2CompletedCovarianceSchurDefectNumerator a z /
        ((starRingEnd ℂ)
            ((z + I) * suzukiTaV2CompletedCovarianceFourier a (-z)) *
          ((z + I) * suzukiTaV2CompletedCovarianceFourier a (-z))) := by
  let N := (z - I) * suzukiTaV2CompletedCovarianceFourier a z
  let E := (z + I) * suzukiTaV2CompletedCovarianceFourier a (-z)
  have hEeq : E = suzukiTaV2CharacteristicE a z := by
    dsimp only [E]
    rw [suzukiTaV2CharacteristicE,
      suzukiTaPhysicalFourier_minusDeficiency_reflection,
      suzukiTaPhysicalFourier_plus_eq_completedCovarianceFourier]
  have hE : E ≠ 0 := by
    rw [hEeq]
    exact GaloisForLFunctions.RHTower.suzukiLivsic_denominator_ne_zero
      (differentiable_suzukiTaV2CharacteristicA a).continuous
      (differentiable_suzukiTaV2CharacteristicE a).continuous
      (suzukiTaV2CharacteristicA_I a) (suzukiTaV2_allAngleRealZeros a) hz
  change 1 - (starRingEnd ℂ) (N / E) * (N / E) =
    ((starRingEnd ℂ) E * E - (starRingEnd ℂ) N * N) /
      ((starRingEnd ℂ) E * E)
  rw [map_div₀]
  field_simp [hE]

/-- Exact defect-faithful wall for Suzuki's literal completed covariance source.  Its right side
retains the moving Schur-defect scale and subtracts the full first-jet energy; neither term is
discarded before the prime--polar--Gamma source is scalarized. -/
theorem norm_suzukiTaV2CompletedCovarianceLivsic_defectClearedSecondJet_le
    (a : SuzukiPositiveAperture) {c : ℝ} (hc : 0 < c) :
    let theta := suzukiTaV2CompletedCovarianceLivsic a
    let alpha := theta ((c : ℂ) * I)
    let D := 1 - (starRingEnd ℂ) alpha * alpha
    let P := deriv theta ((c : ℂ) * I) * (2 * (c : ℂ) * I)
    let Q := iteratedDeriv 2 theta ((c : ℂ) * I) *
        (2 * (c : ℂ) * I) ^ (2 : ℕ) +
      deriv theta ((c : ℂ) * I) * (4 * (c : ℂ) * I)
    ‖2 * (starRingEnd ℂ) alpha * P ^ (2 : ℕ) + D * Q‖ ≤
      2 * (‖D‖ ^ (2 : ℕ) - ‖P‖ ^ (2 : ℕ)) := by
  rw [suzukiTaV2CompletedCovarianceLivsic_eq_actual]
  apply norm_suzukiMovableSchur_defectClearedSecondJet_le hc
  · exact differentiableOn_suzukiTaV2Livsic_upperHalfPlane a
  · exact fun z hz => norm_suzukiTaV2Livsic_lt_one a hz

/-- Defect-normalized source budget for the literal completed covariance quotient.  It gives a
uniformly nonsingular landing for the covariant second jet while preserving the negative
first-jet square generated by prime--polar--Gamma cancellation. -/
theorem norm_suzukiTaV2CompletedCovarianceLivsic_defectNormalizedSecondJet_budget
    (a : SuzukiPositiveAperture) {c : ℝ} (hc : 0 < c) :
    let theta := suzukiTaV2CompletedCovarianceLivsic a
    let alpha := theta ((c : ℂ) * I)
    let D := 1 - (starRingEnd ℂ) alpha * alpha
    let P := deriv theta ((c : ℂ) * I) * (2 * (c : ℂ) * I)
    let Q := iteratedDeriv 2 theta ((c : ℂ) * I) *
        (2 * (c : ℂ) * I) ^ (2 : ℕ) +
      deriv theta ((c : ℂ) * I) * (4 * (c : ℂ) * I)
    ‖Q + (2 * (starRingEnd ℂ) alpha / D) * P ^ (2 : ℕ)‖ +
        2 * ‖P‖ ^ (2 : ℕ) / ‖D‖ ≤ 2 * ‖D‖ := by
  rw [suzukiTaV2CompletedCovarianceLivsic_eq_actual]
  apply norm_suzukiMovableSchur_defectNormalizedSecondJet_budget hc
  · exact differentiableOn_suzukiTaV2Livsic_upperHalfPlane a
  · exact fun z hz => norm_suzukiTaV2Livsic_lt_one a hz

/-- Aperture- and height-uniform control of the defect-normalized second jet of Suzuki's literal
completed covariance source.  Prime--polar--Gamma coupling remains inside `theta`, `D`, `P`, and
`Q`; only the exact Schur covariance correction is removed. -/
theorem norm_suzukiTaV2CompletedCovarianceLivsic_defectNormalizedSecondJet_le_two
    (a : SuzukiPositiveAperture) {c : ℝ} (hc : 0 < c) :
    let theta := suzukiTaV2CompletedCovarianceLivsic a
    let alpha := theta ((c : ℂ) * I)
    let D := 1 - (starRingEnd ℂ) alpha * alpha
    let P := deriv theta ((c : ℂ) * I) * (2 * (c : ℂ) * I)
    let Q := iteratedDeriv 2 theta ((c : ℂ) * I) *
        (2 * (c : ℂ) * I) ^ (2 : ℕ) +
      deriv theta ((c : ℂ) * I) * (4 * (c : ℂ) * I)
    ‖Q + (2 * (starRingEnd ℂ) alpha / D) * P ^ (2 : ℕ)‖ ≤ 2 := by
  rw [suzukiTaV2CompletedCovarianceLivsic_eq_actual]
  apply norm_suzukiMovableSchur_defectNormalizedSecondJet_le_two hc
  · exact differentiableOn_suzukiTaV2Livsic_upperHalfPlane a
  · exact fun z hz => norm_suzukiTaV2Livsic_lt_one a hz

/-- Uniform covariant two-jet control at every positive symmetric Mellin shift, stated entirely in
the literal completed prime--polar--Gamma source quotient. -/
theorem norm_suzukiTaV2CompletedCovarianceLivsic_covariantSecondJet_le
    (a : SuzukiPositiveAperture) {c : ℝ} (hc : 0 < c) :
    ‖(2 * (starRingEnd ℂ) (suzukiTaV2CompletedCovarianceLivsic a ((c : ℂ) * I)) /
          (1 - (starRingEnd ℂ)
              (suzukiTaV2CompletedCovarianceLivsic a ((c : ℂ) * I)) *
            suzukiTaV2CompletedCovarianceLivsic a ((c : ℂ) * I)) ^ (2 : ℕ)) *
          (deriv (suzukiTaV2CompletedCovarianceLivsic a) ((c : ℂ) * I) *
            (2 * (c : ℂ) * I)) ^ (2 : ℕ) +
        (1 - (starRingEnd ℂ)
              (suzukiTaV2CompletedCovarianceLivsic a ((c : ℂ) * I)) *
            suzukiTaV2CompletedCovarianceLivsic a ((c : ℂ) * I))⁻¹ *
          (iteratedDeriv 2 (suzukiTaV2CompletedCovarianceLivsic a)
                ((c : ℂ) * I) * (2 * (c : ℂ) * I) ^ (2 : ℕ) +
            deriv (suzukiTaV2CompletedCovarianceLivsic a) ((c : ℂ) * I) *
              (4 * (c : ℂ) * I))‖ ≤
      2 * (1 -
        ‖(2 * (c : ℂ) * I *
            deriv (suzukiTaV2CompletedCovarianceLivsic a) ((c : ℂ) * I)) /
          (1 - (starRingEnd ℂ)
              (suzukiTaV2CompletedCovarianceLivsic a ((c : ℂ) * I)) *
            suzukiTaV2CompletedCovarianceLivsic a ((c : ℂ) * I))‖ ^ (2 : ℕ)) := by
  rw [suzukiTaV2CompletedCovarianceLivsic_eq_actual]
  exact norm_suzukiTaV2MovableSchurCovariantSecondJet_le a hc

/-- Denominator-cleared movable wall law for the literal completed covariance quotient.  Bound is
uniform in aperture and positive Mellin-shift height, with no quotient normalization remaining. -/
theorem norm_suzukiTaV2CompletedCovarianceLivsic_denominatorClearedSecondJet_le_two
    (a : SuzukiPositiveAperture) {c : ℝ} (hc : 0 < c) :
    let theta := suzukiTaV2CompletedCovarianceLivsic a
    let alpha := theta ((c : ℂ) * I)
    let D := 1 - (starRingEnd ℂ) alpha * alpha
    let P := deriv theta ((c : ℂ) * I) * (2 * (c : ℂ) * I)
    let Q := iteratedDeriv 2 theta ((c : ℂ) * I) *
        (2 * (c : ℂ) * I) ^ (2 : ℕ) +
      deriv theta ((c : ℂ) * I) * (4 * (c : ℂ) * I)
    ‖2 * (starRingEnd ℂ) alpha * P ^ (2 : ℕ) + D * Q‖ ≤ 2 := by
  rw [suzukiTaV2CompletedCovarianceLivsic_eq_actual]
  apply norm_suzukiMovableSchur_denominatorClearedSecondJet_le_two hc
  · exact differentiableOn_suzukiTaV2Livsic_upperHalfPlane a
  · exact fun z hz => norm_suzukiTaV2Livsic_lt_one a hz

end
end RHTower
