import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsNormalizedOddProfile

/-!
# Mirrored radii detect the first asymmetric energy term

Opposite interior coordinates share the quartic leading profile. Their
actual Gibbs energy difference is fifth order. The symmetric average
cancels this first odd correction, while the mirror difference divided
by barrier height and actual peak displacement has a universal limit.
-/
noncomputable section
open Real Filter Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAGibbsMirrorDifference (w φ τ l ψ : ℝ) : ℝ :=
  egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
    (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeAInteriorRadius w φ τ ψ) -
  egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
    (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeAInteriorRadius w φ τ (-ψ))

theorem egbFixedChargeAGibbsMirrorDifference_gap_difference (w φ τ l ψ : ℝ) :
    egbFixedChargeAGibbsMirrorDifference w φ τ l ψ =
      egbFixedChargeAInteriorGibbsGap w φ τ l ψ - egbFixedChargeAInteriorGibbsGap w φ τ l (-ψ) := by
  unfold egbFixedChargeAGibbsMirrorDifference egbFixedChargeAInteriorGibbsGap
  ring

theorem egbFixedChargeAGibbsMirrorDifference_reference_independent (w φ τ l₁ l₂ ψ : ℝ) :
    egbFixedChargeAGibbsMirrorDifference w φ τ l₁ ψ = egbFixedChargeAGibbsMirrorDifference w φ τ l₂ ψ := by
  rw [egbFixedChargeAGibbsMirrorDifference_gap_difference, egbFixedChargeAGibbsMirrorDifference_gap_difference,
    egbFixedChargeAInteriorGibbsGap_reference_independent w φ τ l₁ l₂ ψ,
    egbFixedChargeAInteriorGibbsGap_reference_independent w φ τ l₁ l₂ (-ψ)]

theorem egbFixedChargeAGibbsMirrorDifference_odd (w φ τ l ψ : ℝ) :
    egbFixedChargeAGibbsMirrorDifference w φ τ l (-ψ) = -egbFixedChargeAGibbsMirrorDifference w φ τ l ψ := by
  unfold egbFixedChargeAGibbsMirrorDifference
  rw [neg_neg]
  ring

theorem egbFixedChargeAGibbsMirrorDifference_fifth_order_limit (w φ l ψ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAGibbsMirrorDifference w φ τ l ψ / egbCoexistenceASymmetricRatio τ ^ 5)
      atBot (𝓝 (2 * egbFixedChargeAGibbsOddCoefficient w φ * sin ψ * cos ψ ^ 4)) := by
  have h := (egbFixedChargeAInteriorGibbsGap_fifth_order_limit w φ l ψ).sub
    (egbFixedChargeAInteriorGibbsGap_fifth_order_limit w φ l (-ψ))
  simp only [sin_neg, cos_neg] at h
  have he : egbFixedChargeAGibbsOddCoefficient w φ * sin ψ * cos ψ ^ 4 -
      egbFixedChargeAGibbsOddCoefficient w φ * (-sin ψ) * cos ψ ^ 4 =
      2 * egbFixedChargeAGibbsOddCoefficient w φ * sin ψ * cos ψ ^ 4 := by ring
  rw [he] at h
  convert h using 1
  funext τ
  rw [egbFixedChargeAGibbsMirrorDifference_gap_difference]
  ring

theorem egbFixedChargeAGibbsSymmetricAverage_fifth_zero_limit (w φ l ψ : ℝ) :
    Tendsto (fun τ => ((egbFixedChargeAInteriorGibbsGap w φ τ l ψ + egbFixedChargeAInteriorGibbsGap w φ τ l (-ψ)) / 2 -
      egbFixedChargeAGibbsBarrierCoefficient w φ * cos ψ ^ 4 * egbCoexistenceASymmetricRatio τ ^ 4) /
      egbCoexistenceASymmetricRatio τ ^ 5) atBot (𝓝 (0 : ℝ)) := by
  have h := ((egbFixedChargeAInteriorGibbsGap_fifth_order_limit w φ l ψ).add
    (egbFixedChargeAInteriorGibbsGap_fifth_order_limit w φ l (-ψ))).div_const 2
  simp only [sin_neg, cos_neg] at h
  have he : (egbFixedChargeAGibbsOddCoefficient w φ * sin ψ * cos ψ ^ 4 +
      egbFixedChargeAGibbsOddCoefficient w φ * (-sin ψ) * cos ψ ^ 4) / 2 = 0 := by ring
  rw [he] at h
  convert h using 1
  funext τ
  ring

theorem egbFixedChargeAGibbsMirrorDifference_normalized_first_limit (w φ l₁ l₂ ψ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAGibbsMirrorDifference w φ τ l₁ ψ / egbFixedChargeAGibbsBarrier w φ τ l₂) /
      egbCoexistenceASymmetricRatio τ)
      atBot (𝓝 (8 * egbFixedChargeAMiddleMeanCorrection φ * sin ψ * cos ψ ^ 4)) := by
  have h := (egbFixedChargeAInteriorGibbsGap_normalized_first_correction_limit w φ l₁ l₂ ψ).sub
    (egbFixedChargeAInteriorGibbsGap_normalized_first_correction_limit w φ l₁ l₂ (-ψ))
  simp only [sin_neg, cos_neg] at h
  have he : 4 * egbFixedChargeAMiddleMeanCorrection φ * sin ψ * cos ψ ^ 4 -
      4 * egbFixedChargeAMiddleMeanCorrection φ * (-sin ψ) * cos ψ ^ 4 =
      8 * egbFixedChargeAMiddleMeanCorrection φ * sin ψ * cos ψ ^ 4 := by ring
  rw [he] at h
  convert h using 1
  funext τ
  rw [egbFixedChargeAGibbsMirrorDifference_gap_difference]
  ring

theorem egbFixedChargeAGibbsMirrorDifference_peak_displacement_limit (w φ l₁ l₂ ψ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAGibbsMirrorDifference w φ τ l₁ ψ / egbFixedChargeAGibbsBarrier w φ τ l₂) /
      egbFixedChargeAMiddleGapCoordinate τ φ)
      atBot (𝓝 (8 * sin ψ * cos ψ ^ 4)) := by
  have h := (egbFixedChargeAInteriorGibbsGap_peak_displacement_correction_limit w φ l₁ l₂ ψ).sub
    (egbFixedChargeAInteriorGibbsGap_peak_displacement_correction_limit w φ l₁ l₂ (-ψ))
  simp only [sin_neg, cos_neg] at h
  have he : 4 * sin ψ * cos ψ ^ 4 - 4 * (-sin ψ) * cos ψ ^ 4 = 8 * sin ψ * cos ψ ^ 4 := by ring
  rw [he] at h
  convert h using 1
  funext τ
  rw [egbFixedChargeAGibbsMirrorDifference_gap_difference]
  ring

end GaloisForLFunctions.HTGeometry
