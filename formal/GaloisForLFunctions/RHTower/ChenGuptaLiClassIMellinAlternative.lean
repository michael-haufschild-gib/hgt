/-
# Chen--Gupta--Li Class-I Mellin alternative

Closed alternative extracted from the Section 12.1 exact formula. A certified
primitive Class-I zero forces either the genuine shifted coefficient tail or
the normalized safe-line Mellin integral to retain half the smoothed unit atom.
-/
import GaloisForLFunctions.RHTower.ChenGuptaLiClassIMellinNormalization

open Complex Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- **Chen--Gupta--Li, Section 12.1: closed Class-I Mellin alternative.**
At every certified primitive Class-I zero, either the actual shifted detector
tail or the normalized critical-line Mellin integral has norm at least half of
the smoothed unit atom. -/
theorem cglPrimitiveClassI_tail_or_safeLineIntegral_large
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 2 ≤
        ‖coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X n χ.1.1
          (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H z))
          ((Y + 1 : ℕ) : ℝ)⁻¹‖ ∨
      Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 2 ≤
        ‖(1 / (2 * Real.pi) : ℝ) • (∫ t : ℝ,
          cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
            (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
            ((2 : ℂ) + (t : ℂ) * I))‖ := by
  have htail := cglPrimitiveClassI_mellin_initialLine_tail_identity X n Y χ τ H z
  have hsafe := cglPrimitiveClassI_mellinInv_eq_safeLineIntegral X n Y χ τ H z
  have heq :
      Complex.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) +
          coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X n χ.1.1
            (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H z))
            ((Y + 1 : ℕ) : ℝ)⁻¹ =
        (1 / (2 * Real.pi) : ℝ) • (∫ t : ℝ,
          cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
            (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
            ((2 : ℂ) + (t : ℂ) * I)) := by
    rw [← hsafe]
    exact htail.symm
  have hsub : Complex.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) =
        (1 / (2 * Real.pi) : ℝ) • (∫ t : ℝ,
          cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
            (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
            ((2 : ℂ) + (t : ℂ) * I)) -
          coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X n χ.1.1
            (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H z))
            ((Y + 1 : ℕ) : ℝ)⁻¹ := by
    linear_combination heq
  have htriangle :
      Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) ≤
        ‖coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X n χ.1.1
          (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H z))
          ((Y + 1 : ℕ) : ℝ)⁻¹‖ +
        ‖(1 / (2 * Real.pi) : ℝ) • (∫ t : ℝ,
          cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
            (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
            ((2 : ℂ) + (t : ℂ) * I))‖ := by
    calc
      Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) =
          ‖Complex.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹))‖ := by
        rw [Complex.norm_exp]
        norm_num [Complex.normSq_apply]
      _ = ‖(1 / (2 * Real.pi) : ℝ) • (∫ t : ℝ,
          cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
            (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
            ((2 : ℂ) + (t : ℂ) * I)) -
          coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X n χ.1.1
            (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H z))
            ((Y + 1 : ℕ) : ℝ)⁻¹‖ := by rw [hsub]
      _ ≤ _ := by
        simpa [add_comm] using
          (norm_sub_le
            ((1 / (2 * Real.pi) : ℝ) • (∫ t : ℝ,
              cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
                (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
                ((2 : ℂ) + (t : ℂ) * I)))
            (coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X n χ.1.1
              (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H z))
              ((Y + 1 : ℕ) : ℝ)⁻¹))
  by_contra h
  push Not at h
  linarith

end RHTower
