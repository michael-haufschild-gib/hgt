/-
# Chen--Gupta--Li Class-I normalized dyadic witness

Closed Class-I witness in the exact normalized character/ordinate matrix
coordinates required by CGL's large-value argument.
-/
import GaloisForLFunctions.RHTower.ChenGuptaLiClassITailRescaling

open Complex Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

/-- **Chen--Gupta--Li, Section 12.1--12.3: normalized Class-I dyadic
witness.** Every certified primitive Class-I zero forces either a finite CGL
character/ordinate polynomial with unit-ball coefficient vector to exceed its
explicit scaled threshold, or the normalized critical-line Mellin integral to
be large. -/
theorem cglPrimitiveClassI_normalizedDyadicBlock_or_safeLineIntegral_large
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    (∃ L : ℕ, ∃ r : Fin L,
      cglShiftedTailDyadicCoefficientScale X (2 ^ r.1)
        (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H z)
        ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ *
          (Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / (4 * (L : ℝ))) ≤
        ‖cglShiftedTailDyadicScaledPolynomial X (2 ^ r.1) n χ.1.1
          (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H z)
          ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩‖) ∨
      Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 2 ≤
        ‖(1 / (2 * Real.pi) : ℝ) • (∫ t : ℝ,
          cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
            (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
            ((2 : ℂ) + (t : ℂ) * I))‖ := by
  let s : CGLRightHalfPlanePoint :=
    cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H z
  let x : CGLPositiveSmoothingScale := ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩
  rcases cglPrimitiveClassI_dyadicIncrement_or_safeLineIntegral_large X n Y χ τ H z with
    ⟨L, r, hr⟩ | hsafe
  · left
    refine ⟨L, r, ?_⟩
    change cglShiftedTailDyadicCoefficientScale X (2 ^ r.1) s x *
        (Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / (4 * (L : ℝ))) ≤
      ‖cglShiftedTailDyadicScaledPolynomial X (2 ^ r.1) n χ.1.1 s x‖
    have hscale : 0 ≤ cglShiftedTailDyadicCoefficientScale X (2 ^ r.1) s x := by
      unfold cglShiftedTailDyadicCoefficientScale
      positivity
    have hpoly : cglShiftedTailDyadicScaledPolynomial X (2 ^ r.1) n χ.1.1 s x =
        (cglShiftedTailDyadicCoefficientScale X (2 ^ r.1) s x : ℂ) *
          cglShiftedDetectorTailDyadicIncrement X n χ.1.1 s x r.1 := by
      rw [cglShiftedTailDyadicScaledPolynomial_eq_scale_mul,
        ← cglShiftedDetectorTailDyadicIncrement_eq_characterPolynomial]
    rw [hpoly, norm_mul, Complex.norm_real, Real.norm_of_nonneg hscale]
    change Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / (4 * (L : ℝ)) ≤
      ‖cglShiftedDetectorTailDyadicIncrement X n χ.1.1 s x r.1‖ at hr
    exact mul_le_mul_of_nonneg_left hr hscale
  · exact Or.inr hsafe

end RHTower
