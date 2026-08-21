/-
# Chen--Gupta--Li Class-II left critical-line witness

The CGL Class-II branch is the shifted left vertical contour, where the
Dirichlet L-function lies on the critical line.  This module converts the
existing right-safe-line alternative and proved left-edge convergence into a
literal finite left-line integral witness.  It does not yet impose the
source's logarithmic cutoff or extract the local L-value lower bound.

No RH, GRH, zero-density, zero-detection, large-value, or moment premise is
supplied by callers.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveZeroRows

open Complex Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- **Chen--Gupta--Li Section 12.1–12.2:** every certified primitive Class-I
zero forces the normalized dyadic tail witness, or a finite truncation of the
actual left critical-line Mellin integral above a closed threshold. -/
theorem cglPrimitiveClassI_normalizedDyadicBlock_or_exists_leftLineIntegral_large
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
      ∃ K : ℕ, Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 ≤
        ‖(1 / (2 * Real.pi) : ℝ) •
          (∫ t in (-((K + 1 : ℕ) : ℝ))..((K + 1 : ℕ) : ℝ),
            cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
              (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
              ((((1 / 2 : ℝ) - z.1.1.re : ℝ) : ℂ) + (t : ℂ) * I))‖ := by
  rcases cglPrimitiveClassI_normalizedDyadicBlock_or_safeLineIntegral_large X n Y χ τ H z with
    htail | hsafe
  · exact Or.inl htail
  · right
    let E : ℝ := Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹))
    let J : ℂ := ∫ t : ℝ,
      cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
        (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
        ((2 : ℂ) + (t : ℂ) * I)
    let F : ℕ → ℂ := fun K =>
      (1 / (2 * Real.pi) : ℝ) •
        (∫ t in (-((K + 1 : ℕ) : ℝ))..((K + 1 : ℕ) : ℝ),
          cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
            (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
            ((((1 / 2 : ℝ) - z.1.1.re : ℝ) : ℂ) + (t : ℂ) * I))
    have hleft := tendsto_cglPrimitiveClassI_smoothedLeftLine_truncation X n Y χ τ H z
    change Tendsto _ atTop (𝓝 J) at hleft
    have hscaled : Tendsto F atTop (𝓝 ((1 / (2 * Real.pi) : ℝ) • J)) := by
      simpa only [F] using hleft.const_smul (1 / (2 * Real.pi) : ℝ)
    have hEpos : 0 < E := Real.exp_pos _
    rcases Metric.tendsto_atTop.1 hscaled.norm (E / 4) (by positivity) with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    have hdist := hK K le_rfl
    rw [Real.dist_eq] at hdist
    have hlow := (abs_lt.mp hdist).1
    change E / 2 ≤ ‖(1 / (2 * Real.pi) : ℝ) • J‖ at hsafe
    change E / 4 ≤ ‖F K‖
    nlinarith

end RHTower
