import GaloisForLFunctions.RHTower.CCMActualHeadMatchedSymmetricFirstMomentControl
import GaloisForLFunctions.RHTower.CCMArchimedeanComplexSmoothCore

/-!
# All-prime matched-cell convergence on the literal smooth CCM core

The exact CCM form domain has a source-faithful dense core of smooth compactly supported physical
heads.  Their Fourier transforms are Schwartz, hence have the single first moment required by the
matched symmetric-cell theorem.

Consequently both the even residual and the intact prime-minus-matched-polar family are absolutely
summable on every literal complex smooth-core vector.  This is the source-native application of
the fractional matched-cell gain: all-prime convergence is now closed on the dense CCM core.  The
remaining problem is extension/sign control for the completed producer, not convergence of its
prime--polar cells.
-/

open MeasureTheory Set
open scoped ENNReal InnerProduct FourierTransform SchwartzMap

noncomputable section

namespace RHTower

/-- A Schwartz density has finite absolute first moment after squaring. -/
theorem integrable_abs_mul_normSq_schwartzMap (F : SchwartzMap ℝ ℂ) :
    Integrable (fun xi : ℝ => |xi| * ‖F xi‖ ^ 2) := by
  let C : ℝ := SchwartzMap.seminorm ℂ 0 0 F
  let XF : SchwartzMap ℝ ℂ :=
    SchwartzMap.smulLeftCLM ℂ (fun xi : ℝ => (xi : ℂ)) F
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hXF : Integrable (fun xi : ℝ => ‖XF xi‖) := XF.integrable.norm
  have hmajor : Integrable (fun xi : ℝ => C * ‖XF xi‖) := hXF.const_mul C
  refine Integrable.mono' hmajor
    ((continuous_abs.mul (F.continuous.norm.pow 2)).aestronglyMeasurable) ?_
  filter_upwards with xi
  have hF : ‖F xi‖ ≤ C := SchwartzMap.norm_le_seminorm ℂ F xi
  have hXFpoint : ‖XF xi‖ = |xi| * ‖F xi‖ := by
    rw [show XF xi = (xi : ℂ) • F xi by
      exact SchwartzMap.smulLeftCLM_apply_apply (by fun_prop) F xi]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (abs_nonneg xi) (sq_nonneg _)), hXFpoint]
  calc
    |xi| * ‖F xi‖ ^ 2 = (|xi| * ‖F xi‖) * ‖F xi‖ := by ring
    _ ≤ (|xi| * ‖F xi‖) * C :=
      mul_le_mul_of_nonneg_left hF
        (mul_nonneg (abs_nonneg xi) (norm_nonneg _))
    _ = C * (|xi| * ‖F xi‖) := by ring

/-- Every literal complex smooth-core head satisfies the fractional first-moment condition. -/
theorem integrable_ccmComplexSmoothFormVector_fourierFirstMoment
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g)
    (hgaper : tsupport g ⊆ Ioo (-a.1) a.1) :
    Integrable (fun xi : ℝ =>
      |xi| * ‖(fourierUnitary
        (ccmArchimedeanFormToAperture a
          (ccmComplexSmoothFormVector a g hgdiff hgsupp hgaper) : SoninL2) :
            ℝ → ℂ) xi‖ ^ 2) := by
  let G : SchwartzMap ℝ ℂ := suzukiComplexTestSchwartz g hgdiff hgsupp
  let F : SchwartzMap ℝ ℂ := 𝓕 G
  let f : SoninL2 := ccmArchimedeanFormToAperture a
    (ccmComplexSmoothFormVector a g hgdiff hgsupp hgaper)
  have hphysical : f = suzukiComplexTestL2 g hgdiff hgsupp := by
    change (ccmArchimedeanFormToAperture a
      (ccmComplexSmoothFormVector a g hgdiff hgsupp hgaper) : SoninL2) = _
    rw [ccmArchimedeanFormToAperture_coe,
      ccmArchimedeanFormEmbedding_ccmComplexSmoothFormVector]
  have hfourier : fourierUnitary f = F.toLp 2 volume := by
    rw [hphysical]
    exact SchwartzMap.toLp_fourier_eq G
  have hae : ((fourierUnitary f : SoninL2) : ℝ → ℂ) =ᵐ[volume] F := by
    rw [hfourier]
    exact F.coeFn_toLp 2 volume
  have hF := integrable_abs_mul_normSq_schwartzMap F
  apply hF.congr
  filter_upwards [hae] with xi hxi
  rw [hxi]

/-- The even matched symmetric residual is absolutely summable on every literal complex smooth
CCM source vector. -/
theorem summable_ccmComplexSmoothFormVector_matchedSymmetricCellResidual
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g)
    (hgaper : tsupport g ⊆ Ioo (-a.1) a.1) :
    Summable (fun n : ℕ =>
      ccmActualHeadMatchedSymmetricCellResidual n
        (ccmArchimedeanFormToAperture a
          (ccmComplexSmoothFormVector a g hgdiff hgsupp hgaper) : SoninL2)) := by
  exact summable_ccmActualHeadMatchedSymmetricCellResidual_of_firstMoment _
    (integrable_ccmComplexSmoothFormVector_fourierFirstMoment
      a g hgdiff hgsupp hgaper)

/-- **Dense-core completed convergence.**  Every literal complex smooth CCM source has an
absolutely summable all-prime family after each prime atom is compensated by its exact
mass-matched outgoing polar cell. -/
theorem summable_ccmComplexSmoothFormVector_matchedPrimePolarCellDifference
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g)
    (hgaper : tsupport g ⊆ Ioo (-a.1) a.1) :
    Summable (fun n : ℕ =>
      let f : SoninL2 := ccmArchimedeanFormToAperture a
        (ccmComplexSmoothFormVector a g hgdiff hgsupp hgaper)
      criticalMellinAtomWeight n *
          ccmActualHeadTranslationDefect (Real.log n) f -
        ccmActualHeadOutgoingPolarSymmetricCell
          (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f) := by
  exact summable_ccmActualHeadMatchedPrimePolarCellDifference_of_firstMoment _
    (integrable_ccmComplexSmoothFormVector_fourierFirstMoment
      a g hgdiff hgsupp hgaper)

end RHTower
