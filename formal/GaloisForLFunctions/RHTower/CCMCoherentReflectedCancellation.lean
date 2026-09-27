import GaloisForLFunctions.RHTower.CCMActualHeadSupportedCoherentGamma

/-!
# A reflected component invisible to the actual signed current

The shifts `-s` and `r+s` have opposite real pairings with `U_r f-f`.
This applies to the entire actual prime sum and its oriented terminal term,
before taking any norm. Their sum therefore remains invisible after the
physical support projection. No parity assumption on the source is needed.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProduct BigOperators
noncomputable section
namespace RHTower

private theorem autocorrelation_neg (s : ℝ) (f : SoninL2) :
    ccmActualHeadSymmetricAutocorrelation (-s) f =
      ccmActualHeadSymmetricAutocorrelation s f := by
  simp only [ccmActualHeadSymmetricAutocorrelation, neg_neg, add_comm]

/-- Reflection about the increment midpoint cancels the real signed pairing.
The assertion holds for every complex physical source. -/
theorem re_inner_increment_reflected_shift_sum_zero (r s : ℝ) (f : SoninL2) :
    (inner ℂ (logTranslationCLM r f - f)
      (logTranslationCLM (-s) f + logTranslationCLM (r+s) f)).re = 0 := by
  have h₁ := ccmActualHeadAutocorrelation_add_sub_eq_re_inner_increment_shifted r s f
  have h₂ := ccmActualHeadAutocorrelation_add_sub_eq_re_inner_increment_shifted r (-(r+s)) f
  rw [neg_neg, show r + -(r+s) = -s by ring, autocorrelation_neg,
    autocorrelation_neg] at h₂
  rw [inner_add_right, Complex.add_re]
  linarith only [h₁, h₂]

/-- The literal reflected field uses the same real prime coefficients and
the same signed terminal coefficient as the completed coherent field. -/
def ccmActualHeadReflectedCoherentField (T : ℝ) (N : ℕ) (f : SoninL2) (r : ℝ) : SoninL2 :=
  (∑ n ∈ Finset.range N, (ccmOutgoingQuantileDisplacementCellDensity n r : ℂ) •
    logTranslationCLM (r + Real.log n) f) +
      (ccmActualHeadQuantileTerminalDisplacementDensity T N r : ℂ) •
        logTranslationCLM (r+T) f

theorem aestronglyMeasurable_ccmActualHeadReflectedCoherentField
    (T : ℝ) (N : ℕ) (f : SoninL2) :
    AEStronglyMeasurable (ccmActualHeadReflectedCoherentField T N f) := by
  have hshift (s : ℝ) : AEStronglyMeasurable (fun r : ℝ => logTranslationCLM (r+s) f) :=
    ((continuous_logTranslationCLM f).comp (continuous_id.add_const s)).aestronglyMeasurable
  have hsum : AEStronglyMeasurable (fun r : ℝ =>
      ∑ n ∈ Finset.range N, (ccmOutgoingQuantileDisplacementCellDensity n r : ℂ) •
        logTranslationCLM (r + Real.log n) f) := by
    refine (Finset.aestronglyMeasurable_sum (Finset.range N) fun n _ =>
      (Complex.ofRealCLM.continuous.measurable.comp
        (measurable_ccmOutgoingQuantileDisplacementCellDensity n)).aestronglyMeasurable.smul
          (hshift (Real.log n))).congr ?_
    filter_upwards with r
    simp only [Finset.sum_apply]
    rfl
  exact hsum.add ((Complex.ofRealCLM.continuous.measurable.comp
    (measurable_ccmActualHeadQuantileTerminalDisplacementDensity T N)).aestronglyMeasurable.smul
      (hshift T))

/-- Cancellation includes all prime and terminal coefficients in one identity. -/
theorem re_inner_increment_completed_add_reflected_zero
    (T : ℝ) (N : ℕ) (f : SoninL2) (r : ℝ) :
    (inner ℂ (logTranslationCLM r f - f)
      (ccmActualHeadQuantileCompletedCoherentField T N f r +
        ccmActualHeadReflectedCoherentField T N f r)).re = 0 := by
  have hscale (s c : ℝ) :
      (inner ℂ (logTranslationCLM r f - f)
        ((c : ℂ) • (logTranslationCLM (-s) f + logTranslationCLM (r+s) f))).re = 0 := by
    rw [inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, re_inner_increment_reflected_shift_sum_zero, mul_zero]
  have hfield : ccmActualHeadQuantileCompletedCoherentField T N f r +
      ccmActualHeadReflectedCoherentField T N f r =
      (∑ n ∈ Finset.range N, (ccmOutgoingQuantileDisplacementCellDensity n r : ℂ) •
        (logTranslationCLM (-Real.log n) f + logTranslationCLM (r + Real.log n) f)) +
      (ccmActualHeadQuantileTerminalDisplacementDensity T N r : ℂ) •
        (logTranslationCLM (-T) f + logTranslationCLM (r+T) f) := by
    simp only [ccmActualHeadQuantileCompletedCoherentField, ccmActualHeadQuantileBulkCoherentField,
      ccmActualHeadQuantileCellCoherentField, ccmActualHeadQuantileTerminalCoherentField,
      ccmActualHeadReflectedCoherentField, smul_add, Finset.sum_add_distrib]
    abel
  rw [hfield, inner_add_right, inner_sum, Complex.add_re, Complex.re_sum]
  simp only [hscale, Finset.sum_const_zero, add_zero]

/-- A real-current-invisible direction inside the already reduced support. -/
def ccmActualHeadSupportedReflectedDirection (a : SuzukiPositiveAperture)
    (N : ℕ) (f : SoninL2) (r : ℝ) : SoninL2 :=
  ccmIncrementSupportProjection a r
    (ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f r +
      ccmActualHeadReflectedCoherentField (2*a.1) N f r)

private theorem projected_measurable {E : Type*} [TopologicalSpace E]
    (P : ℝ × E → E) (Y : ℝ → E) (hP : Continuous P) (hY : AEStronglyMeasurable Y) :
    AEStronglyMeasurable (fun r : ℝ => P (r, Y r)) :=
  hP.comp_aestronglyMeasurable
    ((continuous_id : Continuous (fun r : ℝ => r)).aestronglyMeasurable.prodMk hY)

theorem aestronglyMeasurable_ccmActualHeadSupportedReflectedDirection
    (a : SuzukiPositiveAperture) (N : ℕ) (f : SoninL2) :
    AEStronglyMeasurable (ccmActualHeadSupportedReflectedDirection a N f) :=
  projected_measurable
    (fun p : ℝ × SoninL2 => ccmIncrementSupportProjection a p.1 p.2)
    (fun r => ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f r +
      ccmActualHeadReflectedCoherentField (2*a.1) N f r)
    (continuous_ccmIncrementSupportProjection_joint a)
    ((aestronglyMeasurable_ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f).add
      (aestronglyMeasurable_ccmActualHeadReflectedCoherentField (2*a.1) N f))

theorem re_inner_increment_supportedReflectedDirection_zero
    (a : SuzukiPositiveAperture) (N : ℕ) (f : suzukiApertureHilbert a) (r : ℝ) :
    (inner ℂ (logTranslationCLM r f.1 - f.1)
      (ccmActualHeadSupportedReflectedDirection a N f.1 r)).re = 0 := by
  rw [ccmActualHeadSupportedReflectedDirection, inner_increment_ccmIncrementSupportProjection]
  exact re_inner_increment_completed_add_reflected_zero (2*a.1) N f.1 r

end RHTower
