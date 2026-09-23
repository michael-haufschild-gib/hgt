import GaloisForLFunctions.RHTower.XiRealBoundaryDivisorMeasure
import GaloisForLFunctions.RHTower.HedenmalmWardGreenRemovableExtensionKernelProjection
import GaloisForLFunctions.RHTower.SlabFullWidthAdmissibility
import GaloisForLFunctions.RHTower.XiCenteredRealShiftDiagonalExtractor
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureLatticePoleGammaVMBudget
import GaloisForLFunctions.HTGeometry.SchwartzCompactContinuousDensity

/-!
# Source-only Plemelj realization of the HCF critical-line trace

The HCF critical-line subtraction is recovered without selecting `XiZeroCopy` in the observable.
For each compact cutoff, the observable uses only `XiC`, its logarithmic derivative, and the
real HCF Cauchy weight.  The local real-boundary divisor theorem identifies its one-sided limit
with the analytic-multiplicity sum over real Xi zeros.  Compact-cutoff exhaustion is treated
separately below; it is the only passage needed to recover the infinite HCF line trace.

This module is a scalarization theorem.  It does not assert the separate quantitative
pole--Gamma--von-Mangoldt budget bound.
-/

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry
open RHTower.RealBoundaryDivisor

namespace RHTower

noncomputable section

/-- The real-axis HCF energy weight, written without any divisor data. -/
def criticalFeatureRealBoundaryWeight (t x : ℝ) : ℝ :=
  4 / (1 + (x - t) ^ (2 : ℕ)) ^ (2 : ℕ)

theorem continuous_criticalFeatureRealBoundaryWeight (t : ℝ) :
    Continuous (criticalFeatureRealBoundaryWeight t) := by
  unfold criticalFeatureRealBoundaryWeight
  apply Continuous.div continuous_const
    ((continuous_const.add ((continuous_id.sub continuous_const).pow 2)).pow 2)
  intro x
  change (1 + (x - t) ^ (2 : ℕ)) ^ (2 : ℕ) ≠ 0
  apply pow_ne_zero
  nlinarith [sq_nonneg (x - t)]

theorem criticalFeatureRealBoundaryWeight_eq_normSq (t x : ℝ) :
    criticalFeatureRealBoundaryWeight t x =
      Complex.normSq (criticalFeatureCauchyKernelTest t (x : ℂ)) := by
  rw [criticalFeatureCauchyKernelTest_eq t (by simp)]
  rw [Complex.normSq_div]
  have hden : (1 : ℂ) + ((x : ℂ) - (t : ℂ)) ^ (2 : ℕ) =
      ((1 + (x - t) ^ (2 : ℕ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hden, Complex.normSq_ofReal]
  norm_num [criticalFeatureRealBoundaryWeight, Complex.normSq_ofReal]
  ring

/-- HCF weight localized by the canonical smooth compact cutoff. -/
def criticalFeatureBoundaryCutoffWeight (t : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  criticalFeatureRealBoundaryWeight t x *
    SchwartzMap.realCompactIntervalCutoff (n : ℝ) x

theorem continuous_criticalFeatureBoundaryCutoffWeight (t : ℝ) (n : ℕ) :
    Continuous (criticalFeatureBoundaryCutoffWeight t n) := by
  exact (continuous_criticalFeatureRealBoundaryWeight t).mul
    (SchwartzMap.realCompactIntervalCutoff (n : ℝ)).continuous

theorem criticalFeatureBoundaryCutoffWeight_eq_zero_of_not_mem
    (t : ℝ) (n : ℕ) {x : ℝ}
    (hx : x ∉ Ioo (-((n : ℝ) + 3)) ((n : ℝ) + 3)) :
    criticalFeatureBoundaryCutoffWeight t n x = 0 := by
  have hnot : x ∉ tsupport (SchwartzMap.realCompactIntervalCutoff (n : ℝ)) := by
    rw [SchwartzMap.realCompactIntervalCutoff_tsupport]
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    rw [abs_of_nonneg hn]
    simp only [Set.mem_setOf_eq]
    intro hle
    apply hx
    constructor
    · have habs : -x ≤ |x| := neg_le_abs x
      linarith
    · have habs : x ≤ |x| := le_abs_self x
      linarith
  have hzero := image_eq_zero_of_notMem_tsupport hnot
  rw [criticalFeatureBoundaryCutoffWeight, hzero, mul_zero]

/-- Compact source observable.  Definition contains no zero or divisor index. -/
def criticalFeatureCompactBoundaryObservable (t : ℝ) (n : ℕ) (eta : ℝ) : ℝ :=
  ∫ x in Icc (-((n : ℝ) + 3)) ((n : ℝ) + 3),
    criticalFeatureBoundaryCutoffWeight t n x * boundaryDensity XiC eta x

/-- Fixed-cutoff source boundary value, selected from the source observable itself. -/
def criticalFeatureCompactSourceBoundaryLimit (t : ℝ) (n : ℕ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) (criticalFeatureCompactBoundaryObservable t n)

/-- **Source-only compact HCF Plemelj law.**  The fixed-cutoff boundary value is exactly the
analytic-multiplicity-weighted HCF energy carried by real Xi zeros in a containing ball.  Zeros
are an output of the theorem, not an input to either source definition above. -/
theorem exists_criticalFeatureCompactSourceBoundaryLimit_eq_realZeroSum
    (t : ℝ) (n : ℕ) :
    ∃ Gamma : Finset ℝ,
      (∀ gamma : ℝ, gamma ∈ Gamma ↔
        ((gamma : ℂ) ∈ Metric.ball (0 : ℂ) ((n : ℝ) + 4) ∧
          XiC (gamma : ℂ) = 0)) ∧
      criticalFeatureCompactSourceBoundaryLimit t n =
        ∑ gamma ∈ Gamma,
          ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
            criticalFeatureBoundaryCutoffWeight t n gamma := by
  have hr : 0 ≤ (n : ℝ) + 3 := by positivity
  have hrR : (n : ℝ) + 3 < (n : ℝ) + 4 := by linarith
  obtain ⟨Gamma, hGamma, hlim⟩ :=
    XiRealBoundary.tendsto_xiBoundaryDensity_setIntegral
      (c := 0) (r := (n : ℝ) + 3) (R := (n : ℝ) + 4)
      hr hrR (continuous_criticalFeatureBoundaryCutoffWeight t n)
      (fun x hx => by
        apply criticalFeatureBoundaryCutoffWeight_eq_zero_of_not_mem t n
        simpa only [zero_sub, zero_add] using hx)
  refine ⟨Gamma, ?_, ?_⟩
  · simpa using hGamma
  · have hlim' : Tendsto (criticalFeatureCompactBoundaryObservable t n)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∑ gamma ∈ Gamma,
          ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
            criticalFeatureBoundaryCutoffWeight t n gamma)) := by
      change Tendsto
        (fun eta : ℝ => ∫ x in Icc (-((n : ℝ) + 3)) ((n : ℝ) + 3),
          criticalFeatureBoundaryCutoffWeight t n x * boundaryDensity XiC eta x)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∑ gamma ∈ Gamma,
          ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
            criticalFeatureBoundaryCutoffWeight t n gamma))
      simpa only [zero_sub, zero_add] using hlim
    rw [criticalFeatureCompactSourceBoundaryLimit, hlim'.limUnder_eq]

/-! ## Cutoff exhaustion on the multiplicity-exact critical line -/

/-- Divisor-side cutoff family used only after the source observable has been defined. -/
def criticalLineCriticalFeatureCutoffEnergy
    (t : ℝ) (n : ℕ) (q : XiZeroCopy) : ℝ :=
  criticalLineCriticalFeatureEnergy t q *
    SchwartzMap.realCompactIntervalCutoff (n : ℝ) (xiSpectralPoint q).re

def criticalLineCriticalFeatureCutoffTrace (t : ℝ) (n : ℕ) : ℝ :=
  ∑' q : XiZeroCopy, criticalLineCriticalFeatureCutoffEnergy t n q

theorem criticalLineCriticalFeatureEnergy_nonneg' (t : ℝ) (q : XiZeroCopy) :
    0 ≤ criticalLineCriticalFeatureEnergy t q := by
  rw [criticalLineCriticalFeatureEnergy]
  split_ifs
  · exact Complex.normSq_nonneg _
  · simp

theorem criticalLineCriticalFeatureCutoffEnergy_nonneg
    (t : ℝ) (n : ℕ) (q : XiZeroCopy) :
    0 ≤ criticalLineCriticalFeatureCutoffEnergy t n q := by
  exact mul_nonneg (criticalLineCriticalFeatureEnergy_nonneg' t q)
    (SchwartzMap.realCompactIntervalCutoff_nonnegative _ _)

theorem criticalLineCriticalFeatureCutoffEnergy_le
    (t : ℝ) (n : ℕ) (q : XiZeroCopy) :
    criticalLineCriticalFeatureCutoffEnergy t n q ≤
      criticalLineCriticalFeatureEnergy t q := by
  rw [criticalLineCriticalFeatureCutoffEnergy]
  exact mul_le_of_le_one_right (criticalLineCriticalFeatureEnergy_nonneg' t q)
    (SchwartzMap.realCompactIntervalCutoff_le_one _ _)

theorem criticalLineCriticalFeatureCutoffEnergy_summable (t : ℝ) (n : ℕ) :
    Summable (criticalLineCriticalFeatureCutoffEnergy t n) := by
  exact Summable.of_nonneg_of_le
    (criticalLineCriticalFeatureCutoffEnergy_nonneg t n)
    (criticalLineCriticalFeatureCutoffEnergy_le t n)
    (criticalLineCriticalFeatureEnergy_summable t)

theorem tendsto_criticalLineCriticalFeatureCutoffEnergy
    (t : ℝ) (q : XiZeroCopy) :
    Tendsto (fun n : ℕ => criticalLineCriticalFeatureCutoffEnergy t n q)
      atTop (𝓝 (criticalLineCriticalFeatureEnergy t q)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge |(xiSpectralPoint q).re|
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcore : |(xiSpectralPoint q).re| ≤ |(n : ℝ)| + 1 := by
    rw [show |(n : ℝ)| = (n : ℝ) by
      rw [abs_of_nonneg (Nat.cast_nonneg n)]]
    linarith
  rw [criticalLineCriticalFeatureCutoffEnergy,
    SchwartzMap.realCompactIntervalCutoff_apply_of_abs_le_add_one _ hcore, mul_one]

/-- Canonical compact cutoffs exhaust the complete multiplicity-exact HCF critical-line trace. -/
theorem tendsto_criticalLineCriticalFeatureCutoffTrace (t : ℝ) :
    Tendsto (criticalLineCriticalFeatureCutoffTrace t) atTop
      (𝓝 (criticalLineCriticalFeatureEnergyTrace t)) := by
  have h := tendsto_tsum_of_dominated_convergence
    (criticalLineCriticalFeatureEnergy_summable t)
    (fun q => tendsto_criticalLineCriticalFeatureCutoffEnergy t q)
    (Filter.Eventually.of_forall fun n q => by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (criticalLineCriticalFeatureCutoffEnergy_nonneg t n q)]
      exact criticalLineCriticalFeatureCutoffEnergy_le t n q)
  change Tendsto
    (fun n : ℕ => ∑' q : XiZeroCopy,
      criticalLineCriticalFeatureCutoffEnergy t n q)
    atTop (𝓝 (∑' q : XiZeroCopy, criticalLineCriticalFeatureEnergy t q))
  exact h

/-! ## Exact identification of each source cutoff -/

/-- Real Xi zeros in the degenerate centered rectangle containing the `n`th cutoff support. -/
def criticalFeatureBoundaryRealZeroFinset (n : ℕ) : Finset ℝ :=
  (xiCClosedRectangleZeros
      (-(((n : ℝ) + 4 : ℝ) : ℂ))
      ((((n : ℝ) + 4 : ℝ) : ℂ))).image Complex.re

private theorem criticalFeatureBoundaryRectangle_im_eq_zero
    {n : ℕ} {w : ℂ}
    (hw : w ∈ xiCClosedRectangleZeros
      (-(((n : ℝ) + 4 : ℝ) : ℂ))
      ((((n : ℝ) + 4 : ℝ) : ℂ))) :
    w.im = 0 := by
  have hrect := (mem_xiCClosedRectangleZeros.mp hw).1
  have him := (Complex.mem_reProdIm.mp hrect).2
  have him' : 0 ≤ w.im ∧ w.im ≤ 0 := by
    simpa only [neg_im, ofReal_im, neg_zero, Set.mem_uIcc, le_refl, and_self,
      or_self] using him
  exact le_antisymm him'.2 him'.1

private theorem criticalFeatureBoundaryRectangle_re_inj (n : ℕ) :
    Set.InjOn Complex.re
      (xiCClosedRectangleZeros
        (-(((n : ℝ) + 4 : ℝ) : ℂ))
        ((((n : ℝ) + 4 : ℝ) : ℂ)) : Set ℂ) := by
  intro w hw v hv hre
  apply Complex.ext hre
  rw [criticalFeatureBoundaryRectangle_im_eq_zero hw,
    criticalFeatureBoundaryRectangle_im_eq_zero hv]

private theorem sum_criticalFeatureBoundaryRealZeroFinset_eq_rectangle
    (t : ℝ) (n : ℕ) :
    (∑ gamma ∈ criticalFeatureBoundaryRealZeroFinset n,
      ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
        criticalFeatureBoundaryCutoffWeight t n gamma) =
      ∑ w ∈ xiCClosedRectangleZeros
          (-(((n : ℝ) + 4 : ℝ) : ℂ))
          ((((n : ℝ) + 4 : ℝ) : ℂ)),
        (xiSpectralMultiplicity w : ℝ) *
          criticalFeatureBoundaryCutoffWeight t n w.re := by
  rw [criticalFeatureBoundaryRealZeroFinset,
    Finset.sum_image (criticalFeatureBoundaryRectangle_re_inj n)]
  apply Finset.sum_congr rfl
  intro w hw
  have him := criticalFeatureBoundaryRectangle_im_eq_zero hw
  have hwreal : ((w.re : ℝ) : ℂ) = w := by
    apply Complex.ext
    · simp
    · simp [him]
  rw [hwreal, xiSpectralMultiplicity_eq_analyticOrderAt_toNat
    (mem_xiCClosedRectangleZeros.mp hw).2]

private theorem sum_criticalFeatureBoundaryRectangle_eq_zeroCopy
    (t : ℝ) (n : ℕ) :
    (∑ w ∈ xiCClosedRectangleZeros
        (-(((n : ℝ) + 4 : ℝ) : ℂ))
        ((((n : ℝ) + 4 : ℝ) : ℂ)),
      (xiSpectralMultiplicity w : ℝ) *
        criticalFeatureBoundaryCutoffWeight t n w.re) =
      ∑ q ∈ xiZeroCopyClosedRectangle
          (-(((n : ℝ) + 4 : ℝ) : ℂ))
          ((((n : ℝ) + 4 : ℝ) : ℂ)),
        criticalFeatureBoundaryCutoffWeight t n (xiSpectralPoint q).re := by
  have hgroup := sum_xiZeroCopyClosedRectangle_eq_multiplicity_sum
    (fun w : ℂ =>
      (criticalFeatureBoundaryCutoffWeight t n w.re : ℂ))
    (-(((n : ℝ) + 4 : ℝ) : ℂ))
    ((((n : ℝ) + 4 : ℝ) : ℂ))
  exact_mod_cast hgroup.symm

private theorem sum_criticalFeatureBoundaryZeroCopy_eq_cutoffTrace
    (t : ℝ) (n : ℕ) :
    (∑ q ∈ xiZeroCopyClosedRectangle
        (-(((n : ℝ) + 4 : ℝ) : ℂ))
        ((((n : ℝ) + 4 : ℝ) : ℂ)),
      criticalFeatureBoundaryCutoffWeight t n (xiSpectralPoint q).re) =
      criticalLineCriticalFeatureCutoffTrace t n := by
  let S := xiZeroCopyClosedRectangle
    (-(((n : ℝ) + 4 : ℝ) : ℂ))
    ((((n : ℝ) + 4 : ℝ) : ℂ))
  have houtside : ∀ q : XiZeroCopy, q ∉ S →
      criticalLineCriticalFeatureCutoffEnergy t n q = 0 := by
    intro q hq
    rw [criticalLineCriticalFeatureCutoffEnergy, criticalLineCriticalFeatureEnergy]
    by_cases hline : (q.1 : ℂ).re = 1 / 2
    · rw [if_pos hline]
      have him : (xiSpectralPoint q).im = 0 := by
        rw [xiSpectralPoint_im_eq, hline]
        norm_num
      have hcut : SchwartzMap.realCompactIntervalCutoff (n : ℝ)
          (xiSpectralPoint q).re = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        rw [SchwartzMap.realCompactIntervalCutoff_tsupport]
        have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
        rw [abs_of_nonneg hn]
        simp only [Set.mem_setOf_eq]
        intro hcore
        apply hq
        apply mem_xiZeroCopyClosedRectangle.mpr
        apply Complex.mem_reProdIm.mpr
        constructor
        · change (xiSpectralPoint q).re ∈
            uIcc (-((n : ℝ) + 4)) ((n : ℝ) + 4)
          rw [Set.mem_uIcc]
          left
          constructor <;> linarith [neg_le_abs (xiSpectralPoint q).re,
            le_abs_self (xiSpectralPoint q).re]
        · simp only [neg_im, ofReal_im, neg_zero]
          simp [him]
      rw [hcut, mul_zero]
    · rw [if_neg hline, zero_mul]
  rw [criticalLineCriticalFeatureCutoffTrace, tsum_eq_sum houtside]
  apply Finset.sum_congr rfl
  intro q hq
  have hrect := mem_xiZeroCopyClosedRectangle.mp hq
  have him := (Complex.mem_reProdIm.mp hrect).2
  have him0 : (xiSpectralPoint q).im = 0 := by
    have him' : 0 ≤ (xiSpectralPoint q).im ∧ (xiSpectralPoint q).im ≤ 0 := by
      simpa only [neg_im, ofReal_im, neg_zero, Set.mem_uIcc, le_refl,
        and_self, or_self] using him
    exact le_antisymm him'.2 him'.1
  have hline : (q.1 : ℂ).re = 1 / 2 := by
    rw [xiSpectralPoint_im_eq] at him0
    linarith
  have hreal : (((xiSpectralPoint q).re : ℝ) : ℂ) = xiSpectralPoint q := by
    apply Complex.ext
    · simp
    · simp [him0]
  rw [criticalLineCriticalFeatureCutoffEnergy,
    criticalLineCriticalFeatureEnergy, if_pos hline, ← hreal,
    criticalFeatureBoundaryCutoffWeight,
    criticalFeatureRealBoundaryWeight_eq_normSq]
  simp

/-- **Exact fixed-cutoff bridge.**  The source-selected compact boundary limit is the matching
multiplicity-exact critical-line cutoff trace.  `XiZeroCopy` occurs only in the proof target, after
the zero-independent source observable and its limit have been fixed. -/
theorem criticalFeatureCompactSourceBoundaryLimit_eq_cutoffTrace
    (t : ℝ) (n : ℕ) :
    criticalFeatureCompactSourceBoundaryLimit t n =
      criticalLineCriticalFeatureCutoffTrace t n := by
  obtain ⟨Gamma, hGamma, hsource⟩ :=
    exists_criticalFeatureCompactSourceBoundaryLimit_eq_realZeroSum t n
  have hsubset : Gamma ⊆ criticalFeatureBoundaryRealZeroFinset n := by
    intro gamma hgamma
    have hg := (hGamma gamma).mp hgamma
    have habs : |gamma| < (n : ℝ) + 4 := by
      simpa only [Metric.mem_ball, Complex.dist_eq, sub_zero, norm_real,
        Real.norm_eq_abs] using hg.1
    apply Finset.mem_image.mpr
    refine ⟨(gamma : ℂ), ?_, by simp⟩
    apply mem_xiCClosedRectangleZeros.mpr
    constructor
    · apply Complex.mem_reProdIm.mpr
      constructor
      · change gamma ∈ uIcc (-((n : ℝ) + 4)) ((n : ℝ) + 4)
        rw [Set.mem_uIcc]
        left
        constructor <;> linarith [neg_le_abs gamma, le_abs_self gamma]
      · simp
    · exact hg.2
  have hextra : ∀ gamma ∈ criticalFeatureBoundaryRealZeroFinset n,
      gamma ∉ Gamma →
      ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
          criticalFeatureBoundaryCutoffWeight t n gamma = 0 := by
    intro gamma hgamma hnotGamma
    obtain ⟨w, hw, hwre⟩ := Finset.mem_image.mp hgamma
    have him := criticalFeatureBoundaryRectangle_im_eq_zero hw
    have hwreal : ((gamma : ℝ) : ℂ) = w := by
      apply Complex.ext
      · simpa using hwre.symm
      · simp [him]
    have hzero : XiC (gamma : ℂ) = 0 := by
      rw [hwreal]
      exact (mem_xiCClosedRectangleZeros.mp hw).2
    have hnotBall : (gamma : ℂ) ∉ Metric.ball (0 : ℂ) ((n : ℝ) + 4) := by
      intro hball
      exact hnotGamma ((hGamma gamma).mpr ⟨hball, hzero⟩)
    have habs : (n : ℝ) + 4 ≤ |gamma| := by
      have hnot : ¬ |gamma| < (n : ℝ) + 4 := by
        simpa only [Metric.mem_ball, Complex.dist_eq, sub_zero, norm_real,
          Real.norm_eq_abs] using hnotBall
      exact not_lt.mp hnot
    have hnotIoo : gamma ∉ Ioo (-((n : ℝ) + 3)) ((n : ℝ) + 3) := by
      intro hinside
      have habslt : |gamma| < (n : ℝ) + 3 := abs_lt.mpr hinside
      linarith
    rw [criticalFeatureBoundaryCutoffWeight_eq_zero_of_not_mem t n hnotIoo, mul_zero]
  calc
    criticalFeatureCompactSourceBoundaryLimit t n =
        ∑ gamma ∈ Gamma,
          ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
            criticalFeatureBoundaryCutoffWeight t n gamma := hsource
    _ = ∑ gamma ∈ criticalFeatureBoundaryRealZeroFinset n,
          ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
            criticalFeatureBoundaryCutoffWeight t n gamma :=
      Finset.sum_subset hsubset hextra
    _ = ∑ w ∈ xiCClosedRectangleZeros
          (-(((n : ℝ) + 4 : ℝ) : ℂ))
          ((((n : ℝ) + 4 : ℝ) : ℂ)),
        (xiSpectralMultiplicity w : ℝ) *
          criticalFeatureBoundaryCutoffWeight t n w.re :=
      sum_criticalFeatureBoundaryRealZeroFinset_eq_rectangle t n
    _ = ∑ q ∈ xiZeroCopyClosedRectangle
          (-(((n : ℝ) + 4 : ℝ) : ℂ))
          ((((n : ℝ) + 4 : ℝ) : ℂ)),
        criticalFeatureBoundaryCutoffWeight t n (xiSpectralPoint q).re :=
      sum_criticalFeatureBoundaryRectangle_eq_zeroCopy t n
    _ = criticalLineCriticalFeatureCutoffTrace t n :=
      sum_criticalFeatureBoundaryZeroCopy_eq_cutoffTrace t n

/-- **Infinite source-only HCF trace.**  Iterated compact Plemelj limits recover the full
critical-line HCF energy trace unconditionally. -/
theorem tendsto_criticalFeatureCompactSourceBoundaryLimit (t : ℝ) :
    Tendsto (criticalFeatureCompactSourceBoundaryLimit t) atTop
      (𝓝 (criticalLineCriticalFeatureEnergyTrace t)) := by
  exact (tendsto_criticalLineCriticalFeatureCutoffTrace t).congr'
    (Filter.Eventually.of_forall fun n =>
      (criticalFeatureCompactSourceBoundaryLimit_eq_cutoffTrace t n).symm)

/-! ## Positive-real-shift pole--Gamma--von-Mangoldt presentation -/

/-- Lower centered boundary density written literally through the continued prime--Gamma source.
The ordinary zeta coordinate is `1/2 + eta + I*x`, so `eta > 0` is a positive real shift. -/
def criticalFeaturePositiveShiftPoleGammaDensity (eta x : ℝ) : ℝ :=
  (Real.pi)⁻¹ *
    (continuedPrimeArchSourceRelativeTrace
      ((x : ℂ) - (eta : ℂ) * I)).im

/-- Compact HCF observable in literal continued pole--Gamma--von-Mangoldt coordinates. -/
def criticalFeatureCompactPoleGammaObservable (t : ℝ) (n : ℕ) (eta : ℝ) : ℝ :=
  ∫ x in Icc (-((n : ℝ) + 3)) ((n : ℝ) + 3),
    criticalFeatureBoundaryCutoffWeight t n x *
      criticalFeaturePositiveShiftPoleGammaDensity eta x

private theorem countable_criticalFeatureLowerBoundaryZeros (eta : ℝ) :
    {x : ℝ | XiC ((x : ℂ) - (eta : ℂ) * I) = 0}.Countable := by
  apply (Set.countable_range
    (fun q : XiZeroCopy => (xiSpectralPoint q).re)).mono
  intro x hx
  obtain ⟨q, hq⟩ :=
    (XiC_eq_zero_iff_exists_xiZeroCopy
      ((x : ℂ) - (eta : ℂ) * I)).mp hx
  refine ⟨q, ?_⟩
  have hre := congrArg Complex.re hq
  simpa using hre

/-- Away from a lower-boundary zero, Schwarz reflection turns the upper Xi Plemelj density into
the continued source at the positive ordinary real shift. -/
theorem boundaryDensity_XiC_eq_positiveShiftPoleGammaDensity
    {eta x : ℝ} (heta0 : 0 < eta) (hetaHalf : eta < 1 / 2)
    (hXi : XiC ((x : ℂ) - (eta : ℂ) * I) ≠ 0) :
    boundaryDensity XiC eta x =
      criticalFeaturePositiveShiftPoleGammaDensity eta x := by
  let z : ℂ := (x : ℂ) - (eta : ℂ) * I
  have hzIm : |z.im| < 1 / 2 := by
    simp [z, abs_of_pos heta0]
    simpa only [one_div] using hetaHalf
  have hadm : XiExplicitAdmissible z :=
    SlabFullWidthAdmissibility.XiExplicitAdmissible_of_abs_im_lt_half hzIm hXi
  have hsource := continuedPrimeArchSourceRelativeTrace_eq_logDeriv_XiC hadm
  have hconj : (starRingEnd ℂ) z = (x : ℂ) + (eta : ℂ) * I := by
    simp [z]
  have hlog := logDeriv_XiC_conj hXi
  rw [hconj] at hlog
  rw [boundaryDensity, criticalFeaturePositiveShiftPoleGammaDensity,
    show (x : ℂ) - (eta : ℂ) * I = z by rfl, hsource, hlog]
  simp
  ring

/-- The two boundary densities agree almost everywhere on every subcritical positive shift.
Possible zeros on the horizontal line form a countable, hence Lebesgue-null, exceptional set. -/
theorem ae_boundaryDensity_XiC_eq_positiveShiftPoleGammaDensity
    {eta : ℝ} (heta0 : 0 < eta) (hetaHalf : eta < 1 / 2) :
    ∀ᵐ x : ℝ ∂volume,
      boundaryDensity XiC eta x =
        criticalFeaturePositiveShiftPoleGammaDensity eta x := by
  have hnull : volume
      {x : ℝ | XiC ((x : ℂ) - (eta : ℂ) * I) = 0} = 0 :=
    (countable_criticalFeatureLowerBoundaryZeros eta).measure_zero volume
  have hae : ∀ᵐ x : ℝ ∂volume,
      XiC ((x : ℂ) - (eta : ℂ) * I) ≠ 0 := by
    rw [ae_iff]
    simpa only [Set.mem_setOf_eq, not_not] using hnull
  filter_upwards [hae] with x hx
  exact boundaryDensity_XiC_eq_positiveShiftPoleGammaDensity
    heta0 hetaHalf hx

/-- Every compact Xi boundary observable is, unconditionally and without a divisor-free
horizontal-line assumption, the same Lebesgue integral of the positive-shift continued
pole--Gamma--von-Mangoldt source. -/
theorem criticalFeatureCompactBoundaryObservable_eq_poleGamma
    (t : ℝ) (n : ℕ) {eta : ℝ} (heta0 : 0 < eta) (hetaHalf : eta < 1 / 2) :
    criticalFeatureCompactBoundaryObservable t n eta =
      criticalFeatureCompactPoleGammaObservable t n eta := by
  rw [criticalFeatureCompactBoundaryObservable,
    criticalFeatureCompactPoleGammaObservable]
  apply setIntegral_congr_ae measurableSet_Icc
  filter_upwards
    [ae_boundaryDensity_XiC_eq_positiveShiftPoleGammaDensity heta0 hetaHalf]
    with x hx
  rw [hx]
  intro _hx
  rfl

/-- The literal positive-shift pole--Gamma observable tends to the matching HCF line cutoff. -/
theorem tendsto_criticalFeatureCompactPoleGammaObservable
    (t : ℝ) (n : ℕ) :
    Tendsto (criticalFeatureCompactPoleGammaObservable t n)
      (𝓝[>] (0 : ℝ))
      (𝓝 (criticalLineCriticalFeatureCutoffTrace t n)) := by
  have hsource : Tendsto (criticalFeatureCompactBoundaryObservable t n)
      (𝓝[>] (0 : ℝ))
      (𝓝 (criticalLineCriticalFeatureCutoffTrace t n)) := by
    have hr : 0 ≤ (n : ℝ) + 3 := by positivity
    have hrR : (n : ℝ) + 3 < (n : ℝ) + 4 := by linarith
    obtain ⟨Gamma, _hGamma, hlim⟩ :=
      XiRealBoundary.tendsto_xiBoundaryDensity_setIntegral
        (c := 0) (r := (n : ℝ) + 3) (R := (n : ℝ) + 4)
        hr hrR (continuous_criticalFeatureBoundaryCutoffWeight t n)
        (fun x hx => by
          apply criticalFeatureBoundaryCutoffWeight_eq_zero_of_not_mem t n
          simpa only [zero_sub, zero_add] using hx)
    have hlim' : Tendsto (criticalFeatureCompactBoundaryObservable t n)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∑ gamma ∈ Gamma,
          ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
            criticalFeatureBoundaryCutoffWeight t n gamma)) := by
      change Tendsto
        (fun eta : ℝ => ∫ x in Icc (-((n : ℝ) + 3)) ((n : ℝ) + 3),
          criticalFeatureBoundaryCutoffWeight t n x * boundaryDensity XiC eta x)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∑ gamma ∈ Gamma,
          ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
            criticalFeatureBoundaryCutoffWeight t n gamma))
      simpa only [zero_sub, zero_add] using hlim
    have htarget :
        (∑ gamma ∈ Gamma,
          ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
            criticalFeatureBoundaryCutoffWeight t n gamma) =
          criticalLineCriticalFeatureCutoffTrace t n := by
      have hlimUnder := hlim'.limUnder_eq
      rw [← criticalFeatureCompactSourceBoundaryLimit,
        criticalFeatureCompactSourceBoundaryLimit_eq_cutoffTrace] at hlimUnder
      exact hlimUnder.symm
    rwa [htarget] at hlim'
  apply hsource.congr'
  have hhalf : ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ), eta < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hhalf] with eta heta0 hetaHalf
  exact (criticalFeatureCompactBoundaryObservable_eq_poleGamma
    t n heta0 hetaHalf)

/-- **Final pre-divisor replacement.**  The iterated height-local pole--Gamma--von-Mangoldt
evaluation recovers the formerly `XiZeroCopy`-weighted infinite HCF critical-line trace. -/
theorem tendsto_iterated_criticalFeaturePoleGammaTrace (t : ℝ) :
    Tendsto
      (fun n : ℕ =>
        limUnder (𝓝[>] (0 : ℝ))
          (criticalFeatureCompactPoleGammaObservable t n))
      atTop (𝓝 (criticalLineCriticalFeatureEnergyTrace t)) := by
  have hinner (n : ℕ) :
      limUnder (𝓝[>] (0 : ℝ))
          (criticalFeatureCompactPoleGammaObservable t n) =
        criticalLineCriticalFeatureCutoffTrace t n :=
    (tendsto_criticalFeatureCompactPoleGammaObservable t n).limUnder_eq
  exact (tendsto_criticalLineCriticalFeatureCutoffTrace t).congr'
    (Filter.Eventually.of_forall fun n => (hinner n).symm)

/-- Corrected HCF lattice budget with both terms source-defined before scalarization. -/
def criticalFeatureSourcePlemeljCorrectedLatticeBudget
    (K : Finset ℤ) (n : ℕ) : ℝ :=
  ∑ k ∈ K,
    (criticalFeaturePoleGammaVMJet (k : ℝ) -
      limUnder (𝓝[>] (0 : ℝ))
        (criticalFeatureCompactPoleGammaObservable (k : ℝ) n))

/-- **Budget-level source replacement.**  Source-only corrected budgets converge to the exact HCF
corrected lattice budget.  This removes the former `XiZeroCopy`-weighted infinite trace from the
pre-divisor definition without changing its value. -/
theorem tendsto_criticalFeatureSourcePlemeljCorrectedLatticeBudget
    (K : Finset ℤ) :
    Tendsto (criticalFeatureSourcePlemeljCorrectedLatticeBudget K) atTop
      (𝓝 (criticalFeaturePrimeGammaOffLineLatticeBudget K)) := by
  have hterm (k : ℤ) : Tendsto
      (fun n : ℕ =>
        criticalFeaturePoleGammaVMJet (k : ℝ) -
          limUnder (𝓝[>] (0 : ℝ))
            (criticalFeatureCompactPoleGammaObservable (k : ℝ) n))
      atTop
      (𝓝 (criticalFeaturePoleGammaVMJet (k : ℝ) -
        criticalLineCriticalFeatureEnergyTrace (k : ℝ))) :=
    tendsto_const_nhds.sub
      (tendsto_iterated_criticalFeaturePoleGammaTrace (k : ℝ))
  have hsum := tendsto_finsetSum K (fun k _hk => hterm k)
  change Tendsto
    (fun n : ℕ => ∑ k ∈ K,
      (criticalFeaturePoleGammaVMJet (k : ℝ) -
        limUnder (𝓝[>] (0 : ℝ))
          (criticalFeatureCompactPoleGammaObservable (k : ℝ) n)))
    atTop
    (𝓝 (∑ k ∈ K,
      ((criticalFeaturePrimeGammaSourceDiagonal (k : ℝ)).re -
        criticalLineCriticalFeatureEnergyTrace (k : ℝ))))
  have htarget :
      (∑ k ∈ K,
        ((criticalFeaturePrimeGammaSourceDiagonal (k : ℝ)).re -
          criticalLineCriticalFeatureEnergyTrace (k : ℝ))) =
        ∑ k ∈ K,
          (criticalFeaturePoleGammaVMJet (k : ℝ) -
            criticalLineCriticalFeatureEnergyTrace (k : ℝ)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [re_criticalFeaturePrimeGammaSourceDiagonal_eq_poleGammaVMJet]
  rw [htarget]
  exact hsum

/-! ## New source-only pole--Gamma covariance -/

/-- Height-local pole--Gamma covariance before the compact cutoff is exhausted.  Both the
archimedean jet and the positive-shift boundary integral are zero-independent source terms. -/
def criticalFeaturePoleGammaPlemeljCovarianceAtCutoff
    (K : Finset ℤ) (n : ℕ) : ℝ :=
  criticalFeaturePoleGammaLatticeBudget K -
    ∑ k ∈ K,
      limUnder (𝓝[>] (0 : ℝ))
        (criticalFeatureCompactPoleGammaObservable (k : ℝ) n)

/-- Infinite source-only pole--Gamma covariance. -/
def criticalFeaturePoleGammaPlemeljCovariance (K : Finset ℤ) : ℝ :=
  limUnder atTop (criticalFeaturePoleGammaPlemeljCovarianceAtCutoff K)

/-- Exact source split at every compact cutoff. -/
theorem criticalFeatureSourcePlemeljCorrectedLatticeBudget_eq_channels
    (K : Finset ℤ) (n : ℕ) :
    criticalFeatureSourcePlemeljCorrectedLatticeBudget K n =
      criticalFeatureVonMangoldtLatticeBudget K +
        criticalFeaturePoleGammaPlemeljCovarianceAtCutoff K n := by
  rw [criticalFeatureSourcePlemeljCorrectedLatticeBudget,
    criticalFeaturePoleGammaPlemeljCovarianceAtCutoff,
    Finset.sum_sub_distrib]
  change criticalFeaturePoleGammaVMLatticeBudget K -
      (∑ k ∈ K, limUnder (𝓝[>] (0 : ℝ))
        (criticalFeatureCompactPoleGammaObservable (k : ℝ) n)) = _
  rw [criticalFeaturePoleGammaVMLatticeBudget_eq_channels]
  ring

/-- Cutoff covariances converge to corrected HCF budget minus the safe-line von-Mangoldt channel. -/
theorem tendsto_criticalFeaturePoleGammaPlemeljCovarianceAtCutoff
    (K : Finset ℤ) :
    Tendsto (criticalFeaturePoleGammaPlemeljCovarianceAtCutoff K) atTop
      (𝓝 (criticalFeaturePrimeGammaOffLineLatticeBudget K -
        criticalFeatureVonMangoldtLatticeBudget K)) := by
  have h :=
    (tendsto_criticalFeatureSourcePlemeljCorrectedLatticeBudget K).sub_const
      (criticalFeatureVonMangoldtLatticeBudget K)
  apply h.congr'
  filter_upwards with n
  rw [criticalFeatureSourcePlemeljCorrectedLatticeBudget_eq_channels]
  ring

/-- **Exact covariance identity.**  Corrected HCF budget is the new source-only covariance plus
the uniformly bounded safe-line von-Mangoldt channel. -/
theorem criticalFeaturePrimeGammaOffLineLatticeBudget_eq_plemeljCovariance_add_vm
    (K : Finset ℤ) :
    criticalFeaturePrimeGammaOffLineLatticeBudget K =
      criticalFeaturePoleGammaPlemeljCovariance K +
        criticalFeatureVonMangoldtLatticeBudget K := by
  have hlim :=
    (tendsto_criticalFeaturePoleGammaPlemeljCovarianceAtCutoff K).limUnder_eq
  rw [criticalFeaturePoleGammaPlemeljCovariance, hlim]
  ring

/-- The corrected budget and the new source-only covariance differ by `o(N)` whenever the lattice
cardinality is `o(N)`.  This is the previously missing pre-divisor covariance reduction. -/
theorem tendsto_correctedBudget_sub_plemeljCovariance_div
    (K : ℕ → Finset ℤ) (N : ℕ → ℝ)
    (hN : ∀ᶠ n in atTop, 0 < N n)
    (hcard : Tendsto (fun n => ((K n).card : ℝ) / N n) atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        (criticalFeaturePrimeGammaOffLineLatticeBudget (K n) -
          criticalFeaturePoleGammaPlemeljCovariance (K n)) / N n)
      atTop (𝓝 0) := by
  have hvm := tendsto_criticalFeatureVonMangoldtLatticeBudget_div_of_card_div
    K N hN hcard
  convert hvm using 1
  funext n
  rw [criticalFeaturePrimeGammaOffLineLatticeBudget_eq_plemeljCovariance_add_vm]
  ring

end

end RHTower
