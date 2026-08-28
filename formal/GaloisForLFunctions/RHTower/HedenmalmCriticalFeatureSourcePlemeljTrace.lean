import GaloisForLFunctions.RHTower.XiRealBoundaryDivisorMeasure
import GaloisForLFunctions.RHTower.HedenmalmWardGreenRemovableExtensionKernelProjection
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
  4 / (1 + (x - t) ^ 2) ^ 2

theorem continuous_criticalFeatureRealBoundaryWeight (t : ℝ) :
    Continuous (criticalFeatureRealBoundaryWeight t) := by
  unfold criticalFeatureRealBoundaryWeight
  apply Continuous.div continuous_const
    ((continuous_const.add ((continuous_id.sub continuous_const).pow 2)).pow 2)
  intro x
  positivity

theorem criticalFeatureRealBoundaryWeight_eq_normSq (t x : ℝ) :
    criticalFeatureRealBoundaryWeight t x =
      Complex.normSq (criticalFeatureCauchyKernelTest t (x : ℂ)) := by
  rw [criticalFeatureCauchyKernelTest_eq t (by simp)]
  rw [Complex.normSq_div]
  have hden : (1 : ℂ) + ((x : ℂ) - (t : ℂ)) ^ 2 =
      ((1 + (x - t) ^ 2 : ℝ) : ℂ) := by
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
      simpa only [criticalFeatureCompactBoundaryObservable, zero_sub, zero_add] using hlim
    rw [criticalFeatureCompactSourceBoundaryLimit, hlim'.limUnder_eq]

end

end RHTower
