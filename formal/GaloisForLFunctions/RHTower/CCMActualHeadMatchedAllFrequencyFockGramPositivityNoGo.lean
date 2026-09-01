import GaloisForLFunctions.RHTower.CCMActualHeadMatchedInfiniteFockReporterSignNoGo

/-!
# All-frequency Fock Gram positivity does not orient the matched source

The fixed-frequency coherent-Fock carriers of the actual matched CCM source are principal
restrictions of one kernel indexed simultaneously by arithmetic atoms and real frequency.  This
single kernel is positive semidefinite on every finite mixed-frequency packet.

Nevertheless, every literal prime-power reporter lies above one at outer phase `2π` and below one
at outer phase `π`, inside this same kernel.  Thus cross-frequency Gram positivity does not repair
the source-sign obstruction.  A viable nonlocal Ward mechanism must preserve additional oriented
structure rather than use only positivity of mixed-frequency Gram minors.
-/

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate ComplexOrder RealInnerProductSpace

noncomputable section
namespace RHTower

/-- Arithmetic atoms and probes carrying their own real-frequency labels. -/
abbrev CCMActualHeadMatchedPhaseAllFrequencyProjectiveFockIndex :=
  CCMActualHeadMatchedPhaseProjectiveFockIndex (ℕ × ℝ)

namespace CCMActualHeadMatchedPhaseAllFrequencyProjectiveFockIndex

/-- Joint arithmetic-frequency feature map into the existing three-dimensional source space. -/
def feature :
    CCMActualHeadMatchedPhaseAllFrequencyProjectiveFockIndex →
      CCMActualHeadMatchedPhaseProjectiveFockSpace
  | .atom nxi => ccmActualHeadMatchedPhaseProjectiveAtomFeature nxi.1 nxi.2
  | .positiveProbe nxi => ccmActualHeadMatchedPhaseRotatingProbe nxi.1 nxi.2
  | .negativeProbe nxi => -ccmActualHeadMatchedPhaseRotatingProbe nxi.1 nxi.2

/-- Embed one fixed-frequency carrier as a principal subsystem of the joint carrier. -/
def fixedFrequencyEmbedding (xi : ℝ) :
    CCMActualHeadMatchedPhaseProjectiveFockIndex ℕ →
      CCMActualHeadMatchedPhaseAllFrequencyProjectiveFockIndex
  | .atom n => .atom (n, xi)
  | .positiveProbe n => .positiveProbe (n, xi)
  | .negativeProbe n => .negativeProbe (n, xi)

theorem feature_fixedFrequencyEmbedding (xi : ℝ)
    (i : CCMActualHeadMatchedPhaseProjectiveFockIndex ℕ) :
    feature (fixedFrequencyEmbedding xi i) =
      CCMActualHeadMatchedPhaseProjectiveFockIndex.feature id xi i := by
  cases i <;> rfl

end CCMActualHeadMatchedPhaseAllFrequencyProjectiveFockIndex

/-- Exponential inner-product matrix on all arithmetic-frequency labels at once. -/
def ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockMatrix :
    Matrix CCMActualHeadMatchedPhaseAllFrequencyProjectiveFockIndex
      CCMActualHeadMatchedPhaseAllFrequencyProjectiveFockIndex ℝ :=
  GaloisForLFunctions.HilbertMetric.hilbertExponentialInnerMatrix
    CCMActualHeadMatchedPhaseAllFrequencyProjectiveFockIndex.feature (1 / 2)

/-- Complex scalar extension of the all-frequency Fock matrix. -/
def ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockKernel :
    CCMActualHeadMatchedPhaseAllFrequencyProjectiveFockIndex →
      CCMActualHeadMatchedPhaseAllFrequencyProjectiveFockIndex → ℂ :=
  fun a b => (ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockMatrix a b : ℂ)

/-- One kernel satisfies every finite mixed-frequency Gram-positivity constraint. -/
theorem ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockKernel_isPSDKernel :
    GaloisForLFunctions.HTGeometry.IsPSDKernel
      ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockKernel := by
  apply GaloisForLFunctions.HTGeometry.isPSDKernel_of_forall_posSemidef
  · intro a b
    have hs :
        ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockMatrix a b =
          ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockMatrix b a := by
      simp [ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockMatrix,
        GaloisForLFunctions.HilbertMetric.hilbertExponentialInnerMatrix,
        real_inner_comm]
    simpa [ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockKernel] using
      congrArg (fun r : ℝ => (r : ℂ)) hs
  · intro m w
    let A : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun j k =>
      ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockMatrix (w j) (w k)
    have hA : A.PosSemidef := by
      have h :=
        GaloisForLFunctions.HilbertMetric.hilbertExponentialInnerMatrix_fin_posSemidef
          (fun j =>
            CCMActualHeadMatchedPhaseAllFrequencyProjectiveFockIndex.feature (w j))
          (1 / 2) (by norm_num)
      convert h using 1
      ext j k
      simp [A, ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockMatrix,
        GaloisForLFunctions.HilbertMetric.hilbertExponentialInnerMatrix]
    convert realMatrix_posSemidef_map_complex A hA using 1
    ext j k
    rfl

/-- Each fixed-frequency Fock matrix is a principal restriction of the joint matrix. -/
theorem ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockMatrix_fixedFrequencyEmbedding
    (xi : ℝ) (a b : CCMActualHeadMatchedPhaseProjectiveFockIndex ℕ) :
    ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockMatrix
        (CCMActualHeadMatchedPhaseAllFrequencyProjectiveFockIndex.fixedFrequencyEmbedding xi a)
        (CCMActualHeadMatchedPhaseAllFrequencyProjectiveFockIndex.fixedFrequencyEmbedding xi b) =
      ccmActualHeadMatchedPhaseProjectiveFockMatrix id xi a b := by
  simp [ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockMatrix,
    ccmActualHeadMatchedPhaseProjectiveFockMatrix,
    GaloisForLFunctions.HilbertMetric.hilbertExponentialInnerMatrix,
    CCMActualHeadMatchedPhaseAllFrequencyProjectiveFockIndex.feature_fixedFrequencyEmbedding]

/-- Kernel form of the exact fixed-frequency principal-restriction law. -/
theorem ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockKernel_fixedFrequencyEmbedding
    (xi : ℝ) (a b : CCMActualHeadMatchedPhaseProjectiveFockIndex ℕ) :
    ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockKernel
        (CCMActualHeadMatchedPhaseAllFrequencyProjectiveFockIndex.fixedFrequencyEmbedding xi a)
        (CCMActualHeadMatchedPhaseAllFrequencyProjectiveFockIndex.fixedFrequencyEmbedding xi b) =
      ccmActualHeadMatchedPhaseGlobalProjectiveFockKernel xi a b := by
  change
    (ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockMatrix
      (CCMActualHeadMatchedPhaseAllFrequencyProjectiveFockIndex.fixedFrequencyEmbedding xi a)
      (CCMActualHeadMatchedPhaseAllFrequencyProjectiveFockIndex.fixedFrequencyEmbedding xi b) : ℂ) =
        _
  rw [ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockMatrix_fixedFrequencyEmbedding]
  rfl

/-- Same-frequency positive/negative probe ratio read inside the joint kernel. -/
def ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockRatio
    (xi : ℝ) (n : ℕ) : ℝ :=
  (ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockKernel
    (.atom (n, xi)) (.positiveProbe (n, xi))).re /
  (ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockKernel
    (.atom (n, xi)) (.negativeProbe (n, xi))).re

theorem ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockRatio_eq_global
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockRatio xi n =
      ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio xi n := by
  change
    (ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockKernel
      (CCMActualHeadMatchedPhaseAllFrequencyProjectiveFockIndex.fixedFrequencyEmbedding xi (.atom n))
      (CCMActualHeadMatchedPhaseAllFrequencyProjectiveFockIndex.fixedFrequencyEmbedding xi
        (.positiveProbe n))).re /
      (ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockKernel
        (CCMActualHeadMatchedPhaseAllFrequencyProjectiveFockIndex.fixedFrequencyEmbedding xi (.atom n))
        (CCMActualHeadMatchedPhaseAllFrequencyProjectiveFockIndex.fixedFrequencyEmbedding xi
          (.negativeProbe n))).re = _
  rw [ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockKernel_fixedFrequencyEmbedding,
    ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockKernel_fixedFrequencyEmbedding]
  rfl

/-- Every prime-power reporter straddles one inside the same all-frequency PSD kernel. -/
theorem ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockPrimePowerReporterSignStraddle
    (p : Nat.Primes) (e : ℕ) :
    let n := xiGammaEulerValuationNat (p, e)
    GaloisForLFunctions.HTGeometry.IsPSDKernel
        ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockKernel ∧
      1 < ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockRatio
        (ccmActualHeadMatchedPhasePositiveReporterFrequency n) n ∧
      ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockRatio
        (ccmActualHeadMatchedPhaseNegativeReporterFrequency n) n < 1 := by
  dsimp only
  have hn : 1 < xiGammaEulerValuationNat (p, e) :=
    one_lt_xiGammaEulerValuationNat p e
  have hw : 0 < criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) := by
    rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude]
    exact sq_pos_of_pos (suzukiCriticalEntryWallBareAmplitude_pos p e)
  exact ⟨ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockKernel_isPSDKernel,
    by
      rw [ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockRatio_eq_global]
      exact
        ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio_gt_one_at_positiveReporterFrequency
          hn hw,
    by
      rw [ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockRatio_eq_global]
      exact
        ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio_lt_one_at_negativeReporterFrequency
          hn hw⟩

/--
All mixed-frequency Gram minors are positive, but their exact logarithmic source reporter is not
nonnegative.  Hence cross-frequency PSD information alone cannot supply the Ward orientation.
-/
theorem ccmActualHeadMatchedPhaseAllFrequencyFockGramReporterPositivityRouteKilled :
    GaloisForLFunctions.HTGeometry.IsPSDKernel
        ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockKernel ∧
      ¬ ∀ (xi : ℝ) (n : ℕ),
        0 ≤ (1 / 2 : ℝ) * Real.log
          (ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockRatio xi n) := by
  refine ⟨ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockKernel_isPSDKernel, ?_⟩
  intro h
  apply ccmActualHeadMatchedPhaseGlobalProjectiveFockPointwiseReporterPositivityRouteKilled
  intro xi n hpsd
  rw [← ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockRatio_eq_global]
  exact h xi n

/-- Ratio-order version of the all-frequency Gram-positivity no-go. -/
theorem ccmActualHeadMatchedPhaseAllFrequencyFockGramRatioLowerBoundRouteKilled :
    GaloisForLFunctions.HTGeometry.IsPSDKernel
        ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockKernel ∧
      ¬ ∀ (xi : ℝ) (n : ℕ),
        1 ≤ ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockRatio xi n := by
  refine ⟨ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockKernel_isPSDKernel, ?_⟩
  intro h
  apply ccmActualHeadMatchedPhaseGlobalProjectiveFockPointwiseRatioLowerBoundRouteKilled
  intro xi n hpsd
  rw [← ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockRatio_eq_global]
  exact h xi n

end RHTower
