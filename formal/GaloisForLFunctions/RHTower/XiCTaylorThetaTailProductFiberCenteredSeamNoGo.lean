import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberCenteredSeam
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Centre optimization no-go for the corrected product-fibre seam

The Hermitian-polarization defect and the complete oriented endpoint-window current must be kept
together.  Their exact sum is the actual phase current minus the favorable coherent base.  Since
that base is nonpositive in the upper half-plane, every common centre adds a nonnegative penalty;
as the centre tends to infinity, the penalty vanishes and the corrected seam returns to the
actual phase current.
-/

open Complex Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The canonical first-atom phase tail vanishes as its lower endpoint tends to infinity. -/
theorem tendsto_thetaCuspTailSecondDensityAtomOnePhaseTail_atTop_zero
    (z : ℂ) :
    Tendsto (fun c : ℝ => thetaCuspTailSecondDensityAtomOnePhaseTail c z)
      atTop (nhds 0) := by
  unfold thetaCuspTailSecondDensityAtomOnePhaseTail
  exact MeasureTheory.tendsto_integral_Ioi_zero tendsto_id

/-- The corrected polarization-plus-window seam is exactly the actual phase current minus the
coherent prime-oriented base, written as one explicit scalar penalty. -/
theorem thetaProductFiberCenteredCorrectedPhaseSeamCurrent_eq_actual_sub_penalty
    (k : ℕ) {c : ℝ} (hc : 0 ≤ c) {z : ℂ} (hz : 0 ≤ z.im) :
    thetaProductFiberCenteredCorrectedPhaseSeamCurrent k c z =
      thetaProductFiberActualPhaseCurrent k z -
        Complex.normSq (thetaCuspTailSecondDensityAtomOnePhaseTail c z) *
          (thetaProductFiberCenteredPhaseDerivative k z *
            (starRingEnd ℂ) (thetaProductFiberCenteredPhase k z)).im := by
  have h := thetaProductFiberActualPhaseCurrent_eq_coherentBase_add_correctedCenteredSeam
    k hc hz
  unfold xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent at h
  linarith

/-- **Centre-optimization no-go.**  In the open upper half-plane, the complete corrected seam is
never smaller than the actual untruncated phase current.  This compares the joint object; no
window or polarization term is estimated separately. -/
theorem thetaProductFiberActualPhaseCurrent_le_centeredCorrectedPhaseSeam
    (k : ℕ) {c : ℝ} (hc : 0 ≤ c) {z : ℂ} (hz : 0 < z.im) :
    thetaProductFiberActualPhaseCurrent k z ≤
      thetaProductFiberCenteredCorrectedPhaseSeamCurrent k c z := by
  rw [thetaProductFiberCenteredCorrectedPhaseSeamCurrent_eq_actual_sub_penalty
    k hc hz.le]
  have hphase :=
    xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent_nonpos_all
      k hz (thetaCuspTailSecondDensityAtomOnePhaseTail c z)
  unfold xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent at hphase
  linarith

/-- Conditional centre comparison: the corrected seam is monotone in the squared norm of the
chosen common tail. -/
theorem thetaProductFiberCenteredCorrectedPhaseSeamCurrent_mono_of_tail_normSq_le
    (k : ℕ) {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    {z : ℂ} (hz : 0 < z.im)
    (hTail :
      Complex.normSq (thetaCuspTailSecondDensityAtomOnePhaseTail c₁ z) ≤
        Complex.normSq (thetaCuspTailSecondDensityAtomOnePhaseTail c₂ z)) :
    thetaProductFiberCenteredCorrectedPhaseSeamCurrent k c₁ z ≤
      thetaProductFiberCenteredCorrectedPhaseSeamCurrent k c₂ z := by
  rw [thetaProductFiberCenteredCorrectedPhaseSeamCurrent_eq_actual_sub_penalty
      k hc₁ hz.le,
    thetaProductFiberCenteredCorrectedPhaseSeamCurrent_eq_actual_sub_penalty
      k hc₂ hz.le]
  have hphase :=
    xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent_nonpos_all
      k hz 1
  have hmul := mul_le_mul_of_nonpos_right hTail hphase
  simp only [xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent,
    Complex.normSq_one, one_mul] at hmul
  linarith

/-- The exact joint seam returns to the actual phase current as the common centre escapes.  Thus
the best limiting common-centre choice merely recovers the original sign problem. -/
theorem tendsto_thetaProductFiberCenteredCorrectedPhaseSeamCurrent_atTop_actual
    (k : ℕ) {z : ℂ} (hz : 0 ≤ z.im) :
    Tendsto (fun c : ℝ =>
      thetaProductFiberCenteredCorrectedPhaseSeamCurrent k c z)
      atTop (nhds (thetaProductFiberActualPhaseCurrent k z)) := by
  have htail := tendsto_thetaCuspTailSecondDensityAtomOnePhaseTail_atTop_zero z
  have hnorm : Tendsto (fun c : ℝ =>
      Complex.normSq (thetaCuspTailSecondDensityAtomOnePhaseTail c z))
      atTop (nhds 0) := by
    simpa only [Complex.normSq_zero] using
      Complex.continuous_normSq.continuousAt.tendsto.comp htail
  let C : ℝ :=
    (thetaProductFiberCenteredPhaseDerivative k z *
      (starRingEnd ℂ) (thetaProductFiberCenteredPhase k z)).im
  have hmodel : Tendsto (fun c : ℝ =>
      thetaProductFiberActualPhaseCurrent k z -
        Complex.normSq (thetaCuspTailSecondDensityAtomOnePhaseTail c z) * C)
      atTop (nhds (thetaProductFiberActualPhaseCurrent k z)) := by
    simpa only [zero_mul, sub_zero] using
      tendsto_const_nhds.sub (hnorm.mul tendsto_const_nhds)
  apply hmodel.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with c hc
  symm
  simpa only [C] using
    thetaProductFiberCenteredCorrectedPhaseSeamCurrent_eq_actual_sub_penalty
      k hc hz

end

end RHTower
