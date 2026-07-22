/-
Schatten-1 closure of the exact Sonin time-band ideal.

The generator upgrade comes from the factorially convergent rank-one Fourier expansion in
`FiniteTimeBandFourierSchatten`; algebraic closure then follows from the genuine Schatten-1
ideal laws in `TraceNorm`.
-/
import GaloisForLFunctions.RHTower.FiniteTimeBandFourierSchatten
import GaloisForLFunctions.RHTower.SoninTimeBandIdeal

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- The Fourier-then-physical central cutoff block is Schatten-1. -/
theorem memSchattenClass_one_fourierCutoff_indicatorCutoff_central
    (s t : ℝ) (hs : 0 < s) :
    MemSchattenClass 1
      (fourierCutoff (centralInterval s) (measurableSet_centralInterval s) *
        indicatorCutoff (centralInterval t) (measurableSet_centralInterval t)) := by
  let U : SoninL2 →L[Complex] SoninL2 :=
    fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap
  let K : SoninL2 →L[Complex] SoninL2 := cutoffFourierCutoff (-s) s (-t) t
  have hK : MemSchattenClass 1 K := by
    simpa [K] using
      memSchattenClass_one_cutoffFourierCutoff (-s) s (-t) t (by linarith)
  have hEq :
      fourierCutoff (centralInterval s) (measurableSet_centralInterval s) *
          indicatorCutoff (centralInterval t) (measurableSet_centralInterval t) =
        U * K := by
    apply ContinuousLinearMap.ext
    intro f
    rfl
  rw [hEq]
  exact memSchattenClass_one_comp_left hK U

/-- The physical-then-Fourier central cutoff block is Schatten-1. -/
theorem memSchattenClass_one_indicatorCutoff_fourierCutoff_central
    (s t : ℝ) (hs : 0 < s) :
    MemSchattenClass 1
      (indicatorCutoff (centralInterval s) (measurableSet_centralInterval s) *
        fourierCutoff (centralInterval t) (measurableSet_centralInterval t)) := by
  let Aₛ : SoninL2 →L[Complex] SoninL2 :=
    indicatorCutoff (centralInterval s) (measurableSet_centralInterval s)
  let F : SoninL2 →L[Complex] SoninL2 :=
    fourierUnitary.toLinearIsometry.toContinuousLinearMap
  let J : SoninL2 →L[Complex] SoninL2 := l2Reflection
  let K : SoninL2 →L[Complex] SoninL2 := cutoffFourierCutoff (-s) s (-t) t
  have hK : MemSchattenClass 1 K := by
    simpa [K] using
      memSchattenClass_one_cutoffFourierCutoff (-s) s (-t) t (by linarith)
  have hEq :
      indicatorCutoff (centralInterval s) (measurableSet_centralInterval s) *
          fourierCutoff (centralInterval t) (measurableSet_centralInterval t) =
        J * K * F := by
    apply ContinuousLinearMap.ext
    intro f
    change Aₛ (fourierUnitary.symm
      (indicatorCutoff (centralInterval t) (measurableSet_centralInterval t)
        (fourierUnitary f))) = J (K (F f))
    rw [fourierUnitary_symm_eq_reflection_fourier]
    change indicatorCutoff (centralInterval s) (measurableSet_centralInterval s)
        (l2Reflection (fourierUnitary
          (indicatorCutoff (centralInterval t) (measurableSet_centralInterval t)
            (fourierUnitary f)))) = J (K (F f))
    rw [← l2Reflection_indicatorCutoff_central]
    dsimp [J, K, F, cutoffFourierCutoff]
    rfl
  rw [hEq]
  exact memSchattenClass_one_comp_right
    (memSchattenClass_one_comp_left hK J) F

namespace IsSoninTimeBandIdeal

/-- Every element of the exact algebraic Sonin time-band ideal is Schatten-1. -/
theorem memSchattenClass_one {T : SoninL2 →L[Complex] SoninL2}
    (hT : IsSoninTimeBandIdeal T) : MemSchattenClass 1 T := by
  induction hT with
  | zero => simp [MemSchattenClass, approxNumber_zero_op]
  | indicatorFourier s t hs ht =>
      exact memSchattenClass_one_indicatorCutoff_fourierCutoff_central s t hs
  | fourierIndicator s t hs ht =>
      exact memSchattenClass_one_fourierCutoff_indicatorCutoff_central s t hs
  | add hS hT ihS ihT =>
      exact memSchattenClass_one_add
        hS.isCompactOperator hT.isCompactOperator ihS ihT
  | neg hT ihT => simpa using memSchattenClass_one_smul ihT (-1)
  | leftMul L hT ihT => exact memSchattenClass_one_comp_left ihT L
  | rightMul hT R ihT => exact memSchattenClass_one_comp_right ihT R

end IsSoninTimeBandIdeal

theorem centralSoninProjectionCorrection_memSchattenClass_one
    (a : ℝ) (ha : 0 < a) :
    MemSchattenClass 1 (centralSoninProjectionCorrection a) :=
  (centralSoninProjectionCorrection_mem_timeBandIdeal a ha).memSchattenClass_one

end RHTower
