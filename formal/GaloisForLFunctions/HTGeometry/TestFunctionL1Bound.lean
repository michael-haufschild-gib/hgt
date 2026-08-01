import GaloisForLFunctions.HTGeometry.TestFunctionSeminorm
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The `L¹` norm of a test function is controlled by its supremum

A test function vanishes outside its fixed compact set, so its absolute value is dominated by the
indicator of that set times the supremum.  Integrating gives
`∫ ‖φ‖ ≤ vol(J) · ‖φ‖_∞`.

This is the continuity input for the smoothing map `φ ↦ K_φ`: the operator norm of the smoothing
is bounded by the `L¹` norm of the weight, hence by the order-zero seminorm of the test space.

* `deningerTest_integral_norm_le` : the `L¹` bound.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

section L1Bound

variable {J : Set ℝ}

/-- A test function is integrable. -/
theorem deningerTest_integrable (hJ : IsCompact J) {phi : ℝ → ℂ}
    (hphi : phi ∈ deningerTestSpace J) : Integrable phi :=
  (continuous_iteratedDeriv_of_mem hphi 0).congr
      (fun t => by rw [iteratedDeriv_zero]) |>.integrable_of_hasCompactSupport
    (hasCompactSupport_of_mem hJ hphi)

/-- **The `L¹` bound.**  The integral of the absolute value of a test function is at most the
measure of its support set times its supremum. -/
theorem deningerTest_integral_norm_le (hJ : IsCompact J) {phi : ℝ → ℂ}
    (hphi : phi ∈ deningerTestSpace J) :
    ∫ t, ‖phi t‖ ≤ (MeasureTheory.volume J).toReal * deningerTestSupNorm 0 phi := by
  classical
  set M : ℝ := deningerTestSupNorm 0 phi with hM
  have hMnonneg : 0 ≤ M := deningerTestSupNorm_nonneg hJ hphi 0
  have hbound : ∀ t, ‖phi t‖ ≤ M := by
    intro t
    have h := norm_iteratedDeriv_le_supNorm hJ hphi 0 t
    rwa [iteratedDeriv_zero] at h
  have hzero : ∀ t, t ∉ J → phi t = 0 := by
    intro t ht
    by_contra hne
    exact ht (hphi.2 (subset_tsupport phi hne))
  have hle : ∀ t, ‖phi t‖ ≤ J.indicator (fun _ => M) t := by
    intro t
    by_cases ht : t ∈ J
    · rw [Set.indicator_of_mem ht]
      exact hbound t
    · rw [Set.indicator_of_notMem ht, hzero t ht, norm_zero]
  have hintNorm : Integrable (fun t => ‖phi t‖) :=
    (deningerTest_integrable hJ hphi).norm
  have hmeas : MeasurableSet J := hJ.measurableSet
  have hfin : MeasureTheory.volume J ≠ ⊤ := (hJ.measure_lt_top).ne
  have hintInd : Integrable (J.indicator fun _ => M) := by
    rw [integrable_indicator_iff hmeas]
    exact integrableOn_const hfin
  refine le_trans (integral_mono hintNorm hintInd hle) ?_
  rw [integral_indicator hmeas, setIntegral_const, MeasureTheory.measureReal_def, smul_eq_mul]

end L1Bound

end GaloisForLFunctions.HTGeometry
