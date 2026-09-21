import GaloisForLFunctions.RHTower.CCMFUSuzukiCriticalDelayedCharge

/-!
# Single delayed-charge normal form for the critical CCM--FU action

The literal prime--polar finite head has moving lower endpoints.  This file proves that those
endpoints, the positive curvature cells, and the forced wall jet combine exactly into one signed
delayed-charge transform.  It supplies no arithmetic bound: the remaining RH-bearing question is
whether this precise transform is uniformly bounded.
-/

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The complete moving Cauchy cell sum is the curvature transform of the literal active delayed
charge.  Inactive subintervals are identically zero, while active subintervals use the local
curvature--kernel integrability certificate.  No absolute value or separate moment is introduced. -/
theorem ccmFUSuzukiCriticalCauchyVolterraCells_eq_delayedChargeTransport
    {H : ℝ} (hH : 2 ≤ H) :
    (∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
      (((j + 3 : ℕ) : ℝ) * ccmFUSuzukiCriticalPrimePolarIncrement j) *
        ∫ y in Real.sqrt ((j + 3 : ℕ) : ℝ)..Real.exp (H / 2),
          cauchyVolterraFUCurvature H y *
            cauchyVolterraKernel (Real.sqrt ((j + 3 : ℕ) : ℝ)) y) =
      ∫ y in 1..Real.exp (H / 2),
        cauchyVolterraFUCurvature H y *
          (ccmFUSuzukiCriticalActiveDelayedCharge H y / y ^ 2) := by
  let M := suzukiCheckpointEventIndex H - 2
  let a : ℕ → ℝ := fun j =>
    ((j + 3 : ℕ) : ℝ) * ccmFUSuzukiCriticalPrimePolarIncrement j
  let xi : ℕ → ℝ := fun j => Real.sqrt ((j + 3 : ℕ) : ℝ)
  let Y : ℝ := Real.exp (H / 2)
  have hH0 : 0 < H := by linarith
  have hY1 : 1 ≤ Y := by
    dsimp only [Y]
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hrange : ∀ j ∈ Finset.range M, 1 ≤ xi j ∧ xi j ≤ Y := by
    intro j hj
    have hactive : 1 < xi j ∧ xi j ≤ Y := by
      simpa only [M, xi, Y] using ccmFUSuzuki_activeSqrtClockRange hH hj
    exact ⟨hactive.1.le, hactive.2⟩
  have hleft : ∀ j ∈ Finset.range M, IntervalIntegrable
      (fun y : ℝ => if xi j ≤ y then
        a j * (cauchyVolterraFUCurvature H y * cauchyVolterraKernel (xi j) y) else 0)
      volume 1 (xi j) := by
    intro j hj
    refine IntervalIntegrable.congr_uIoo (f := fun _ : ℝ => 0) IntervalIntegrable.zero ?_
    intro y hy
    rw [Set.uIoo_of_le (hrange j hj).1] at hy
    simp [not_le_of_gt hy.2]
  have hright : ∀ j ∈ Finset.range M, IntervalIntegrable
      (fun y : ℝ => if xi j ≤ y then
        a j * (cauchyVolterraFUCurvature H y * cauchyVolterraKernel (xi j) y) else 0)
      volume (xi j) Y := by
    intro j hj
    have hactive : 1 < xi j ∧ xi j ≤ Y := by
      simpa only [M, xi, Y] using ccmFUSuzuki_activeSqrtClockRange hH hj
    refine (cauchyVolterraFUCurvature_mul_kernel_intervalIntegrable hH0 hactive.1 hactive.2).const_mul (a j) |>.congr_uIoo ?_
    intro y hy
    rw [Set.uIoo_of_le hactive.2] at hy
    simp [le_of_lt hy.1]
  have hfull : ∀ j ∈ Finset.range M, IntervalIntegrable
      (fun y : ℝ => if xi j ≤ y then
        a j * (cauchyVolterraFUCurvature H y * cauchyVolterraKernel (xi j) y) else 0)
      volume 1 Y := by
    intro j hj
    exact (hleft j hj).trans (hright j hj)
  have htransport := cauchyVolterra_finite_signed_transport_variable_lower
    (s := Finset.range M) (a := a) (ξ := xi) (x := 1) (Y := Y)
    (q := cauchyVolterraFUCurvature H) hrange hleft hright hfull
  change (∑ j ∈ Finset.range M, a j *
      ∫ y in xi j..Y, cauchyVolterraFUCurvature H y * cauchyVolterraKernel (xi j) y) = _
  calc
    (∑ j ∈ Finset.range M, a j *
        ∫ y in xi j..Y, cauchyVolterraFUCurvature H y * cauchyVolterraKernel (xi j) y) =
        ∫ y in 1..Y, ∑ j ∈ Finset.range M,
          if xi j ≤ y then
            a j * (cauchyVolterraFUCurvature H y * cauchyVolterraKernel (xi j) y) else 0 := htransport
    _ = ∫ y in 1..Y, cauchyVolterraFUCurvature H y *
        ccmFUSuzukiCriticalActiveCauchyCodiagonal H y := by
          apply intervalIntegral.integral_congr
          intro y hy
          unfold ccmFUSuzukiCriticalActiveCauchyCodiagonal
          change (∑ j ∈ Finset.range M, if xi j ≤ y then
            a j * (cauchyVolterraFUCurvature H y * cauchyVolterraKernel (xi j) y) else 0) =
              cauchyVolterraFUCurvature H y * ∑ j ∈ Finset.range M,
                if xi j ≤ y then a j * cauchyVolterraKernel (xi j) y else 0
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          split_ifs <;> ring
    _ = ∫ y in 1..Y, cauchyVolterraFUCurvature H y *
        (ccmFUSuzukiCriticalActiveDelayedCharge H y / y ^ 2) := by
          apply intervalIntegral.integral_congr
          intro y hy
          rw [Set.uIcc_of_le hY1] at hy
          change cauchyVolterraFUCurvature H y *
              ccmFUSuzukiCriticalActiveCauchyCodiagonal H y =
            cauchyVolterraFUCurvature H y *
              (ccmFUSuzukiCriticalActiveDelayedCharge H y / y ^ 2)
          rw [ccmFUSuzukiCriticalActiveCauchyCodiagonal_eq_delayedCharge_div_sq
            (ne_of_gt (lt_of_lt_of_le zero_lt_one hy.1))]

/-- Exact literal normal form of the critical CCM--FU action.  Completion is performed before
any positivity or energy estimate: both wall jet and bulk retain one common signed delayed
prime--polar charge. -/
theorem ccmFUSuzukiCriticalMertensDeviationVariationAction_eq_zeroClock_add_delayedChargeTransport
    {H : ℝ} (hH : 2 ≤ H) :
    suzukiCheckpointCriticalVariationAction suzukiCheckpointCriticalMertensDeviation H =
      suzukiCheckpointCriticalMertensDeviation 0 *
          suzukiCheckpointCriticalTriangularMultiplier H 0 +
      (64 / (Real.exp (H / 2) ^ 2 * H ^ 4)) *
        ccmFUSuzukiCriticalActiveDelayedCharge H (Real.exp (H / 2)) +
      ∫ y in 1..Real.exp (H / 2), cauchyVolterraFUCurvature H y *
        (ccmFUSuzukiCriticalActiveDelayedCharge H y / y ^ 2) := by
  have hH0 : 0 < H := by linarith
  have hHne : H ≠ 0 := ne_of_gt hH0
  have hYne : Real.exp (H / 2) ≠ 0 := (Real.exp_pos _).ne'
  have hend :
      (∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
        (((j + 3 : ℕ) : ℝ) * ccmFUSuzukiCriticalPrimePolarIncrement j) *
          (1 - Real.sqrt ((j + 3 : ℕ) : ℝ) / Real.exp (H / 2))) =
        ccmFUSuzukiCriticalActiveDelayedCharge H (Real.exp (H / 2)) /
          Real.exp (H / 2) := by
    rw [ccmFUSuzukiCriticalActiveDelayedCharge_at_wall hH]
    field_simp [hYne]
  rw [ccmFUSuzukiCriticalMertensDeviationVariationAction_eq_zeroClock_add_explicitCauchyVolterraCells hH,
    hend, ccmFUSuzukiCriticalCauchyVolterraCells_eq_delayedChargeTransport hH]
  field_simp [hYne, hHne]

end

end RHTower
