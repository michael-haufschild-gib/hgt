import GaloisForLFunctions.RHTower.CCM.CCMFUCauchyVolterraSignedSourceFactorization

/-!
# Delayed charge normal form for critical CCM--FU Cauchy transport

The RH-bearing active Cauchy codiagonal is not two independently controlled moments.  It is one
source-faithful delayed signed charge.  This file gives its exact normal form before any norm or
absolute value is introduced.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Literal delayed signed charge of the active critical prime--polar head. -/
def ccmFUSuzukiCriticalActiveDelayedCharge (H y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
    if Real.sqrt ((j + 3 : ℕ) : ℝ) ≤ y then
      (((j + 3 : ℕ) : ℝ) * ccmFUSuzukiCriticalPrimePolarIncrement j) *
        (y - Real.sqrt ((j + 3 : ℕ) : ℝ))
    else 0

/-- Exact delayed-charge form of the active Cauchy codiagonal.  All prime--polar cancellation
remains inside each active atom; no zeroth and first moment is estimated separately. -/
theorem ccmFUSuzukiCriticalActiveCauchyCodiagonal_eq_delayedCharge_div_sq
    {H y : ℝ} (hy : y ≠ 0) :
    ccmFUSuzukiCriticalActiveCauchyCodiagonal H y =
      ccmFUSuzukiCriticalActiveDelayedCharge H y / y ^ (2 : ℕ) := by
  unfold ccmFUSuzukiCriticalActiveCauchyCodiagonal
    ccmFUSuzukiCriticalActiveDelayedCharge cauchyVolterraKernel
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs with hactive
  · field_simp [hy]
  · simp

/-- At the moving FU wall, every literal finite-head atom is active.  Thus the endpoint term
is the same signed delayed charge as the interior transport, rather than a separate zeroth or
first moment. -/
theorem ccmFUSuzukiCriticalActiveDelayedCharge_at_wall
    {H : ℝ} (hH : 2 ≤ H) :
    ccmFUSuzukiCriticalActiveDelayedCharge H (Real.exp (H / 2)) =
      Real.exp (H / 2) *
        ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
          (((j + 3 : ℕ) : ℝ) * ccmFUSuzukiCriticalPrimePolarIncrement j) *
            (1 - Real.sqrt ((j + 3 : ℕ) : ℝ) / Real.exp (H / 2)) := by
  let M := suzukiCheckpointEventIndex H - 2
  let a : ℕ → ℝ := fun j =>
    ((j + 3 : ℕ) : ℝ) * ccmFUSuzukiCriticalPrimePolarIncrement j
  let xi : ℕ → ℝ := fun j => Real.sqrt ((j + 3 : ℕ) : ℝ)
  let Y : ℝ := Real.exp (H / 2)
  have hYne : Y ≠ 0 := (Real.exp_pos _).ne'
  change (∑ j ∈ Finset.range M, if xi j ≤ Y then a j * (Y - xi j) else 0) =
    Y * ∑ j ∈ Finset.range M, a j * (1 - xi j / Y)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hactive : xi j ≤ Y := by
    simpa only [xi, Y, M] using (ccmFUSuzuki_activeSqrtClockRange hH hj).2
  rw [if_pos hactive]
  field_simp [hYne]

end

end RHTower
