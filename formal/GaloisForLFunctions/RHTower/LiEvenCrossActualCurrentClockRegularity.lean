import GaloisForLFunctions.RHTower.LiEvenCrossActualCurrentClockSeries
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Continuity of the complete-source LI clock

The actual reciprocal-moment series admits one summable factorial envelope on each bounded
clock interval. Tannery's theorem therefore proves continuity without a sign assumption on
the later moments or a restriction on the real clock.
-/

open Filter Topology

namespace RHTower
noncomputable section

/-- One factorial envelope controls every term throughout a bounded clock interval. -/
theorem norm_liEvenCrossActualCurrentClockSeriesTerm_le_of_abs_le
    {w R : ℝ} (hw : |w| ≤ R) (j : ℕ) :
    ‖(-1 : ℝ)^j * (16*w)^j * normalizedPrimeArchMoment j /
      ((2*j+1).factorial : ℝ)‖ ≤
      xiShiftAbsoluteMass 0 * ((16*R/150)^j / ((2*j+1).factorial : ℝ)) := by
  have hA := xiShiftAbsoluteMass_nonneg 0
  calc
    _ ≤ xiShiftAbsoluteMass 0 *
        ((16*|w|/150)^j / ((2*j+1).factorial : ℝ)) :=
      norm_liEvenCrossActualCurrentClockSeriesTerm_le w j
    _ ≤ _ := by gcongr

/-- The literal complete-source clock is continuous at every real clock value. -/
theorem continuous_liEvenCrossActualCurrentClockSeries :
    Continuous liEvenCrossActualCurrentClockSeries := by
  rw [continuous_iff_continuousAt]
  intro w₀
  let R : ℝ := |w₀|+1
  have hR : 0 < R := by dsimp [R]; linarith [abs_nonneg w₀]
  have hsum : Summable (fun j : ℕ => xiShiftAbsoluteMass 0 *
      ((16*R/150)^j / ((2*j+1).factorial : ℝ))) :=
    (summable_liEvenCrossActualCurrentClockFactorialEnvelope (16*R/150)
      (by positivity)).mul_left (xiShiftAbsoluteMass 0)
  have hterms (j : ℕ) : Tendsto (fun w : ℝ =>
      (-1 : ℝ)^j*(16*w)^j*normalizedPrimeArchMoment j /
        ((2*j+1).factorial : ℝ)) (𝓝 w₀)
      (𝓝 ((-1 : ℝ)^j*(16*w₀)^j*normalizedPrimeArchMoment j /
        ((2*j+1).factorial : ℝ))) := by
    exact (by fun_prop : Continuous (fun w : ℝ =>
      (-1 : ℝ)^j*(16*w)^j*normalizedPrimeArchMoment j /
        ((2*j+1).factorial : ℝ))).continuousAt.tendsto
  have hbound : ∀ᶠ w : ℝ in 𝓝 w₀, ∀ j : ℕ,
      ‖(-1 : ℝ)^j*(16*w)^j*normalizedPrimeArchMoment j /
        ((2*j+1).factorial : ℝ)‖ ≤ xiShiftAbsoluteMass 0 *
        ((16*R/150)^j / ((2*j+1).factorial : ℝ)) := by
    have habs : ∀ᶠ w : ℝ in 𝓝 w₀, |w| < R :=
      (continuous_abs.continuousAt : ContinuousAt (fun w : ℝ => |w|) w₀).tendsto.eventually
        (gt_mem_nhds (show |w₀| < R by dsimp [R]; linarith))
    filter_upwards [habs] with w hw
    intro j
    exact norm_liEvenCrossActualCurrentClockSeriesTerm_le_of_abs_le hw.le j
  exact tendsto_tsum_of_dominated_convergence hsum hterms hbound

end
end RHTower
