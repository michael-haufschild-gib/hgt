import GaloisForLFunctions.HTGeometry.GammaCommonInverseCollar

/-!
# The moving-base shell is eventually small

The capacity and atlas laws on the common inverse collar are conditioned on the moving-base shell
having modulus below one half.  The corpus already proves the shell tends to zero, so the condition
holds for every large index — and, at every tolerance, cofinally.

The laws therefore apply along a cofinal set of indices with no further input; the hypothesis is a
threshold, not a restriction on the object.
-/

open Filter Topology

namespace GaloisForLFunctions

/-- The shell modulus tends to zero. -/
theorem tendsto_norm_gammaMovingBaseShell_zero :
    Tendsto (fun n => ‖gammaMovingBaseShell n‖) atTop (nhds 0) := by
  simpa using tendsto_gammaMovingBaseShell_zero.norm

/-- **The shell is eventually below every positive tolerance.** -/
theorem eventually_norm_gammaMovingBaseShell_lt {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ‖gammaMovingBaseShell n‖ < ε :=
  (tendsto_order.1 tendsto_norm_gammaMovingBaseShell_zero).2 ε hε

/-- **The half-shell hypothesis of the collar laws holds for every large index.** -/
theorem eventually_norm_gammaMovingBaseShell_lt_half :
    ∀ᶠ n : ℕ in atTop, ‖gammaMovingBaseShell n‖ < (1 / 2 : ℝ) :=
  eventually_norm_gammaMovingBaseShell_lt (by norm_num)

/-- Hence some index satisfies it, and cofinally many do. -/
theorem exists_norm_gammaMovingBaseShell_lt_half (N : ℕ) :
    ∃ n ≥ N, ‖gammaMovingBaseShell n‖ < (1 / 2 : ℝ) := by
  obtain ⟨n, hn, hlt⟩ :=
    (eventually_norm_gammaMovingBaseShell_lt_half.and (eventually_ge_atTop N)).exists
  exact ⟨n, hlt, hn⟩

end GaloisForLFunctions
