import GaloisForLFunctions.RHTower.SoninShellModeBandEscape
import GaloisForLFunctions.RHTower.SoninPacketSupportCutoffs
import GaloisForLFunctions.RHTower.SoninCouplingBranchEstimate

/-!
# Where a dilated shell mode lives

Dilation carries the cutoff intertwining exactly, so the inverse dilate of a shell mode sits in the
dilated shell with no error at all: every aperture below the dilated inner radius annihilates it and
every aperture above the dilated outer radius fixes it.

For the wavepacket these statements hold only because its profile has compact support; for the shell
modes they are immediate, and they are the geometric half of a layer estimate on modes.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter
open scoped Topology

/-- Every aperture below the dilated inner radius annihilates the dilated shell mode. -/
theorem evenIndicatorCutoff_evenDilationCLM_inv_evenShellVectorEven_eq_zero
    (s u : ℝ) (hsu : s < u) (n : ℕ) (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : t ≤ r * s) :
    evenIndicatorCutoff t
        (evenDilationCLM r⁻¹ (inv_pos.mpr hr) (evenShellVectorEven s u hsu n)) = 0 := by
  have hcov := DFunLike.congr_fun
    (evenIndicatorCutoff_mul_evenDilationCLM t r⁻¹ (inv_pos.mpr hr))
    (evenShellVectorEven s u hsu n)
  rw [mul_apply_eq_comp, mul_apply_eq_comp] at hcov
  have hle : r⁻¹ * t ≤ s := by
    rw [inv_mul_le_iff₀ hr]
    linarith
  rw [hcov, evenIndicatorCutoff_evenShellVectorEven_eq_zero s u (r⁻¹ * t) hsu hle n, map_zero]

/-- Every aperture above the dilated outer radius fixes the dilated shell mode. -/
theorem evenIndicatorCutoff_evenDilationCLM_inv_evenShellVectorEven_eq_self
    (s u : ℝ) (hsu : s < u) (n : ℕ) (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : r * u ≤ t) :
    evenIndicatorCutoff t
        (evenDilationCLM r⁻¹ (inv_pos.mpr hr) (evenShellVectorEven s u hsu n)) =
      evenDilationCLM r⁻¹ (inv_pos.mpr hr) (evenShellVectorEven s u hsu n) := by
  have hcov := DFunLike.congr_fun
    (evenIndicatorCutoff_mul_evenDilationCLM t r⁻¹ (inv_pos.mpr hr))
    (evenShellVectorEven s u hsu n)
  rw [mul_apply_eq_comp, mul_apply_eq_comp] at hcov
  have hle : u ≤ r⁻¹ * t := by
    rw [le_inv_mul_iff₀ hr]
    linarith
  rw [hcov, evenIndicatorCutoff_evenShellVectorEven_of_le s u (r⁻¹ * t) hsu hle n]

/-- The dilated shell mode keeps its norm. -/
theorem norm_evenDilationCLM_inv_evenShellVectorEven
    (s u : ℝ) (hs : 0 < s) (hsu : s < u) (n : ℕ) (r : ℝ) (hr : 0 < r) :
    ‖evenDilationCLM r⁻¹ (inv_pos.mpr hr) (evenShellVectorEven s u hsu n)‖ = 1 := by
  rw [norm_evenDilationCLM_apply r⁻¹ (inv_pos.mpr hr) (evenShellVectorEven s u hsu n)]
  exact (evenShellVectorEven_orthonormal s u hs hsu).norm_eq_one n

end RHTower
