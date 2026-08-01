import GaloisForLFunctions.RHTower.SoninCouplingBranchEstimate

/-!
# Fourier cutoffs conjugated through a dilation

Dilating a vector rescales its frequencies inversely, so the Fourier cutoff at aperture `s` on the
inverse dilate is the dilate of the Fourier cutoff at aperture `r s`.  Since dilation is an
isometry, every Fourier-band energy of the dilated vector is a Fourier-band energy of the original
at the rescaled aperture.

This is what converts the frequency-concentration statement for the dilated wavepacket into one
about the packet itself at apertures growing with the clock.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- The Fourier cutoff on an inverse dilate is the dilate of the rescaled Fourier cutoff. -/
theorem evenFourierCutoff_evenDilationCLM_inv_apply
    (s r : ℝ) (hr : 0 < r) (v : evenSubspace) :
    evenFourierCutoff s (evenDilationCLM r⁻¹ (inv_pos.mpr hr) v) =
      evenDilationCLM r⁻¹ (inv_pos.mpr hr) (evenFourierCutoff (r * s) v) := by
  have hcov := DFunLike.congr_fun
    (evenFourierCutoff_mul_evenDilationCLM s r⁻¹ (inv_pos.mpr hr)) v
  rw [mul_apply_eq_comp, mul_apply_eq_comp] at hcov
  rw [hcov, show (r⁻¹)⁻¹ * s = r * s by rw [inv_inv]]

/-- Fourier-band energies transport across the dilation. -/
theorem norm_evenFourierCutoff_evenDilationCLM_inv
    (s r : ℝ) (hr : 0 < r) (v : evenSubspace) :
    ‖evenFourierCutoff s (evenDilationCLM r⁻¹ (inv_pos.mpr hr) v)‖ =
      ‖evenFourierCutoff (r * s) v‖ := by
  rw [evenFourierCutoff_evenDilationCLM_inv_apply s r hr v]
  exact norm_evenDilationCLM_apply r⁻¹ (inv_pos.mpr hr) (evenFourierCutoff (r * s) v)

/-- The complementary Fourier-band energies transport too. -/
theorem norm_sub_evenFourierCutoff_evenDilationCLM_inv
    (s r : ℝ) (hr : 0 < r) (v : evenSubspace) :
    ‖evenDilationCLM r⁻¹ (inv_pos.mpr hr) v -
        evenFourierCutoff s (evenDilationCLM r⁻¹ (inv_pos.mpr hr) v)‖ =
      ‖v - evenFourierCutoff (r * s) v‖ := by
  rw [evenFourierCutoff_evenDilationCLM_inv_apply s r hr v, ← map_sub]
  exact norm_evenDilationCLM_apply r⁻¹ (inv_pos.mpr hr) (v - evenFourierCutoff (r * s) v)

end RHTower
