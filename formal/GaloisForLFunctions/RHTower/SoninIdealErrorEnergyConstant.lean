import GaloisForLFunctions.RHTower.SoninShellCutScheduleExists
import GaloisForLFunctions.RHTower.SoninTimeBandHilbertSchmidt
import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry

/-!
# The ideal errors' energy does not move with the scale

One of the three relative-ideal errors is a correction difference precomposed with the dilation, so
its Hilbert--Schmidt energy could in principle grow with the scale.  It does not: dilation is
unitary, and passing to adjoints turns right composition by it into left composition by its inverse,
which preserves the energy exactly.

So the discount subtracted from the number of annuli is a constant of the aperture alone, and the
energy bound's right-hand side grows with the cut.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- **Right composition by a dilation preserves Hilbert--Schmidt energy.** -/
theorem hsNormSq_comp_evenDilationCLM {T : evenSubspace →L[ℂ] evenSubspace}
    (hT : IsHilbertSchmidt T) (r : ℝ) (hr : 0 < r) :
    hsNormSq (T ∘L evenDilationCLM r hr) = hsNormSq T := by
  have hTD := hT.comp_right (evenDilationCLM r hr)
  rw [← hTD.hsNormSq_adjoint, adjoint_comp, adjoint_evenDilationCLM,
    hsNormSq_comp_left_eq_of_norm_map hT.adjoint (evenDilationCLM r⁻¹ (inv_pos.mpr hr))
      (fun x => norm_evenDilationCLM_apply r⁻¹ (inv_pos.mpr hr) x)]
  exact hT.hsNormSq_adjoint

/-- **The third ideal error's energy is scale free.** -/
theorem hsNormSq_soninCouplingIdealErrors_two (a b r : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) :
    hsNormSq (soninCouplingIdealErrors a b r hr 2) =
      hsNormSq (evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) := by
  have hideal : IsSoninPrincipalRelativeIdeal
      (evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) :=
    (IsSoninPrincipalRelativeIdeal.projectionCorrection a ha).sub
      (IsSoninPrincipalRelativeIdeal.projectionCorrection b hb)
  have hHS := isHilbertSchmidt_of_isSoninPrincipalRelativeIdeal hideal
  show hsNormSq ((evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) *
    evenDilationCLM r hr) = _
  rw [show (evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) *
      evenDilationCLM r hr =
    (evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) ∘L
      evenDilationCLM r hr from rfl]
  exact hsNormSq_comp_evenDilationCLM hHS r hr

/-- **The whole discount is scale free.**  Every one of the three ideal errors has an energy that
does not depend on the scale. -/
theorem sum_hsNormSq_soninCouplingIdealErrors (a b r : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) :
    ∑ k : Fin 3, hsNormSq (soninCouplingIdealErrors a b r hr k) =
      2 * hsNormSq (evenSoninProjectionCorrection b) +
        hsNormSq (evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) := by
  rw [Fin.sum_univ_three, hsNormSq_soninCouplingIdealErrors_two a b r ha hb hr]
  show hsNormSq (evenSoninProjectionCorrection b) + hsNormSq (evenSoninProjectionCorrection b) +
    _ = _
  ring

end RHTower
