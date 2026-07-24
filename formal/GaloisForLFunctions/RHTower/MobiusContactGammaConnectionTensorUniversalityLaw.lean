import GaloisForLFunctions.HTGeometry.GammaFactorialJetConnectionTensorLaw
import GaloisForLFunctions.RHTower.MobiusGammaContactTransgression

/-!
# Möbius-contact Gamma connection-tensor universality

The norm of the finite Möbius contact defect is Gamma's pole-clock connection transport. Its
inverse tensor powers, with universal factorial fiber weights, are exactly the intrinsic
covariant top-residue norms at every jet grade.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The observable contact defect and the source-defined factorial connection have identical
positive transport at every depth. -/
theorem norm_mobiusGammaContactPartialCharge_defect_eq_connectionTransport (N : ℕ) :
    ‖(-2 - mobiusGammaContactPartialCharge N) / 2‖ =
      GaloisForLFunctions.HTGeometry.gammaFactorialConnectionTransport N := by
  have hscale :
      (-2 - mobiusGammaContactPartialCharge N) / 2 =
        GaloisForLFunctions.reciprocalGammaFactorialScale N := by
    rw [mobiusGammaContactPartialCharge_eq]
    simp only [GaloisForLFunctions.reciprocalGammaFactorialScale]
    ring
  rw [hscale]
  exact GaloisForLFunctions.HTGeometry.norm_reciprocalGammaFactorialScale_eq_connectionTransport N

/-- **Möbius-contact Gamma connection-tensor universality law.** Contact transport collapses to
the boundary, its flat inverse gauge diverges, and every intrinsic jet grade is its factorially
weighted inverse tensor power. -/
theorem mobiusContactGamma_completeConnectionTensorUniversality :
    (∀ N : ℕ,
      ‖(-2 - mobiusGammaContactPartialCharge N) / 2‖ =
        GaloisForLFunctions.HTGeometry.gammaFactorialConnectionTransport N) ∧
    Tendsto (fun N : ℕ => ‖(-2 - mobiusGammaContactPartialCharge N) / 2‖)
      atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => ‖(-2 - mobiusGammaContactPartialCharge N) / 2‖⁻¹)
      atTop atTop ∧
    ∀ branch n : ℕ, ∀ j : Fin (n + 1),
      ‖GaloisForLFunctions.gammaPoleCovariantTopResidueValue branch n j‖ =
        ‖(-2 - mobiusGammaContactPartialCharge branch) / 2‖⁻¹ ^ (j : ℕ) *
          ((j : ℕ).factorial : ℝ) := by
  refine ⟨norm_mobiusGammaContactPartialCharge_defect_eq_connectionTransport, ?_, ?_, ?_⟩
  · simpa only [norm_mobiusGammaContactPartialCharge_defect_eq_connectionTransport] using
      GaloisForLFunctions.HTGeometry.gammaFactorialConnectionTransport_tendsto_zero
  · simpa only [norm_mobiusGammaContactPartialCharge_defect_eq_connectionTransport] using
      GaloisForLFunctions.HTGeometry.gammaFactorialConnectionTransport_inv_tendsto_atTop
  · intro branch n j
    rw [norm_mobiusGammaContactPartialCharge_defect_eq_connectionTransport]
    exact GaloisForLFunctions.norm_gammaPoleCovariantTopResidueValue_eq_factorialConnectionTensorPower
      branch n j

end

end GaloisForLFunctions.RHTower
