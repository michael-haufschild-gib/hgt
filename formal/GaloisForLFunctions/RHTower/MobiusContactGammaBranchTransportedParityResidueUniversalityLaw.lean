import GaloisForLFunctions.RHTower.MobiusContactGammaCrossParityZetaRatioUniversalityLaw
import GaloisForLFunctions.RHTower.MobiusContactGammaConnectionTensorUniversalityLaw

/-!
# Möbius-contact Gamma branch-transported parity residues

The adjacent odd/even Gamma factorial channels start in the branch-zero
factorial fiber. The Möbius-contact connection tensor transports both
channels to every fixed Gamma pole branch. They acquire one common intrinsic
branch-residue amplitude, while their nonzero even-zeta quotient remains
branch-independent.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Inverse contact-connection tensor power at the parity grade `2r+1`. -/
def mobiusContactGammaBranchParityTensorScale
    (branch r : ℕ) : ℝ :=
  ‖(-2 - mobiusGammaContactPartialCharge branch) / 2‖⁻¹ ^ (2 * r + 1)

/-- **Möbius-contact Gamma branch-transported parity-residue universality
law.** Both adjacent parity channels transport to the same intrinsic
covariant residue at every pole branch; their projective even-zeta invariant
is connection-flat. -/
theorem mobiusContactGamma_branchTransportedParityResidueUniversality :
    ∀ (r branch : ℕ) (x : ℂ), x ≠ 0 →
      Tendsto (fun n =>
        (mobiusContactGammaBranchParityTensorScale branch r : ℂ) *
          mobiusContactGammaOddCorrection r n x) atTop
        (𝓝 (2 *
          ((‖GaloisForLFunctions.gammaPoleCovariantTopResidueValue branch
            (2 * r + 1) (Fin.last (2 * r + 1))‖ : ℂ) *
            riemannZeta ((2 * r + 2 : ℕ) : ℂ)))) ∧
      Tendsto (fun n =>
        (mobiusContactGammaBranchParityTensorScale branch r : ℂ) *
          mobiusContactGammaEvenFiniteTail r n x) atTop
        (𝓝 (-(‖GaloisForLFunctions.gammaPoleCovariantTopResidueValue branch
          (2 * r + 1) (Fin.last (2 * r + 1))‖ : ℂ))) ∧
      Tendsto (fun n => mobiusContactGammaCrossParityRatio r n x) atTop
        (𝓝 (-2 * riemannZeta ((2 * r + 2 : ℕ) : ℂ))) ∧
      -2 * riemannZeta ((2 * r + 2 : ℕ) : ℂ) ≠ 0 := by
  intro r branch x hx
  have hres :=
    mobiusContactGamma_completeConnectionTensorUniversality.2.2.2
      branch (2 * r + 1) (Fin.last (2 * r + 1))
  have hres' :
      ‖GaloisForLFunctions.gammaPoleCovariantTopResidueValue branch
          (2 * r + 1) (Fin.last (2 * r + 1))‖ =
        mobiusContactGammaBranchParityTensorScale branch r *
          (2 * r + 1).factorial := by
    simpa only [mobiusContactGammaBranchParityTensorScale, Fin.val_last] using hres
  have hresC :
      (‖GaloisForLFunctions.gammaPoleCovariantTopResidueValue branch
          (2 * r + 1) (Fin.last (2 * r + 1))‖ : ℂ) =
        (mobiusContactGammaBranchParityTensorScale branch r : ℂ) *
          ((2 * r + 1).factorial : ℂ) := by
    exact_mod_cast hres'
  have hodd :=
    (tendsto_mobiusContactGammaOddCorrection r hx).const_mul
      (mobiusContactGammaBranchParityTensorScale branch r : ℂ)
  have heven :=
    (tendsto_mobiusContactGammaEvenFiniteTail r hx).const_mul
      (mobiusContactGammaBranchParityTensorScale branch r : ℂ)
  refine ⟨?_, ?_, tendsto_mobiusContactGammaCrossParityRatio r hx,
    mobiusContactGammaCrossParityRatio_limit_ne_zero r⟩
  · convert hodd using 1
    rw [hresC]
    ring_nf
  · convert heven using 1
    rw [hresC]
    ring_nf

end

end GaloisForLFunctions.RHTower
