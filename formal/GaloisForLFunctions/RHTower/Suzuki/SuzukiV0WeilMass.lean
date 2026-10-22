import GaloisForLFunctions.RHTower.Suzuki.SuzukiModelWeilIsomorphism
import GaloisForLFunctions.RHTower.Suzuki.SuzukiDeBrangesSpace

noncomputable section

/-!
# The mass of `V(0)` in the Weil metric

Theorem 5.5 of the source, in the corpus's unitary Fourier normalisation: on `V(0)` the `L²` mass
and the Weil mass differ by exactly the factor `π`, and the composite `V(0) → K(Θ) → H_W` is the
isomorphism of Theorem 1.1 — its image has the spectral values of `𝖥ψ`.
-/

open MeasureTheory Set Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem mem_suzukiModelSpace_fourier_of_suzukiV0
    {ψ : Lp ℂ 2 (volume : Measure ℝ)} (hψ : ψ ∈ suzukiV0) :
    (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) ψ ∈ suzukiModelSpace := by
  rw [← map_fourier_suzukiV0]
  exact ⟨ψ, hψ, rfl⟩

section

variable [hRH : Fact RiemannHypothesis]

/-- **Theorem 5.5 (1).**  On `V(0)` the `L²` mass and the Weil mass agree up to the factor `π`.
(The corpus's Fourier transform is unitary, so the source's `‖ψ̂‖² = 2π‖ψ‖²` becomes `‖ψ̂‖² = ‖ψ‖²`
and the chain collapses to the two outer terms.) -/
theorem norm_sq_suzukiV0_eq_pi_mul_weil
    {ψ : Lp ℂ 2 (volume : Measure ℝ)} (hψ : ψ ∈ suzukiV0) :
    ‖ψ‖ ^ (2 : ℕ) = Real.pi * ‖suzukiModelWeilEquiv
      ⟨(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) ψ,
        mem_suzukiModelSpace_fourier_of_suzukiV0 hψ⟩‖ ^ (2 : ℕ) := by
  have hbase := norm_sq_suzukiModelWeilEquiv
    (⟨(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) ψ,
      mem_suzukiModelSpace_fourier_of_suzukiV0 hψ⟩ :
      ↥(suzukiModelSpace : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))))
  have hnorm : ‖((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) ψ)‖ = ‖ψ‖ :=
    (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).norm_map ψ
  rw [hnorm] at hbase
  exact hbase

/-- **Theorem 5.5 (2).**  The spectral values of the image of `𝖥ψ` are those of `𝖥ψ`, so the
composite `V(0) → K(Θ) → H_W` is the map of Theorem 1.1. -/
theorem suzukiWeilTauEquiv_suzukiV0
    {ψ : Lp ℂ 2 (volume : Measure ℝ)} (hψ : ψ ∈ suzukiV0) (ρ : XiDivisorSupport) :
    ((suzukiWeilTauEquiv (suzukiModelWeilEquiv
        ⟨(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) ψ,
          mem_suzukiModelSpace_fourier_of_suzukiV0 hψ⟩) : SuzukiTauSpace) :
        ∀ _ : XiDivisorSupport, ℂ) ρ
      = ((Real.sqrt (xiSupportMult ρ : ℝ) : ℝ) : ℂ)
        * suzukiRestriction hRH.out
            ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) ψ) ρ :=
  suzukiWeilTauEquiv_suzukiModelWeilEquiv _ ρ

end

end RHTower
