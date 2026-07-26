import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodNormalCrossingPrimeFace

/-!
# Theta-likelihood prime normal-tangent universality

On every prime shell, all nonzero normalized sections of the paired normal-crossing face coincide
with the unique one-sided tangent of the nonlinear scaled likelihood shell.  The identification
holds simultaneously for the phase and its spectral derivative, and the common tangent preserves
the strict arithmetic orientation in the upper half-plane.
-/

open Real Set Filter Topology

namespace RHTower

noncomputable section

/-- **Prime normal-tangent universality law.**  Every nonzero normal-crossing section is exactly
the one-sided nonlinear boundary tangent, at both value and spectral-derivative level.  Their
common Hermitian current is strictly negative in the upper half-plane. -/
theorem thetaCuspLikelihood_primeNormalTangentUniversality
    {k : ℕ} (hk : k.Prime) {B₀ : ℝ} (hB₀ : B₀ ≠ 0)
    {z : ℂ} (hz : 0 < z.im) :
    Tendsto
        (fun B : ℝ => (B : ℂ)⁻¹ *
          thetaCuspLikelihoodScaledMassShellPhase k B z)
        (𝓝[>] 0)
        (𝓝 ((B₀ : ℂ)⁻¹ *
          thetaCuspLikelihoodTwoFaceMassShellPhase k B₀ z)) ∧
      Tendsto
        (fun B : ℝ => (B : ℂ)⁻¹ *
          thetaCuspLikelihoodScaledMassShellPhaseDerivative k B z)
        (𝓝[>] 0)
        (𝓝 ((B₀ : ℂ)⁻¹ *
          thetaCuspLikelihoodTwoFaceMassShellPhaseDerivative k B₀ z)) ∧
      ((((B₀ : ℂ)⁻¹ *
            thetaCuspLikelihoodTwoFaceMassShellPhaseDerivative k B₀ z) *
          (starRingEnd ℂ) ((B₀ : ℂ)⁻¹ *
            thetaCuspLikelihoodTwoFaceMassShellPhase k B₀ z)).im < 0) := by
  have hface :=
    thetaCuspLikelihoodTwoFaceMassShellPhase_div_eq_primeConormal hk hB₀ z
  have hfaceDerivative :=
    thetaCuspLikelihoodTwoFaceMassShellPhaseDerivative_div_eq_primeConormal
      hk hB₀ z
  refine ⟨?_, ?_, ?_⟩
  · rw [hface]
    exact
      tendsto_thetaCuspLikelihoodScaledPrimeMassShellPhase_div_nhdsGT_zero hk z
  · rw [hfaceDerivative]
    exact
      tendsto_thetaCuspLikelihoodScaledPrimeMassShellPhaseDerivative_div_nhdsGT_zero hk z
  · rw [hface, hfaceDerivative]
    exact thetaCuspLikelihoodPrimeFirstBoundaryLayer_current_lt_zero hk hz

end

end RHTower
