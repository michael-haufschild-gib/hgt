import GaloisForLFunctions.RHTower.InverseTiltedPrimeGammaCentralSource
import GaloisForLFunctions.RHTower.XiEndpointPrimeArchBoundaryLimit

/-!
# Xi endpoint universality of the inverse-tilted prime–Gamma source

The inverse-tilted finite dyadic prime source reconstructs the canonical continued prime–Gamma
trace at every regular centered point.  The canonical trace independently realizes the completed
Xi logarithmic curvature along a cofinal approach to the upper completion endpoint.  Their common
carrier identifies the concrete finite-prime source pointwise along that approach and transports
the endpoint limit to it.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Normalized inverse-tilted dyadic prime/Gamma source. -/
def normalizedInverseTiltedPrimeGammaSource (z : ℂ) : ℂ :=
  -inverseTiltedPrimeGammaSourceTrace z / z

/-- At every point of the explicit endpoint approach, the normalized inverse-tilted source is
exactly the canonical normalized continued prime–Gamma source. -/
theorem normalizedInverseTiltedPrimeGammaSource_xiEndpointApproach_eq (n : ℕ) :
    normalizedInverseTiltedPrimeGammaSource (xiEndpointApproach n) =
      normalizedContinuedPrimeArchSource (xiEndpointApproach n) := by
  let ε : ℝ := 1 / ((n : ℝ) + 3)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hden : (0 : ℝ) < (n : ℝ) + 3 := by linarith
  have hεpos : 0 < ε := by positivity
  have hεhalf : ε < 1 / 2 := by
    dsimp [ε]
    rw [div_lt_iff₀ hden]
    nlinarith
  have hεone : ε < 1 := lt_trans hεhalf (by norm_num)
  have hεC : xiEndpointEpsilon n = (ε : ℂ) := by
    simp [xiEndpointEpsilon, ε]
  have hs : 1 / 2 + xiEndpointApproach n * I = (ε : ℂ) := by
    rw [xiEndpointApproach, hεC]
    rw [mul_assoc, Complex.I_mul_I, mul_neg, mul_one]
    ring
  have hspos : 0 < (1 / 2 + xiEndpointApproach n * I).re := by
    rw [hs]
    simpa using hεpos
  have hs1 : 1 / 2 + xiEndpointApproach n * I ≠ 1 := by
    rw [hs]
    exact_mod_cast ne_of_lt hεone
  have hzeta : riemannZeta (1 / 2 + xiEndpointApproach n * I) ≠ 0 := by
    rw [hs]
    exact riemannZeta_real_strip_ne_zero hεpos hεone
  rw [normalizedInverseTiltedPrimeGammaSource,
    normalizedContinuedPrimeArchSource,
    inverseTiltedPrimeGammaSourceTrace_eq_continuedPrimeArchSourceRelativeTrace
      hspos hs1 hzeta]

/-- **Xi-endpoint inverse-tilted prime–Gamma source universality law.**  The concrete normalized
inverse-tilted finite-prime source equals the completed Xi logarithmic curvature at every cofinal
approach point and converges to its exact endpoint value. -/
theorem inverseTiltedPrimeGammaSource_endpointUniversality :
    (∀ n : ℕ,
      normalizedInverseTiltedPrimeGammaSource (xiEndpointApproach n) =
        -logDeriv XiC (xiEndpointApproach n) / xiEndpointApproach n) ∧
    Tendsto
      (fun n : ℕ => normalizedInverseTiltedPrimeGammaSource (xiEndpointApproach n))
      atTop (𝓝 (-logDeriv XiC (I / 2) / (I / 2))) := by
  constructor
  · intro n
    exact (normalizedInverseTiltedPrimeGammaSource_xiEndpointApproach_eq n).trans
      (xiEndpointApproach_source_eq n)
  · apply tendsto_normalizedContinuedPrimeArchSource_endpoint.congr'
    exact Filter.Eventually.of_forall fun n =>
      (normalizedInverseTiltedPrimeGammaSource_xiEndpointApproach_eq n).symm

end

end RHTower
