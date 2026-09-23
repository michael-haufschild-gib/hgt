import GaloisForLFunctions.RHTower.SoninPinchingUnitaryFrameProjectiveRayUniversalityLaw
import GaloisForLFunctions.HTGeometry.PureStateProjectorTangentInertia

/-!
# Sonin-pinching unitary-frame quantum-geometric saturation

The zero projective Gram energy forced by Sonin pinching is simultaneously zero quantum-Fisher
information, saturation of the quantum metric--Berry bound, complex two-channel dependence, and
degeneracy of the pure-state projector tangent in every unitary reference frame.
-/

open Complex
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- Full quantum-geometric collapse certificate for a framed Sonin scattering pair. -/
structure SoninPinchingQuantumGeometricSaturationCertificate
    (S : SoninL2 →L[ℂ] SoninL2)
    (u v u₀ v₀ : SoninL2) : Prop where
  physical :
    GaloisForLFunctions.PhysicalState (S - 1).toLinearMap u
  scatteringOrbit : v = S u
  projectiveEnergyTransport :
    HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ) u v =
      HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ) u₀ v₀
  projectiveEnergyZero :
    HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ) u v = 0
  pureStateQuantumFisherZero :
    HTGeometry.pureStateQuantumFisherValue
      (‖u‖ ^ (2 : ℕ)) (‖inner ℂ u v‖) (‖v‖ ^ (2 : ℕ)) = 0
  quantumMetricBerrySaturated :
    HTGeometry.quantumMetricAreaValue u v =
      HTGeometry.berryCurvatureValue u v ^ (2 : ℕ) / 4
  gramDetZero :
    (Matrix.gram ℂ ![u, v]).det = 0
  pairDependent :
    ¬ LinearIndependent ℂ ![u, v]
  projectorTangentHermitian :
    (HTGeometry.pureStateProjectorTangentCompression u v).IsHermitian
  projectorTangentDetZero :
    (HTGeometry.pureStateProjectorTangentCompression u v).det = 0

/--
**Sonin-pinching unitary-frame quantum-geometric saturation law.**

Every framed Sonin pinching ray simultaneously saturates every generic quantum-geometric consumer
of projective Gram energy.
-/
theorem soninLogPinching_unitaryFrameQuantumGeometricSaturation
    (X V : SoninL2 →L[ℂ] SoninL2)
    {ψ : SoninL2} (hψnorm : ‖ψ‖ = 1)
    (hψ : GaloisForLFunctions.PhysicalState
      (soninLogFourierScattering - 1).toLinearMap ψ)
    (hleft : V.adjoint * V = 1) (hright : V * V.adjoint = 1) :
    let Y := HTGeometry.twoOutcomePinching soninLogFourierInvariantAverage X
    let S := V * soninLogFourierScattering * V.adjoint
    let u := V (Y ψ)
    let v := S u
    SoninPinchingQuantumGeometricSaturationCertificate
      S u v (Y ψ) (soninLogFourierScattering (Y ψ)) := by
  dsimp only
  let Y := HTGeometry.twoOutcomePinching soninLogFourierInvariantAverage X
  let S := V * soninLogFourierScattering * V.adjoint
  let u := V (Y ψ)
  let v := S u
  change SoninPinchingQuantumGeometricSaturationCertificate
    S u v (Y ψ) (soninLogFourierScattering (Y ψ))
  have hsonin :=
    soninLogPinching_unitaryFrameProjectiveRayUniversality
      X V hψnorm hψ hleft hright
  have hphysical :
      GaloisForLFunctions.PhysicalState (S - 1).toLinearMap u := by
    simpa only [Y, S, u] using hsonin.1
  have htransport :
      HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ) u v =
        HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ) (Y ψ)
          (soninLogFourierScattering (Y ψ)) := by
    simpa only [Y, S, u, v] using hsonin.2.1
  have hzero :
      HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ) u v = 0 := by
    simpa only [Y, S, u, v] using hsonin.2.2
  have hvalue :
      HTGeometry.projectiveQuantumTangentValue
        (‖u‖ ^ (2 : ℕ)) (‖inner ℂ u v‖) (‖v‖ ^ (2 : ℕ)) = 0 := by
    rw [← HTGeometry.projectiveGramTangentEnergy_eq_value]
    exact hzero
  have hqfi :
      HTGeometry.pureStateQuantumFisherValue
        (‖u‖ ^ (2 : ℕ)) (‖inner ℂ u v‖) (‖v‖ ^ (2 : ℕ)) = 0 := by
    rw [HTGeometry.pureStateQuantumFisherValue, hvalue]
    norm_num
  have hmetric :
      HTGeometry.quantumMetricAreaValue u v =
        HTGeometry.berryCurvatureValue u v ^ (2 : ℕ) / 4 := by
    rw [HTGeometry.quantumMetricAreaValue_eq_projectiveGram_add_berry,
      hzero, zero_add]
  have hgram : (Matrix.gram ℂ ![u, v]).det = 0 := by
    rw [HTGeometry.det_gram_pair_eq_projectiveGramTangentEnergy, hzero]
    norm_num
  have hdependent : ¬ LinearIndependent ℂ ![u, v] :=
    (HTGeometry.quantumMetricArea_eq_berry_iff_not_linearIndependent_pair
      u v).mp hmetric
  have hprojector :
      (HTGeometry.pureStateProjectorTangentCompression u v).det = 0 := by
    rw [HTGeometry.det_pureStateProjectorTangentCompression_eq_neg_projectiveEnergy_sq,
      hzero]
    norm_num
  exact
    { physical := hphysical
      scatteringOrbit := rfl
      projectiveEnergyTransport := htransport
      projectiveEnergyZero := hzero
      pureStateQuantumFisherZero := hqfi
      quantumMetricBerrySaturated := hmetric
      gramDetZero := hgram
      pairDependent := hdependent
      projectorTangentHermitian :=
        HTGeometry.pureStateProjectorTangentCompression_isHermitian u v
      projectorTangentDetZero := hprojector }

end

end RHTower
