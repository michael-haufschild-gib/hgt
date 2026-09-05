import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaAmplitudeEnergyCompiler
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaAmplitudeInstances
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobiAmplitudeEnergy
import Mathlib.Tactic

/-!
# Region I and II energy instances

The generic compiler Hamiltonian agrees exactly with the separately derived Jacobi energies in
both real regions.  This gives an independent ODE-level conservation proof and adds the missing
derivative conservation law on Region II.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

theorem regionIAmplitudeOscillatorEnergy_eq
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (x : ℝ) :
    amplitudeOscillatorEnergy (regionIAmplitudeOscillator P J) x =
      correctedJacobiAmplitudeEnergy P J x := by
  rw [amplitudeOscillatorEnergy, correctedJacobiAmplitudeEnergy]
  change
    correctedJacobiAmplitudeVelocity P J x ^ 2 / 2 +
        (P.val.q₀ : ℝ) * correctedJacobiAmplitude P J x ^ 4 / 2 +
        (P.val.q₀ : ℝ) * physicalGamma P ^ 2 *
          correctedJacobiAmplitude P J x ^ 2 / 2 +
        (P.val.q₀ : ℝ) * physicalNu P ^ 2 /
          (2 * correctedJacobiAmplitude P J x ^ 2) = _
  rw [physicalGamma_sq, physicalNu_sq]

theorem regionIAmplitudeOscillatorEnergy_const
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (x y : ℝ) :
    correctedJacobiAmplitudeEnergy P J x = correctedJacobiAmplitudeEnergy P J y := by
  rw [← regionIAmplitudeOscillatorEnergy_eq P J x,
    ← regionIAmplitudeOscillatorEnergy_eq P J y]
  exact amplitudeOscillatorEnergy_const (regionIAmplitudeOscillator P J) x y

theorem regionIIAmplitudeOscillatorEnergy_eq
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (x : ℝ) :
    amplitudeOscillatorEnergy (regionIIAmplitudeOscillator P J) x =
      regionIIJacobiAmplitudeEnergy P J x := by
  rw [amplitudeOscillatorEnergy, regionIIJacobiAmplitudeEnergy]
  change
    regionIIJacobiAmplitudeVelocity P J x ^ 2 / 2 +
        regionIIRealScale P * regionIIJacobiAmplitude P J x ^ 4 / 2 +
        regionIIRealScale P * regionIIGamma P ^ 2 *
          regionIIJacobiAmplitude P J x ^ 2 / 2 +
        regionIIRealScale P * regionIINu P ^ 2 /
          (2 * regionIIJacobiAmplitude P J x ^ 2) = _
  rw [regionIIGamma_sq, regionIINu_sq]

theorem regionIIJacobiAmplitudeEnergy_const
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (x y : ℝ) :
    regionIIJacobiAmplitudeEnergy P J x = regionIIJacobiAmplitudeEnergy P J y := by
  rw [← regionIIAmplitudeOscillatorEnergy_eq P J x,
    ← regionIIAmplitudeOscillatorEnergy_eq P J y]
  exact amplitudeOscillatorEnergy_const (regionIIAmplitudeOscillator P J) x y

theorem regionIIJacobiAmplitudeEnergy_hasDerivAt_zero
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (x : ℝ) :
    HasDerivAt (regionIIJacobiAmplitudeEnergy P J) 0 x := by
  have h := amplitudeOscillatorEnergy_hasDerivAt_zero
    (regionIIAmplitudeOscillator P J) x
  apply h.congr_of_eventuallyEq
  filter_upwards with y
  exact (regionIIAmplitudeOscillatorEnergy_eq P J y).symm

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
