import GaloisForLFunctions.RHTower.PrimeArchConnesReflectionMain
import GaloisForLFunctions.RHTower.PrimeArchEndpointFrequencyAccretivity
import GaloisForLFunctions.RHTower.XiThermalSourceRelativeGapBound

/-!
# Connes--Born/Witten--KMS ultraviolet--infrared master law

The endpoint source controls both ends of the prime--archimedean reflection problem.  In the
central frequency band it makes the continued response unconditionally anti-Herglotz.  In the
reciprocal divisor picture it bounds the transverse thermal energy by less than five percent of
the positive second moment.  The remaining high-frequency response sign is exactly equivalent to
vanishing of that transverse energy, saturation by the explicit theta Born/Witten source value,
selection of the same value by the finite KMS thermodynamic limit, a Connes reflection-positive
Gram realization, and RH.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- **Connes--Born/Witten--KMS ultraviolet--infrared master theorem.**

For every endpoint-admissible radius, the first four conjuncts are unconditional.  The remaining
equivalence chain identifies one and the same sharp orientation datum in response, thermal,
thermodynamic-limit, reflection-positive, and divisor language. -/
theorem primeArchConnesBornWittenKMSFrequencyMaster
    (R : ℝ) (hband : XiEndpointAccretiveBand R) :
    (∀ z : ℂ, 0 < z.im → z.im < 1 / 2 → |z.re| ≤ R →
      (continuedPrimeArchSourceRelativeTrace z).im ≤ 0) ∧
    xiThermalOrientationEnergy <
      (1 / 20 : ℝ) * xiThermalSecondMoment ∧
    xiThermalSecondMoment - xiThermalOrientationEnergy =
      thetaCuspBornWittenQuadraticSource ∧
    thetaCuspBornWittenQuadraticSource ≤ xiThermalSecondMoment ∧
    (ContinuedPrimeArchPositiveFrequencyAbove R ↔
      xiThermalOrientationEnergy = 0) ∧
    (xiThermalOrientationEnergy = 0 ↔
      xiThermalSecondMoment = thetaCuspBornWittenQuadraticSource) ∧
    (xiThermalSecondMoment = thetaCuspBornWittenQuadraticSource ↔
      Tendsto (fun N => xiThermalTruncation N 1) atTop
        (nhds thetaCuspBornWittenQuadraticSource)) ∧
    (Tendsto (fun N => xiThermalTruncation N 1) atTop
        (nhds thetaCuspBornWittenQuadraticSource) ↔
      PrimeArchComplexReflectionPositiveGram) ∧
    (PrimeArchComplexReflectionPositiveGram ↔
      PrimeArchSelfAdjointVacuumRealization) ∧
    (PrimeArchSelfAdjointVacuumRealization ↔ RiemannHypothesis) := by
  have hhigh : ContinuedPrimeArchPositiveFrequencyAbove R ↔ RiemannHypothesis :=
    continuedPrimeArchPositiveFrequencyAbove_iff_riemannHypothesis R hband
  have henergy : xiThermalOrientationEnergy = 0 ↔ RiemannHypothesis :=
    xiThermalOrientationEnergy_eq_zero_iff_rh
  have hsource :
      xiThermalSecondMoment = thetaCuspBornWittenQuadraticSource ↔
        RiemannHypothesis :=
    xiThermalSecondMoment_eq_bornWittenSource_iff_rh
  have hlimit :
      Tendsto (fun N => xiThermalTruncation N 1) atTop
          (nhds thetaCuspBornWittenQuadraticSource) ↔ RiemannHypothesis :=
    tendsto_xiThermalTruncation_one_bornWittenSource_iff_rh
  have hgram : PrimeArchComplexReflectionPositiveGram ↔ RiemannHypothesis :=
    primeArchComplexReflectionPositiveGram_iff_riemannHypothesis
  have hvacuum : PrimeArchSelfAdjointVacuumRealization ↔ RiemannHypothesis :=
    primeArchSelfAdjointVacuumRealization_iff_riemannHypothesis
  refine ⟨?_, xiThermalOrientationEnergy_lt_one_twentieth_secondMoment,
    xiThermalSecondMoment_sub_orientationEnergy_eq_bornWittenSource,
    thetaCuspBornWittenQuadraticSource_le_thermalSecondMoment,
    hhigh.trans henergy.symm, henergy.trans hsource.symm,
    hsource.trans hlimit.symm, hlimit.trans hgram.symm,
    hgram.trans hvacuum.symm, hvacuum⟩
  intro z hzIm hzHalf hzRe
  exact continuedPrimeArchSourceRelativeTrace_im_nonpos_of_endpointBand
    R hband z hzIm hzHalf hzRe

/-- The fully explicit rational form of the master theorem.  Unconditionally, the complete
central band `|Re z| ≤ 161 / 40` is discharged; only the positive-frequency response above
`161 / 40` remains in the equivalent sharp conditions. -/
theorem primeArchConnesBornWittenKMSFrequencyMaster_oneSixtyOne_fortieths :
    (∀ z : ℂ, 0 < z.im → z.im < 1 / 2 → |z.re| ≤ 161 / 40 →
      (continuedPrimeArchSourceRelativeTrace z).im ≤ 0) ∧
    xiThermalOrientationEnergy <
      (1 / 20 : ℝ) * xiThermalSecondMoment ∧
    xiThermalSecondMoment - xiThermalOrientationEnergy =
      thetaCuspBornWittenQuadraticSource ∧
    thetaCuspBornWittenQuadraticSource ≤ xiThermalSecondMoment ∧
    (ContinuedPrimeArchPositiveFrequencyAbove (161 / 40) ↔
      xiThermalOrientationEnergy = 0) ∧
    (xiThermalOrientationEnergy = 0 ↔
      xiThermalSecondMoment = thetaCuspBornWittenQuadraticSource) ∧
    (xiThermalSecondMoment = thetaCuspBornWittenQuadraticSource ↔
      Tendsto (fun N => xiThermalTruncation N 1) atTop
        (nhds thetaCuspBornWittenQuadraticSource)) ∧
    (Tendsto (fun N => xiThermalTruncation N 1) atTop
        (nhds thetaCuspBornWittenQuadraticSource) ↔
      PrimeArchComplexReflectionPositiveGram) ∧
    (PrimeArchComplexReflectionPositiveGram ↔
      PrimeArchSelfAdjointVacuumRealization) ∧
    (PrimeArchSelfAdjointVacuumRealization ↔ RiemannHypothesis) :=
  primeArchConnesBornWittenKMSFrequencyMaster
    (161 / 40) xiEndpointAccretiveBand_oneSixtyOne_fortieths

end

end RHTower
