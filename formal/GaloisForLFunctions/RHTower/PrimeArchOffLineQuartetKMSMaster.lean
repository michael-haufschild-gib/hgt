import GaloisForLFunctions.RHTower.PrimeArchOffLineQuartetAccretivity
import GaloisForLFunctions.RHTower.PrimeArchConnesBornWittenKMSMaster

/-!
# Off-line quartet Connes--Born/Witten--KMS master law

The four-orbit endpoint amplification enlarges the unconditional central response band in the
existing Connes--Born/Witten--KMS master theorem from `161/40` to `87/10`.  It leaves the exact
orientation equivalences unchanged: the surviving positive-frequency response, vanishing thermal
orientation, thermodynamic source-value convergence, reflection positivity, a self-adjoint vacuum
realization, and RH still carry precisely the same datum.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- **Off-line quartet ultraviolet--infrared master theorem.**  The entire centered response band
through `87/10` is unconditional.  All remaining clauses are equivalent sharp orientation data. -/
theorem primeArchOffLineQuartetConnesBornWittenKMSMaster :
    (∀ z : ℂ, 0 < z.im → z.im < 1 / 2 → |z.re| ≤ 87 / 10 →
      (continuedPrimeArchSourceRelativeTrace z).im ≤ 0) ∧
    xiThermalOrientationEnergy <
      (1 / 20 : ℝ) * xiThermalSecondMoment ∧
    xiThermalSecondMoment - xiThermalOrientationEnergy =
      thetaCuspBornWittenQuadraticSource ∧
    thetaCuspBornWittenQuadraticSource ≤ xiThermalSecondMoment ∧
    (ContinuedPrimeArchPositiveAboveEightySevenTenthsUpperAntiHerglotz ↔
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
  have hhigh :
      ContinuedPrimeArchPositiveAboveEightySevenTenthsUpperAntiHerglotz ↔
        RiemannHypothesis :=
    continuedPrimeArchPositiveAboveEightySevenTenths_iff_riemannHypothesis
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
  exact continuedPrimeArchSourceRelativeTrace_im_nonpos_eightySeven_tenths
    z hzIm hzHalf hzRe

end

end RHTower
