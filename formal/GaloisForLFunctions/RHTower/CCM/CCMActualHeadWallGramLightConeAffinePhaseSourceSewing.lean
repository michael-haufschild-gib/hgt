import GaloisForLFunctions.RHTower.CCM.CCMActualHeadWallGramLightConeAffinePhaseJet

/-!
# Source sewing for the affine completion of the actual CCM wall Gram

The canonical completed wall phase has a nonzero zero-clock atom and an oriented first jet, but
those local facts only matter for Route O if they retain the literal completed arithmetic source.
This file gives that exact landing.  Its real deficit is pointwise the reflected chord energy;
therefore summing that deficit against the actual finite-head density produces precisely the
original prime channel.  Substitution into the signed producer is an identity, so the
prime--polar--Gamma cancellation is neither estimated nor separated.

This is not a positivity theorem.  On canonical Gamma--Slepian heads, nonnegativity of the sewn
producer remains equivalent to the literal reverse-prime bound.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

/-- A coefficient-faithful affine phase for every natural Mellin wall atom.  The real coordinate
is its reflected-chord deficit and the imaginary coordinate is the oriented positive-clock
coordinate. -/
def ccmActualHeadMellinWallAffinePhase (xi : ℝ) (n : ℕ) : ℂ :=
  let theta : ℝ := 2 * Real.pi * xi * Real.log (n : ℝ)
  let light : ℝ := criticalMellinAtomWeight n * Real.sin theta
  ((criticalMellinAtomWeight n -
      normSq (ccmActualHeadMellinWallChord xi n) / 2 : ℝ) : ℂ) +
    I * (light : ℂ)

/-- The real affine deficit recovers exactly the reflected chord energy, with no discarded
remainder. -/
theorem normSq_ccmActualHeadMellinWallChord_eq_two_mul_weight_sub_re_affinePhase
    (xi : ℝ) (n : ℕ) :
    normSq (ccmActualHeadMellinWallChord xi n) =
      2 * (criticalMellinAtomWeight n -
        (ccmActualHeadMellinWallAffinePhase xi n).re) := by
  simp only [ccmActualHeadMellinWallAffinePhase, add_re, ofReal_re, mul_re,
    I_re, I_im, ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  ring

/-- At every genuine prime power, the natural-indexed affine phase is the literal completed
Suzuki wall phase. -/
theorem ccmActualHeadMellinWallAffinePhase_primePower_eq_completedPhase
    (xi : ℝ) (p : Nat.Primes) (e : ℕ) :
    ccmActualHeadMellinWallAffinePhase xi (xiGammaEulerValuationNat (p, e)) =
      ccmActualHeadWallLightCompletedPhase xi p e := by
  apply Complex.ext
  · simp only [ccmActualHeadMellinWallAffinePhase,
      ccmActualHeadWallLightCompletedPhase, add_re, ofReal_re, mul_re, I_re,
      I_im, ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  · simp only [ccmActualHeadMellinWallAffinePhase,
      ccmActualHeadWallLightCompletedPhase, add_im, ofReal_im, mul_im, I_re,
      I_im, ofReal_re, zero_mul, one_mul, zero_add]
    rw [ccmActualHeadMatchedWallLightImbalance_eq]
    ring

/-- The literal finite prime channel, retained as the real deficit of the affine phase. -/
def ccmActualHeadPrimeWallAffinePhaseEnergy
    (a : SuzukiPositiveAperture) (g : SoninL2) : ℝ :=
  ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
    ∫ xi : ℝ,
      (2 * (criticalMellinAtomWeight n -
        (ccmActualHeadMellinWallAffinePhase xi n).re)) * ‖g xi‖ ^ 2

/-- Phase-deficit energy is definitionally coefficient-faithful to the actual finite wall-chord
energy. -/
theorem ccmActualHeadPrimeWallAffinePhaseEnergy_eq_chordEnergy
    (a : SuzukiPositiveAperture) (g : SoninL2) :
    ccmActualHeadPrimeWallAffinePhaseEnergy a g =
      ccmActualHeadPrimeWallChordEnergy a g := by
  unfold ccmActualHeadPrimeWallAffinePhaseEnergy ccmActualHeadPrimeWallChordEnergy
  apply Finset.sum_congr rfl
  intro n hn
  apply integral_congr_ae
  filter_upwards with xi
  rw [normSq_ccmActualHeadMellinWallChord_eq_two_mul_weight_sub_re_affinePhase]

/-- The completed prime--polar--Gamma source with its prime channel expressed by the actual
affine phase. -/
def ccmRestrictedWeilActualHeadWallAffinePhaseSignedProducer
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) : ℝ :=
  let f := ccmArchimedeanFormToAperture a u
  let g := ccmArchimedeanWeightedToL2 u.1
  2 * gammaHardyPhaseRate 0 * ‖f‖ ^ 2 +
    ccmActualHeadGammaAutocorrelationEnergy (f : SoninL2) +
    criticalMellinCompletedError (2 * a.1) *
      ccmActualHeadTranslationDefect (2 * a.1) f.1 +
    ccmActualHeadPrimeWallAffinePhaseEnergy a g -
      ccmContinuousPolarTranslationDefectEnergy a f

/-- The sewn affine producer is exactly the prior actual-head wall-Gram producer. -/
theorem ccmRestrictedWeilActualHeadWallAffinePhaseSignedProducer_eq_wallGramSignedProducer
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilActualHeadWallAffinePhaseSignedProducer a u =
      ccmRestrictedWeilActualHeadWallGramSignedProducer a u := by
  rw [ccmRestrictedWeilActualHeadWallAffinePhaseSignedProducer,
    ccmRestrictedWeilActualHeadWallGramSignedProducer,
    ccmActualHeadPrimeWallAffinePhaseEnergy_eq_chordEnergy]

/-- Exact completed-source law for the coefficient-faithful affine phase realization. -/
theorem ccmRestrictedWeilActualHeadWallAffinePhaseSignedProducer_eq_sourceQuadratic
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilActualHeadWallAffinePhaseSignedProducer a u =
      ccmRestrictedWeilSourceQuadratic a u := by
  rw [ccmRestrictedWeilActualHeadWallAffinePhaseSignedProducer_eq_wallGramSignedProducer,
    ccmRestrictedWeilActualHeadWallGramSignedProducer_eq_sourceQuadratic]

/-- The RH-bearing canonical-head condition is unchanged by affine source sewing. -/
theorem ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_wallAffinePhaseSignedProducer_nonneg
    (a : SuzukiPositiveAperture) (n : ℕ) :
    CCMRestrictedWeilCanonicalGroundHeadReversePrimeBound a n ↔
      0 ≤ ccmRestrictedWeilActualHeadWallAffinePhaseSignedProducer a
        (ccmRestrictedWeilCanonicalGroundHead a n) := by
  rw [ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_wallGramSignedProducer_nonneg,
    ccmRestrictedWeilActualHeadWallAffinePhaseSignedProducer_eq_wallGramSignedProducer]

end RHTower
