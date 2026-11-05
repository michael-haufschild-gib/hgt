import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilRieszVectorsHaveNormalizedEndpointTraces
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilRemainderMultiplier

/-!
# Continuous prime and polar responses of actual Weil Riesz sources

A continuous source gives a continuous full finite-prime response. Its two
polar moments multiply the exact exponential profiles. On an enclosing
aperture, this continuous expression represents the complete bounded Weil
remainder, including its scalar term.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry
open ArithmeticContinuationAndCriticalEnergy

private theorem symmetricTranslation_representative (t : ℝ) (f : SoninL2)
    (U : ℝ → ℂ) (hU : U =ᵐ[volume] f) :
    (ccmSymmetricLogTranslation t f : ℝ → ℂ) =ᵐ[volume]
      fun x => U (x+t)+U (x-t) := by
  have hp := hU.comp_tendsto
    (MellinL2.realTranslation_measurePreserving t).quasiMeasurePreserving.tendsto_ae
  have hm := hU.comp_tendsto
    (MellinL2.realTranslation_measurePreserving (-t)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [Lp.coeFn_add (logTranslationCLM t f) (logTranslationCLM (-t) f),
    logarithmicTranslation_coeFn t f, logarithmicTranslation_coeFn (-t) f, hp, hm]
      with x ha ht hn hp hm
  change (logTranslationCLM t f+logTranslationCLM (-t) f) x = _
  rw [ha, Pi.add_apply, ht, hn]
  change U (x+t) = f (x+t) at hp
  change U (x+-t) = f (x+-t) at hm
  rw [← hp, ← hm, ← sub_eq_add_neg]

private theorem primeSum_representative (S : Finset ℕ) (f : SoninL2)
    (U : ℝ → ℂ) (hU : U =ᵐ[volume] f) :
    ((∑ n ∈ S, (criticalMellinAtomWeight n : ℂ) •
      ccmSymmetricLogTranslation (Real.log n) f : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∑ n ∈ S, (criticalMellinAtomWeight n : ℂ)*(U (x+Real.log n)+U (x-Real.log n)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact Lp.coeFn_zero ℂ 2 volume
  | @insert n S hn ih =>
      rw [Finset.sum_insert hn]
      filter_upwards [Lp.coeFn_add
        ((criticalMellinAtomWeight n : ℂ) • ccmSymmetricLogTranslation (Real.log n) f)
        (∑ k ∈ S, (criticalMellinAtomWeight k : ℂ) • ccmSymmetricLogTranslation (Real.log k) f),
        Lp.coeFn_smul (criticalMellinAtomWeight n : ℂ) (ccmSymmetricLogTranslation (Real.log n) f),
        symmetricTranslation_representative (Real.log n) f U hU, ih] with x ha hs ht hi
      rw [ha, Pi.add_apply, hs, Pi.smul_apply, smul_eq_mul, ht, hi, Finset.sum_insert hn]

private theorem finitePrime_representative (b : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert b) (U : ℝ → ℂ) (hU : U =ᵐ[volume] (f : SoninL2)) :
    ((ccmFinitePrimeOperator b f : suzukiApertureHilbert b) : ℝ → ℂ) =ᵐ[volume]
      (centralInterval b.1).indicator (fun x =>
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*b.1)⌋₊,
          (criticalMellinAtomWeight n : ℂ)*(U (x+Real.log n)+U (x-Real.log n))) := by
  have hp : (ccmFullLinePrimeOperator b (f : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*b.1)⌋₊,
        (criticalMellinAtomWeight n : ℂ)*(U (x+Real.log n)+U (x-Real.log n)) := by
    simpa only [ccmFullLinePrimeOperator, sum_apply, smul_apply] using
      primeSum_representative (Finset.Icc 2 ⌊Real.exp (2*b.1)⌋₊) (f : SoninL2) U hU
  rw [ccmFinitePrimeOperator_eq_compressed_fullLine]
  change (ccmApertureCompression b (ccmFullLinePrimeOperator b) f : SoninL2) =ᵐ[volume] _
  rw [ccmApertureCompression_val]
  filter_upwards [indicatorCutoff_ae (centralInterval b.1) (measurableSet_centralInterval b.1)
    (ccmFullLinePrimeOperator b (f : SoninL2)), hp] with x hc hp
  rw [hc]
  by_cases hx : x ∈ centralInterval b.1
  · rw [indicator_of_mem hx, indicator_of_mem hx, hp]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx]

private theorem polar_representative (b : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert b) :
    ((ccmPolarOperator b f : suzukiApertureHilbert b) : ℝ → ℂ) =ᵐ[volume]
      (centralInterval b.1).indicator (fun x =>
        inner ℂ (ccmPolarApertureVector b (-1/2)) f * ccmPolarProfile (1/2) x +
        inner ℂ (ccmPolarApertureVector b (1/2)) f * ccmPolarProfile (-1/2) x) := by
  let c := inner ℂ (ccmPolarApertureVector b (-1/2)) f
  let d := inner ℂ (ccmPolarApertureVector b (1/2)) f
  have he : (ccmPolarOperator b f : SoninL2) =
      c • ccmPolarL2Vector b (1/2)+d • ccmPolarL2Vector b (-1/2) := rfl
  change (ccmPolarOperator b f : SoninL2) =ᵐ[volume] _
  rw [he]
  filter_upwards [Lp.coeFn_add (c • ccmPolarL2Vector b (1/2)) (d • ccmPolarL2Vector b (-1/2)),
    Lp.coeFn_smul c (ccmPolarL2Vector b (1/2)), Lp.coeFn_smul d (ccmPolarL2Vector b (-1/2)),
    ccmPolarL2Vector_coeFn b (1/2), ccmPolarL2Vector_coeFn b (-1/2)] with x ha hc hd hp hm
  rw [ha, Pi.add_apply, hc, hd, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, hp, hm]
  by_cases hx : x ∈ centralInterval b.1
  · simp only [indicator_of_mem hx, c, d]
  · simp only [indicator_of_notMem hx, mul_zero, add_zero]

/-- The full continuous finite-prime, polar, and scalar response before aperture compression. -/
def continuousWeilRemainderProfile (b : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert b) (U : ℝ → ℂ) (x : ℝ) : ℂ :=
  ccmArchimedeanRemainderScalar*U x +
    (inner ℂ (ccmPolarApertureVector b (-1/2)) f * ccmPolarProfile (1/2) x +
      inner ℂ (ccmPolarApertureVector b (1/2)) f * ccmPolarProfile (-1/2) x) -
    ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*b.1)⌋₊,
      (criticalMellinAtomWeight n : ℂ)*(U (x+Real.log n)+U (x-Real.log n))

theorem continuous_continuousWeilRemainderProfile (b : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert b) {U : ℝ → ℂ} (hU : Continuous U) :
    Continuous (continuousWeilRemainderProfile b f U) := by
  unfold continuousWeilRemainderProfile ccmPolarProfile
  fun_prop

/-- The continuous expression is the actual bounded remainder on the whole enclosing aperture. -/
theorem continuousWeilRemainderProfile_ae (b : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert b) (U : ℝ → ℂ) (hU : U =ᵐ[volume] (f : SoninL2)) :
    ((ccmRestrictedWeilBoundedRemainder b f : suzukiApertureHilbert b) : ℝ → ℂ) =ᵐ[
      volume.restrict (centralInterval b.1)] continuousWeilRemainderProfile b f U := by
  have he : (ccmRestrictedWeilBoundedRemainder b f : SoninL2) =
      (ccmArchimedeanRemainderScalar • (f : SoninL2) + (ccmPolarOperator b f : SoninL2)) -
        (ccmFinitePrimeOperator b f : SoninL2) := rfl
  change (ccmRestrictedWeilBoundedRemainder b f : SoninL2) =ᵐ[_] _
  rw [he]
  filter_upwards [ae_restrict_mem (measurableSet_centralInterval b.1),
    ae_restrict_of_ae (Lp.coeFn_sub
      (ccmArchimedeanRemainderScalar • (f : SoninL2)+(ccmPolarOperator b f : SoninL2))
      (ccmFinitePrimeOperator b f : SoninL2)),
    ae_restrict_of_ae (Lp.coeFn_add (ccmArchimedeanRemainderScalar • (f : SoninL2))
      (ccmPolarOperator b f : SoninL2)),
    ae_restrict_of_ae (Lp.coeFn_smul ccmArchimedeanRemainderScalar (f : SoninL2)),
    ae_restrict_of_ae (polar_representative b f),
    ae_restrict_of_ae (finitePrime_representative b f U hU), ae_restrict_of_ae hU]
      with x hx hs ha hc hp hpr hu
  rw [hs, Pi.sub_apply, ha, Pi.add_apply, hc, Pi.smul_apply, smul_eq_mul, hp, hpr,
    indicator_of_mem hx, indicator_of_mem hx, ← hu]
  rfl

namespace WeilHilbertBeforeContact

/-- The actual Riesz source's prime and polar response in any enclosing aperture. -/
def evalVectorRemainderProfile (a : PrecontactAperture) (b : SuzukiPositiveAperture)
    (hab : a.1.1 ≤ b.1) (z : ℂ) : ℝ → ℂ :=
  continuousWeilRemainderProfile b
    (ccmArchimedeanFormToAperture b (apertureExt hab (toForm a (evalVector a z))))
    (evalVectorContinuousRepresentative a z)

theorem continuous_evalVectorRemainderProfile (a : PrecontactAperture) (b : SuzukiPositiveAperture)
    (hab : a.1.1 ≤ b.1) (z : ℂ) : Continuous (evalVectorRemainderProfile a b hab z) :=
  continuous_continuousWeilRemainderProfile b _ (continuous_evalVectorContinuousRepresentative a z)

/-- No prime or polar input is omitted in the actual continuous remainder representative. -/
theorem evalVectorRemainderProfile_ae (a : PrecontactAperture) (b : SuzukiPositiveAperture)
    (hab : a.1.1 ≤ b.1) (z : ℂ) :
    ((ccmRestrictedWeilBoundedRemainder b
      (ccmArchimedeanFormToAperture b (apertureExt hab (toForm a (evalVector a z))))) : ℝ → ℂ) =ᵐ[
        volume.restrict (centralInterval b.1)] evalVectorRemainderProfile a b hab z := by
  apply continuousWeilRemainderProfile_ae
  have he := ccmArchimedeanFormToAperture_coe_eq_of_val_eq
    (apertureExt_val hab (toForm a (evalVector a z)))
  rw [he]
  exact evalVectorContinuousRepresentative_ae a z

#print axioms continuous_evalVectorRemainderProfile
#print axioms evalVectorRemainderProfile_ae
end WeilHilbertBeforeContact
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
