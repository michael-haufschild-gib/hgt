import GaloisForLFunctions.FamilyContinuationTheory.GrossencharacterLFunctionsHaveZerosInTheRightHalfStrip
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.MarkedIdealSeries
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.RawNestingAndRadialExchange

/-! # Angular weight in the free sixth-power factor

The actual sixth-power frequency decomposition converts angular weight `k` into
ideal weight `6k`. The resulting Euler product continues regularly and nonvanishingly
through `z = 1/6`, where the untwisted free factor has its pole.
-/

noncomputable section
set_option autoImplicit false
open Complex Filter NumberField IsDedekindDomain
open scoped Classical BigOperators Topology

namespace GaloisForLFunctions.FamilyContinuationTheory
open HeckeLFunctions MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
open MetaplecticMobiusDescent.CubicEisenstein
open MetaplecticMobiusDescent.CubicEisenstein.ProbePhysical
open MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve
open MetaplecticMobiusDescent.CubicEisenstein.HeckeInverseAmplification

/-- A frequency angular twist changes the sixth-power invariance into an exact
Grössencharacter transformation law. -/
theorem angular_bareSourceCoefficient_sixth_frequency (k : ℕ) (η : HeckeFamily.Character)
    (I : Ideal O) (hI : primaryIdealGenerator I ≠ 0) (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (v H : O) (hcop : IsCoprime v (A * s)) :
    elemPsiSix (v ^ 6 * H) ^ k *
      bareSourceCoefficient η I hI A s
        (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) (v ^ 6 * H) =
      elemPsiSix v ^ (6 * k) * (elemPsiSix H ^ k *
        bareSourceCoefficient η I hI A s
          (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) H) := by
  rw [bareSourceCoefficient_sixth_frequency η I hI A s hA hs v H hcop,
    map_mul, map_pow, mul_pow, ← pow_mul, mul_assoc]

/-- The angular weight on a generator's sixth power is the ideal character of weight `6k`. -/
theorem angular_sixth_generator (k : ℕ) (I : Ideal O) :
    elemPsiSix ((Submodule.IsPrincipal.generator I) ^ 6) ^ k = idealPsiSix I ^ (6 * k) := by
  rw [map_pow, ← pow_mul]
  rfl

/-- The unique sixth-power decomposition transfers angular weight `k` to weight `6k`
on its free ideal variable. -/
theorem angular_sixthFrequency (k : ℕ)
    (p : FreeRow × HeckeInverseAmplification.NonzeroIdeal) :
    elemPsiSix (sixthFrequencyEquiv p).val ^ k =
      elemPsiSix p.1.val ^ k * idealPsiSix p.2.val ^ (6 * k) := by
  rw [sixthFrequencyEquiv_apply, map_mul, map_pow, mul_pow, ← pow_mul,
    ← idealPsiSix_span_singleton (cubicIdealGenerator p.2.val), span_cubicIdealGenerator]

/-- Angular and Mellin weights separate together under the actual sixth-power
frequency parametrization. -/
theorem angular_sixthFrequencyWeight (k : ℕ)
    (p : FreeRow × HeckeInverseAmplification.NonzeroIdeal) (z : ℂ) :
    elemPsiSix (sixthFrequencyEquiv p).val ^ k * frequencyWeight z (sixthFrequencyEquiv p) =
      (elemPsiSix p.1.val ^ k * frequencyWeight z ⟨p.1.val, p.1.property.1⟩) *
        (idealPsiSix p.2.val ^ (6 * k) * fullIdealWeight (6 * z) p.2.val) := by
  rw [angular_sixthFrequency, sixthFrequencyWeight]
  ring

/-- The free sixth-power Euler factor after moving the angular character to frequency. -/
def angularSixthEulerProduct (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    (S : Finset (HeightOneSpectrum O)) (z : ℂ) : ℂ :=
  ∏' v : {v : HeightOneSpectrum O // v ∉ S},
    (1 - elemPsiSix ((Submodule.IsPrincipal.generator v.1.asIdeal) ^ 6) ^ k *
      heckeValue 𝔪 ψ v.1.asIdeal * (primeNorm v.1 : ℂ) ^ (-(6 * z)))⁻¹

theorem angularSixthEulerProduct_eq (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    (k : ℕ) (S : Finset (HeightOneSpectrum O)) (z : ℂ) :
    angularSixthEulerProduct 𝔪 ψ k S z = grossenEulerProductModS 𝔪 ψ (6 * k) S (6 * z) := by
  unfold angularSixthEulerProduct grossenEulerProductModS
  simp_rw [angular_sixth_generator]

/-- Holomorphic continuation of the angular free sixth-power factor. -/
def continuedAngularSixthFactor (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    (S : Finset (HeightOneSpectrum O)) (z : ℂ) : ℂ :=
  grossenLFunction 𝔪 ψ (6 * k) (6 * z) * grossenDeletedFactors 𝔪 ψ (6 * k) S (6 * z)

theorem continuedAngularSixthFactor_initial (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    (k : ℕ) (hk : 1 ≤ k) (S : Finset (HeightOneSpectrum O))
    (z : ℂ) (hz : 1 / 6 < z.re) :
    continuedAngularSixthFactor 𝔪 ψ k S z = angularSixthEulerProduct 𝔪 ψ k S z := by
  rw [angularSixthEulerProduct_eq, grossenEulerProductModS_eq_mul_deletedFactors 𝔪 ψ
    (by omega : 1 ≤ 6 * k) S (by
      simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
      linarith)]
  rfl

/-- A nonzero angular weight makes the free sixth-power factor regular across `z=1/6`. -/
theorem continuedAngularSixthFactor_differentiable (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    (k : ℕ) (hk : 1 ≤ k) (S : Finset (HeightOneSpectrum O)) :
    DifferentiableOn ℂ (continuedAngularSixthFactor 𝔪 ψ k S)
      {z : ℂ | -(3 * (k : ℝ)) < z.re} := by
  intro z hz
  change -(3 * (k : ℝ)) < z.re at hz
  have hi : -(3 * ((6 * k : ℕ) : ℝ)) < (6 * z).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    push_cast
    linarith
  have hL := (differentiableOn_grossenLFunction 𝔪 ψ (by omega : 1 ≤ 6 * k)).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hi)
  have hd : DifferentiableAt ℂ (fun w : ℂ => 6 * w) z := differentiableAt_id.const_mul 6
  exact ((hL.comp z hd).mul
    ((differentiable_grossenDeletedFactors 𝔪 ψ (6 * k) S).differentiableAt.comp z hd)).differentiableWithinAt

/-- The replacement factor has a nonzero value where the spherical factor had a pole. -/
theorem continuedAngularSixthFactor_one_sixth_ne_zero (𝔪 : Modulus K)
    (ψ : HeckeCharacter 𝔪) (k : ℕ) (hk : 1 ≤ k) (S : Finset (HeightOneSpectrum O)) :
    continuedAngularSixthFactor 𝔪 ψ k S (1 / 6) ≠ 0 := by
  unfold continuedAngularSixthFactor
  rw [show (6 : ℂ) * (1 / 6) = 1 by norm_num]
  exact mul_ne_zero
    (grossenLFunction_ne_zero_of_one_le_re 𝔪 ψ (by omega : 1 ≤ 6 * k) (by norm_num))
    (grossenDeletedFactors_ne_zero 𝔪 ψ (6 * k) S (by norm_num))

/-- Moving positive angular weight into the free sixth-power channel removes its residue
at `1/6`, despite the replacement factor being nonzero there. -/
theorem continuedAngularSixthFactor_zero_residue (𝔪 : Modulus K)
    (ψ : HeckeCharacter 𝔪) (k : ℕ) (hk : 1 ≤ k) (S : Finset (HeightOneSpectrum O)) :
    Tendsto (fun z : ℂ => (z - 1 / 6) * continuedAngularSixthFactor 𝔪 ψ k S z)
      (𝓝 (1 / 6)) (𝓝 0) := by
  have hi : -(3 * (k : ℝ)) < (1 / 6 : ℂ).re := by
    norm_num
    have hn := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  have hc : DifferentiableAt ℂ (continuedAngularSixthFactor 𝔪 ψ k S) (1 / 6) :=
    (continuedAngularSixthFactor_differentiable 𝔪 ψ k hk S).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hi)
  have h : ContinuousAt (fun z : ℂ =>
      (z - 1 / 6) * continuedAngularSixthFactor 𝔪 ψ k S z) (1 / 6) :=
    (continuousAt_id.sub continuousAt_const).mul hc.continuousAt
  simpa only [sub_self, zero_mul] using h.tendsto

end GaloisForLFunctions.FamilyContinuationTheory
