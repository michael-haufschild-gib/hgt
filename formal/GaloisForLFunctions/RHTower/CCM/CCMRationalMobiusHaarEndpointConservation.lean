import GaloisForLFunctions.RHTower.CCM.CCMRationalUnitInvariantMobiusPoissonCompression
import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicPureTensorHaarDualCancellation
import Mathlib.GroupTheory.Coset.Card

/-!
# Möbius--Haar endpoint conservation

The divisor source produced by profinite-unit radialization preserves both
Tate endpoint functionals exactly.  The physical endpoint is doubled by
positive/negative pairing.  The Fourier endpoint is also doubled: finite
orbit counting contributes `N / d`, while denominator dilation contributes
the reciprocal Jacobian, and the two factors cancel exactly.
-/

noncomputable section

open MeasureTheory IsDedekindDomain
open scoped Classical BigOperators RestrictedProduct algebraMap FourierTransform SchwartzMap

namespace GaloisForLFunctions.RHTower

private abbrev U := CCMRationalProfiniteUnit
private abbrev IntegralFiniteAdeles :=
  ccmRationalIntegralFiniteAdelesAddSubgroup

/-! ## Exact divisor-orbit counting -/

theorem ccmRationalZMod_mem_castHomKer_iff
    {N d : ℕ} [NeZero N] (hdN : d ∣ N) (r : ZMod N) :
    r ∈ (ZMod.castHom hdN (ZMod d)).toAddMonoidHom.ker ↔
      d ∣ r.val := by
  rw [AddMonoidHom.mem_ker]
  change ZMod.castHom hdN (ZMod d) r = 0 ↔ _
  have hr : (r.val : ZMod N) = r := ZMod.natCast_zmod_val r
  calc
    ZMod.castHom hdN (ZMod d) r = 0 ↔
        ZMod.castHom hdN (ZMod d) (r.val : ZMod N) = 0 := by rw [hr]
    _ ↔ (r.val : ZMod d) = 0 := by rw [map_natCast]
    _ ↔ d ∣ r.val := by
      exact_mod_cast
        (ZMod.intCast_zmod_eq_zero_iff_dvd (r.val : ℤ) d)

def ccmRationalZModDivisibleEquivCastHomKer
    {N d : ℕ} [NeZero N] (hdN : d ∣ N) :
    {r : ZMod N // d ∣ r.val} ≃
      (ZMod.castHom hdN (ZMod d)).toAddMonoidHom.ker where
  toFun r := ⟨r.1, (ccmRationalZMod_mem_castHomKer_iff hdN r.1).2 r.2⟩
  invFun r := ⟨r.1, (ccmRationalZMod_mem_castHomKer_iff hdN r.1).1 r.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exactly `N / d` canonical residues modulo `N` are divisible by `d ∣ N`. -/
theorem ccmRationalZMod_card_divisible
    {N d : ℕ} [NeZero N] (hdN : d ∣ N) (hd : d ≠ 0) :
    Nat.card {r : ZMod N // d ∣ r.val} = N / d := by
  let L := (ZMod.castHom hdN (ZMod d)).toAddMonoidHom
  have hquot : Nat.card (ZMod N ⧸ L.ker) = d := by
    rw [Nat.card_congr
      (QuotientAddGroup.quotientKerEquivOfSurjective L
        (ZMod.castHom_surjective hdN)).toEquiv]
    exact Nat.card_zmod d
  have hcard :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup L.ker
  have hNcard : Nat.card (ZMod N) = N := Nat.card_zmod N
  have hker : Nat.card L.ker = N / d := by
    apply Nat.eq_div_of_mul_eq_left hd
    calc
      Nat.card L.ker * d = d * Nat.card L.ker := Nat.mul_comm _ _
      _ = Nat.card (ZMod N ⧸ L.ker) * Nat.card L.ker := by rw [hquot]
      _ = Nat.card (ZMod N) := hcard.symm
      _ = N := hNcard
  rw [Nat.card_congr (ccmRationalZModDivisibleEquivCastHomKer hdN), hker]

theorem ccmRationalZMod_filter_card_divisible
    {N d : ℕ} [NeZero N] (hdN : d ∣ N) (hd : d ≠ 0) :
    (Finset.univ.filter (fun r : ZMod N => d ∣ r.val)).card = N / d := by
  rw [← Fintype.card_subtype]
  simpa only [Nat.card_eq_fintype_card] using
    ccmRationalZMod_card_divisible hdN hd

theorem CCMRationalZModUnitInvariant.eq_sum_divisors_indicator
    {N : ℕ} [NeZero N] {g : ZMod N → ℂ}
    (hg : CCMRationalZModUnitInvariant N g) (r : ZMod N) :
    g r = ∑ d ∈ N.divisors,
      if d ∣ r.val then
        ccmRationalZModMobiusDivisorCoefficient N g d else 0 := by
  have hN : N ≠ 0 := NeZero.ne N
  rw [hg.eq_sum_mobiusDivisorCoefficient hN r]
  have hfin : (r.val.gcd N).divisors =
      N.divisors.filter (fun d => d ∣ r.val) := by
    ext d
    rw [ccmRational_mem_gcd_divisors_iff hN, Finset.mem_filter]
    constructor
    · rintro ⟨hdr, hdN⟩
      exact ⟨Nat.mem_divisors.mpr ⟨hdN, hN⟩, hdr⟩
    · rintro ⟨hdmem, hdr⟩
      exact ⟨hdr, (Nat.mem_divisors.mp hdmem).1⟩
  rw [hfin, Finset.sum_filter]

/-- **Reciprocal divisor conservation.** The total mass of a unit-invariant
residue weight is the modulus times the reciprocal-divisor mass of its
Möbius coefficients. -/
theorem ccmRationalZMod_sum_eq_modulus_mul_mobiusReciprocal
    {N : ℕ} [NeZero N] {g : ZMod N → ℂ}
    (hg : CCMRationalZModUnitInvariant N g) :
    ∑ r : ZMod N, g r =
      (N : ℂ) * (∑ d ∈ N.divisors,
        ccmRationalZModMobiusDivisorCoefficient N g d / (d : ℂ)) := by
  symm
  calc
    (N : ℂ) * (∑ d ∈ N.divisors,
        ccmRationalZModMobiusDivisorCoefficient N g d / (d : ℂ)) =
        ∑ d ∈ N.divisors, (N : ℂ) *
          (ccmRationalZModMobiusDivisorCoefficient N g d / (d : ℂ)) := by
      rw [Finset.mul_sum]
    _ = ∑ d ∈ N.divisors, ∑ r : ZMod N,
          if d ∣ r.val then
            ccmRationalZModMobiusDivisorCoefficient N g d else 0 := by
      apply Finset.sum_congr rfl
      intro d hdmem
      have hdN := (Nat.mem_divisors.mp hdmem).1
      have hd0 := (Nat.pos_of_mem_divisors hdmem).ne'
      rw [← Finset.sum_filter, Finset.sum_const,
        ccmRationalZMod_filter_card_divisible hdN hd0]
      simp only [nsmul_eq_mul]
      have hmul : d * (N / d) = N := Nat.mul_div_cancel' hdN
      have hmulC : (d : ℂ) * (N / d : ℕ) = (N : ℂ) := by
        exact_mod_cast hmul
      field_simp
      rw [← hmulC]
      ring
    _ = ∑ r : ZMod N, ∑ d ∈ N.divisors,
          if d ∣ r.val then
            ccmRationalZModMobiusDivisorCoefficient N g d else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ r : ZMod N, g r := by
      apply Finset.sum_congr rfl
      intro r hr
      exact (hg.eq_sum_divisors_indicator r).symm

/-! ## Haar transport on the integral finite adeles -/

/-- Right multiplication by a profinite unit as an additive homeomorphism
of the actual compact open integral finite adeles. -/
def ccmRationalIntegralFiniteAdeleProfiniteMulRightEquiv
    (u : U) : IntegralFiniteAdeles ≃ₜ+ IntegralFiniteAdeles where
  toFun x := ccmRationalIntegralFiniteAdeleMul x
    (ccmRationalProfiniteUnitIntegralVal u)
  invFun x := ccmRationalIntegralFiniteAdeleMul x
    (ccmRationalProfiniteUnitIntegralVal u⁻¹)
  left_inv x := by
    apply Subtype.ext
    change x.1 * (u.1 : CCMRationalFiniteAdele) *
      ((u.1⁻¹ : CCMRationalFiniteAdeleˣ) : CCMRationalFiniteAdele) = x.1
    rw [mul_assoc]
    change x.1 * ((u.1 * u.1⁻¹ : CCMRationalFiniteAdeleˣ) :
      CCMRationalFiniteAdele) = x.1
    simp
  right_inv x := by
    apply Subtype.ext
    change x.1 *
      ((u.1⁻¹ : CCMRationalFiniteAdeleˣ) : CCMRationalFiniteAdele) *
        (u.1 : CCMRationalFiniteAdele) = x.1
    rw [mul_assoc]
    change x.1 * ((u.1⁻¹ * u.1 : CCMRationalFiniteAdeleˣ) :
      CCMRationalFiniteAdele) = x.1
    simp
  map_add' x y := by
    apply Subtype.ext
    exact add_mul x.1 y.1 (u.1 : CCMRationalFiniteAdele)
  continuous_toFun := by
    rw [continuous_induced_rng]
    change Continuous (fun x : IntegralFiniteAdeles =>
      x.1 * (u.1 : CCMRationalFiniteAdele))
    exact continuous_subtype_val.mul continuous_const
  continuous_invFun := by
    rw [continuous_induced_rng]
    change Continuous (fun x : IntegralFiniteAdeles =>
      x.1 * ((u.1⁻¹ : CCMRationalFiniteAdeleˣ) : CCMRationalFiniteAdele))
    exact continuous_subtype_val.mul continuous_const

theorem ccmRationalIntegralFiniteAdeleProfiniteMulRightHaarCharacter
    (u : U) :
    addEquivAddHaarChar
      (ccmRationalIntegralFiniteAdeleProfiniteMulRightEquiv u) = 1 := by
  have h := addEquivAddHaarChar_smul_preimage
    ccmRationalIntegralFiniteAdelesHaar
    (X := Set.univ)
    (ccmRationalIntegralFiniteAdeleProfiniteMulRightEquiv u)
  simp only [Set.preimage_univ,
    ccmRationalIntegralFiniteAdelesHaar_univ] at h
  apply ENNReal.coe_injective
  simpa [ENNReal.smul_def] using h

theorem ccmRationalIntegralFiniteAdele_integral_mulRight_profinite
    (ψ : IntegralFiniteAdeles → ℂ) (u : U) :
    (∫ x, ψ (ccmRationalIntegralFiniteAdeleProfiniteMulRightEquiv u x)
        ∂ccmRationalIntegralFiniteAdelesHaar) =
      ∫ x, ψ x ∂ccmRationalIntegralFiniteAdelesHaar := by
  have hmap :
      (∫ x, ψ (ccmRationalIntegralFiniteAdeleProfiniteMulRightEquiv u x)
          ∂ccmRationalIntegralFiniteAdelesHaar) =
        ∫ y, ψ y ∂(ccmRationalIntegralFiniteAdelesHaar.map
          (ccmRationalIntegralFiniteAdeleProfiniteMulRightEquiv u)) :=
    (integral_map_equiv
      (ccmRationalIntegralFiniteAdeleProfiniteMulRightEquiv u).toHomeomorph.toMeasurableEquiv
      ψ).symm
  rw [hmap]
  have hmeasure := addEquivAddHaarChar_smul_map
    ccmRationalIntegralFiniteAdelesHaar
    (ccmRationalIntegralFiniteAdeleProfiniteMulRightEquiv u)
  rw [ccmRationalIntegralFiniteAdeleProfiniteMulRightHaarCharacter u] at hmeasure
  have hmeasure' :
      ccmRationalIntegralFiniteAdelesHaar.map
          (ccmRationalIntegralFiniteAdeleProfiniteMulRightEquiv u) =
        ccmRationalIntegralFiniteAdelesHaar := by
    simpa only [one_smul] using hmeasure
  rw [hmeasure']

/-- Cyclic sample mass is unchanged by a profinite-unit multiplier. -/
theorem ccmRationalProfiniteHaarResidueSample_sum
    (N : ℕ) [NeZero N] (ψ : IntegralFiniteAdeles → ℂ)
    (hψ : Continuous ψ)
    (hclass : CCMRationalIntegralFiniteAdeleCongruenceInvariant N ψ)
    (u : U) :
    ∑ r : ZMod N, ccmRationalProfiniteHaarResidueSample N ψ r u =
      N • (∫ x, ψ x ∂ccmRationalIntegralFiniteAdelesHaar) := by
  let E := ccmRationalIntegralFiniteAdeleProfiniteMulRightEquiv u
  let ψu : IntegralFiniteAdeles → ℂ := fun x => ψ (E x)
  have hψu : Continuous ψu := hψ.comp E.continuous
  have hperiod : ∀ x z : IntegralFiniteAdeles,
      ψu (x + N • z) = ψu x := by
    intro x z
    apply hclass
    have hbase : CCMRationalIntegralFiniteAdeleCongruent N (x + N • z) x := by
      exact ⟨z, by abel⟩
    exact hbase.mul_right (ccmRationalProfiniteUnitIntegralVal u)
  have hquot : ∀ {x y : IntegralFiniteAdeles},
      QuotientAddGroup.mk' ((nsmulAddMonoidHom
        (α := IntegralFiniteAdeles) N).range) x =
        QuotientAddGroup.mk' ((nsmulAddMonoidHom
          (α := IntegralFiniteAdeles) N).range) y →
        ψu x = ψu y :=
    ccmRationalIntegralFiniteAdele_classInvariant_of_nsmulInvariant
      N ψu hperiod
  have hsum := ccmRationalIntegralFiniteAdele_cyclicSampleSum_eq_nsmul_integral
    N ψu
      (hψu.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace ψu)) hquot
  change (∑ r : ZMod N, ψu
      (ccmRationalIntegralFiniteAdeleDiagonal (r.val : ℤ))) = _
  rw [hsum]
  congr 1
  exact ccmRationalIntegralFiniteAdele_integral_mulRight_profinite ψ u

/-- Sum of Haar-radial residue weights is the finite cyclic Haar mass. -/
theorem ccmRationalProfiniteHaarResidueAverage_sum
    (N : ℕ) [NeZero N] (ψ : IntegralFiniteAdeles → ℂ)
    (hψ : Continuous ψ)
    (hclass : CCMRationalIntegralFiniteAdeleCongruenceInvariant N ψ) :
    ∑ r : ZMod N, ccmRationalProfiniteHaarResidueAverage N ψ r =
      N • (∫ x, ψ x ∂ccmRationalIntegralFiniteAdelesHaar) := by
  simp_rw [ccmRationalProfiniteHaarResidueAverage]
  calc
    (∑ r : ZMod N, ∫ u : U,
        ccmRationalProfiniteHaarResidueSample N ψ r u
          ∂ccmRationalProfiniteUnitHaar) =
        ∫ u : U, ∑ r : ZMod N,
          ccmRationalProfiniteHaarResidueSample N ψ r u
            ∂ccmRationalProfiniteUnitHaar := by
      rw [integral_finsetSum]
      intro r hr
      exact integrable_ccmRationalProfiniteHaarResidueSample N ψ hψ r
    _ = ∫ _u : U, N •
          (∫ x, ψ x ∂ccmRationalIntegralFiniteAdelesHaar)
            ∂ccmRationalProfiniteUnitHaar := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u =>
        ccmRationalProfiniteHaarResidueSample_sum N ψ hψ hclass u
    _ = N • (∫ x, ψ x ∂ccmRationalIntegralFiniteAdelesHaar) := by
      rw [integral_const, Measure.real,
        ccmRationalProfiniteUnitHaar_univ]
      simp

namespace CCMRationalFiniteBruhatHaarRadialPacket

theorem averageWeight_sum
    {phi : CCMRationalFiniteBruhatSchwartz}
    (P : CCMRationalFiniteBruhatHaarRadialPacket phi)
    [NeZero P.period] :
    ∑ r : ZMod P.period, P.averageWeight r =
      P.period • ((P.denominator : ℝ)⁻¹ •
        ccmRationalFiniteBruhatIntegral phi) := by
  rw [averageWeight,
    ccmRationalProfiniteHaarResidueAverage_sum P.period P.restricted
      P.restricted_continuous P.restricted_congruenceInvariant,
    P.restrictedIntegral_eq]

theorem averageWeight_zero
    {phi : CCMRationalFiniteBruhatSchwartz}
    (P : CCMRationalFiniteBruhatHaarRadialPacket phi) :
    P.averageWeight 0 = phi.1 0 := by
  letI : NeZero P.period := P.period_neZero
  rw [averageWeight, ccmRationalProfiniteHaarResidueAverage]
  have hconst : (fun u : U =>
      ccmRationalProfiniteHaarResidueSample
        P.period P.restricted 0 u) = fun _ => phi.1 0 := by
    funext u
    have h := P.finiteCoefficient 0 u
    simpa using h.symm
  rw [hconst]
  rw [integral_const, Measure.real,
    ccmRationalProfiniteUnitHaar_univ]
  simp

end CCMRationalFiniteBruhatHaarRadialPacket

/-! ## Fourier endpoint of the compressed source -/

theorem ccmRationalSchwartzEvenization_fourier_zero
    (f : CCMRationalArchimedeanSchwartz) :
    (𝓕 (ccmRationalSchwartzEvenization f)) 0 = 2 * (𝓕 f) 0 := by
  change ((FourierTransform.fourierCLE ℂ
    CCMRationalArchimedeanSchwartz)
      (f + RHTower.deningerReflect f)) 0 = _
  rw [map_add]
  change (𝓕 f) 0 + (𝓕 (RHTower.deningerReflect f)) 0 = _
  rw [fourier_ccmRationalArchimedean_zero_eq_integral,
    fourier_ccmRationalArchimedean_zero_eq_integral]
  change (∫ x : ℝ, f x) + (∫ x : ℝ, f (-x)) = 2 * ∫ x : ℝ, f x
  rw [MeasureTheory.integral_neg_eq_self (fun x : ℝ => f x) volume]
  ring

theorem fourier_ccmRationalNaturalDilation_zero
    (f : CCMRationalArchimedeanSchwartz) {d : ℕ} (hd : d ≠ 0) :
    (𝓕 (ccmRationalNaturalDilation f d)) 0 =
      ((d : ℝ)⁻¹ : ℂ) * (𝓕 f) 0 := by
  have hdposR : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
  rw [show ccmRationalNaturalDilation f d =
      ccmRationalArchimedeanDilation f (d : ℝ) hdposR.ne' by
    simp [ccmRationalNaturalDilation, hd]]
  rw [fourier_ccmRationalArchimedeanDilation f hdposR]
  simp

theorem ccmRationalUnitInvariantMobiusSource_fourier_zero
    {N : ℕ} (hN : N ≠ 0) (g : ZMod N → ℂ)
    (f : CCMRationalArchimedeanSchwartz) :
    (𝓕 (ccmRationalUnitInvariantMobiusSource N g f)) 0 =
      2 * (∑ d ∈ N.divisors,
        ccmRationalZModMobiusDivisorCoefficient N g d / (d : ℂ)) *
          (𝓕 f) 0 := by
  change RHTower.deningerFourierEval
      (ccmRationalUnitInvariantMobiusSource N g f) = _
  rw [ccmRationalUnitInvariantMobiusSource,
    map_sum (RHTower.deningerFourierEval)]
  simp only [map_smul, RHTower.deningerFourierEval_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hdmem
  have hd0 := (Nat.pos_of_mem_divisors hdmem).ne'
  change ccmRationalZModMobiusDivisorCoefficient N g d *
      (𝓕 (ccmRationalNaturalDilation
        (ccmRationalSchwartzEvenization f) d)) 0 = _
  rw [fourier_ccmRationalNaturalDilation_zero _ hd0,
    ccmRationalSchwartzEvenization_fourier_zero]
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
  have hcast : ((d : ℝ) : ℂ) = (d : ℂ) := by norm_num
  rw [hcast]
  field_simp [hdC]

/-- **Pure-tensor two-endpoint conservation.** The canonical Haar-radial
Möbius source has both endpoint values exactly twice the corresponding
adelic Tate endpoints. -/
theorem ccmRationalAdelicPureTensorMobiusSource_endpoints
    (f : CCMRationalArchimedeanSchwartz)
    (phi : CCMRationalFiniteBruhatSchwartz)
    (P : CCMRationalFiniteBruhatHaarRadialPacket phi) :
    let F := ccmRationalUnitInvariantMobiusSource
      P.period P.averageWeight
        (ccmRationalPositiveDenominatorDilation
          f P.denominator P.denominator_pos)
    F 0 = 2 * ccmRationalAdelicBruhatZeroEval (f ⊗ₜ[ℂ] phi) ∧
      (𝓕 F) 0 = 2 * ccmRationalAdelicBruhatIntegral (f ⊗ₜ[ℂ] phi) := by
  letI : NeZero P.period := P.period_neZero
  let fD := ccmRationalPositiveDenominatorDilation
    f P.denominator P.denominator_pos
  let F := ccmRationalUnitInvariantMobiusSource
    P.period P.averageWeight fD
  have hphysical : F 0 =
      2 * ccmRationalAdelicBruhatZeroEval (f ⊗ₜ[ℂ] phi) := by
    rw [ccmRationalUnitInvariantMobiusSource_zero
      P.period_neZero.out P.averageWeight fD,
      P.averageWeight_zero]
    simp [fD, ccmRationalPositiveDenominatorDilation_apply,
      ccmRationalAdelicBruhatZeroEval_tmul]
    ring
  refine ⟨hphysical, ?_⟩
  rw [ccmRationalUnitInvariantMobiusSource_fourier_zero
    P.period_neZero.out P.averageWeight fD]
  have hmass := P.averageWeight_sum
  have hrecip := ccmRationalZMod_sum_eq_modulus_mul_mobiusReciprocal
    P.averageWeight_unitInvariant
  have hperiodC : (P.period : ℂ) ≠ 0 := by
    exact_mod_cast P.period_neZero.out
  have hcoeff :
      (∑ d ∈ P.period.divisors,
        ccmRationalZModMobiusDivisorCoefficient
          P.period P.averageWeight d / (d : ℂ)) =
        ((P.denominator : ℝ)⁻¹ : ℂ) *
          ccmRationalFiniteBruhatIntegral phi := by
    rw [hmass] at hrecip
    simp only [nsmul_eq_mul, Complex.real_smul] at hrecip
    apply mul_left_cancel₀ hperiodC
    simpa [mul_assoc] using hrecip.symm
  rw [hcoeff,
    fourier_ccmRationalPositiveDenominatorDilation_zero_eq
      f P.denominator P.denominator_pos]
  rw [ccmRationalAdelicBruhatIntegral_tmul]
  simp only [Complex.real_smul]
  have hD : (P.denominator : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt P.denominator_pos)
  field_simp [hD]
  ac_rfl

end GaloisForLFunctions.RHTower
