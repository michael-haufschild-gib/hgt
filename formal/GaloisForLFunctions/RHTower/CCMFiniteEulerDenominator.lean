import GaloisForLFunctions.RHTower.CCMFiniteScatteringSoninNormalForm

/-!
# The actual finite Euler denominator of spherical scattering

The denominator is a product of the existing physical local Euler factors.
Its Mellin multiplier is the literal finite Euler polynomial, and the finite
scattering unitary sends it exactly to its adjoint. This keeps all mixed terms.
-/

noncomputable section

open IsDedekindDomain MeasureTheory
open scoped BigOperators

namespace RHTower

private def placePrime (v : HeightOneSpectrum ℤ) : ℕ :=
  Rat.HeightOneSpectrum.primesEquiv v

private theorem placePrime_one_lt (v : HeightOneSpectrum ℤ) : 1 < placePrime v :=
  (Rat.HeightOneSpectrum.primesEquiv v).property.one_lt

private theorem mellinCharacter_inverse_ae (p : ℝ) (f : SoninL2) :
    (MellinL2.mellinCharacterMulUnitary p).symm f =ᵐ[volume]
      fun t => (MellinL2.mellinCharacter p t)⁻¹ * f t := by
  filter_upwards [MellinL2.mellinCharacterMulUnitary_ae p
    ((MellinL2.mellinCharacterMulUnitary p).symm f)] with t ht
  have ht' : f t = MellinL2.mellinCharacter p t *
      ((MellinL2.mellinCharacterMulUnitary p).symm f) t := by
    simpa only [LinearIsometryEquiv.apply_symm_apply] using ht
  have hne : MellinL2.mellinCharacter p t ≠ 0 := by
    intro h
    have hn := MellinL2.norm_mellinCharacter p t
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  rw [ht', ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

private theorem mellin_evenDilation_inverse
    (p : ℝ) (hp : 0 < p) (f : evenSubspace) :
    archimedeanMellinUnitary ((evenDilationUnitary p hp).symm f) =
      (MellinL2.mellinCharacterMulUnitary p).symm (archimedeanMellinUnitary f) := by
  apply (MellinL2.mellinCharacterMulUnitary p).injective
  rw [LinearIsometryEquiv.apply_symm_apply,
    ← archimedeanMellinUnitary_evenDilation p hp,
    LinearIsometryEquiv.apply_symm_apply]

/-- Mellin source formula for the existing physical local Euler polynomial. -/
theorem mellin_evenPrimeLocalFactor_ae
    (p : ℝ) (hp : 1 < p) (f : evenSubspace) :
    archimedeanMellinUnitary (evenPrimeLocalFactor p hp f) =ᵐ[volume]
      fun t => semilocalPrimeSymbol p t * archimedeanMellinUnitary f t := by
  have hM : archimedeanMellinUnitary (evenPrimeLocalFactor p hp f) =
      archimedeanMellinUnitary f - (Real.sqrt p : ℂ)⁻¹ •
        (MellinL2.mellinCharacterMulUnitary p).symm (archimedeanMellinUnitary f) := by
    change archimedeanMellinUnitary
      (f - (Real.sqrt p : ℂ)⁻¹ • (evenDilationUnitary p (zero_lt_one.trans hp)).symm f) = _
    rw [map_sub, map_smul, mellin_evenDilation_inverse]
  rw [hM]
  filter_upwards [Lp.coeFn_sub (archimedeanMellinUnitary f)
      ((Real.sqrt p : ℂ)⁻¹ • (MellinL2.mellinCharacterMulUnitary p).symm
        (archimedeanMellinUnitary f)),
    Lp.coeFn_smul (Real.sqrt p : ℂ)⁻¹
      ((MellinL2.mellinCharacterMulUnitary p).symm (archimedeanMellinUnitary f)),
    mellinCharacter_inverse_ae p (archimedeanMellinUnitary f)] with t hsub hsmul hinv
  simp only [Pi.sub_apply, Pi.smul_apply] at hsub hsmul
  rw [hsub, hsmul, hinv]
  change _ - (Real.sqrt p : ℂ)⁻¹ *
    ((MellinL2.mellinCharacter p t)⁻¹ * _) = _
  unfold semilocalPrimeSymbol
  ring

private theorem star_semilocalPrimeSymbol (p t : ℝ) :
    (starRingEnd ℂ) (semilocalPrimeSymbol p t) =
      1 - (Real.sqrt p : ℂ)⁻¹ * MellinL2.mellinCharacter p t := by
  simp [semilocalPrimeSymbol, MellinL2.star_mellinCharacter]

/-- The adjoint denominator contains only the forward physical dilation. -/
theorem adjoint_evenPrimeLocalFactor_eq_forward (p : ℝ) (hp : 1 < p) :
    ContinuousLinearMap.adjoint (evenPrimeLocalFactor p hp) =
      1 - (Real.sqrt p : ℂ)⁻¹ •
        ((evenDilationUnitary p (zero_lt_one.trans hp)) : evenSubspace →L[ℂ] evenSubspace) := by
  have hcoeff : (Real.sqrt p : ℂ)⁻¹ = (((Real.sqrt p)⁻¹ : ℝ) : ℂ) := by norm_cast
  rw [evenPrimeLocalFactor, hcoeff]
  exact adjoint_one_sub_real_smul_unitary_symm
    (evenDilationUnitary p (zero_lt_one.trans hp)) (Real.sqrt p)⁻¹

/-- The adjoint physical local factor carries the conjugate literal Euler polynomial. -/
theorem mellin_adjoint_evenPrimeLocalFactor_ae
    (p : ℝ) (hp : 1 < p) (f : evenSubspace) :
    archimedeanMellinUnitary (ContinuousLinearMap.adjoint (evenPrimeLocalFactor p hp) f)
      =ᵐ[volume] fun t =>
        (starRingEnd ℂ) (semilocalPrimeSymbol p t) * archimedeanMellinUnitary f t := by
  have hM : archimedeanMellinUnitary
      (ContinuousLinearMap.adjoint (evenPrimeLocalFactor p hp) f) =
      archimedeanMellinUnitary f - (Real.sqrt p : ℂ)⁻¹ •
        MellinL2.mellinCharacterMulUnitary p (archimedeanMellinUnitary f) := by
    rw [adjoint_evenPrimeLocalFactor_eq_forward]
    change archimedeanMellinUnitary
      (f - (Real.sqrt p : ℂ)⁻¹ • evenDilationUnitary p (zero_lt_one.trans hp) f) = _
    rw [map_sub, map_smul, archimedeanMellinUnitary_evenDilation]
  rw [hM]
  filter_upwards [Lp.coeFn_sub (archimedeanMellinUnitary f)
      ((Real.sqrt p : ℂ)⁻¹ • MellinL2.mellinCharacterMulUnitary p
        (archimedeanMellinUnitary f)),
    Lp.coeFn_smul (Real.sqrt p : ℂ)⁻¹
      (MellinL2.mellinCharacterMulUnitary p (archimedeanMellinUnitary f)),
    MellinL2.mellinCharacterMulUnitary_ae p (archimedeanMellinUnitary f)]
    with t hsub hsmul hchar
  simp only [Pi.sub_apply, Pi.smul_apply] at hsub hsmul
  rw [hsub, hsmul, hchar, star_semilocalPrimeSymbol]
  change _ - (Real.sqrt p : ℂ)⁻¹ * (MellinL2.mellinCharacter p t * _) = _
  ring

/-- The physical local polynomial at a finite rational place. -/
def ccmPlaceEulerDenominator (v : HeightOneSpectrum ℤ) :
    evenSubspace →L[ℂ] evenSubspace :=
  evenPrimeLocalFactor (placePrime v : ℝ) (by exact_mod_cast placePrime_one_lt v)

/-- Full finite Euler polynomial, as a product of actual physical source factors. -/
def ccmFiniteEulerDenominator (S : Finset (HeightOneSpectrum ℤ)) :
    evenSubspace →L[ℂ] evenSubspace :=
  (S.toList.map ccmPlaceEulerDenominator).prod

/-- Literal Mellin symbol of the finite physical polynomial. -/
def ccmFiniteEulerDenominatorSymbol (S : Finset (HeightOneSpectrum ℤ)) (t : ℝ) : ℂ :=
  ∏ v ∈ S, semilocalPrimeSymbol (placePrime v : ℝ) t

private theorem mellin_listEulerDenominator_ae (l : List (HeightOneSpectrum ℤ))
    (f : evenSubspace) :
    archimedeanMellinUnitary ((l.map ccmPlaceEulerDenominator).prod f) =ᵐ[volume] fun t =>
      (l.map (fun v => semilocalPrimeSymbol (placePrime v : ℝ) t)).prod *
        archimedeanMellinUnitary f t := by
  induction l generalizing f with
  | nil => simp
  | cons v l ih =>
    simp only [List.map_cons, List.prod_cons]
    change archimedeanMellinUnitary
      (ccmPlaceEulerDenominator v ((l.map ccmPlaceEulerDenominator).prod f)) =ᵐ[volume] _
    filter_upwards [mellin_evenPrimeLocalFactor_ae
      (placePrime v : ℝ) (by exact_mod_cast placePrime_one_lt v)
      ((l.map ccmPlaceEulerDenominator).prod f),
      ih f] with t hhead htail
    change archimedeanMellinUnitary
      (ccmPlaceEulerDenominator v ((l.map ccmPlaceEulerDenominator).prod f)) t = _ at hhead
    rw [hhead, htail]
    ring

/-- Every mixed Euler term is retained in the exact Mellin realization. -/
theorem mellin_ccmFiniteEulerDenominator_ae
    (S : Finset (HeightOneSpectrum ℤ)) (f : evenSubspace) :
    archimedeanMellinUnitary (ccmFiniteEulerDenominator S f) =ᵐ[volume] fun t =>
      ccmFiniteEulerDenominatorSymbol S t * archimedeanMellinUnitary f t := by
  simpa only [ccmFiniteEulerDenominator, ccmFiniteEulerDenominatorSymbol,
    Finset.prod_map_toList] using mellin_listEulerDenominator_ae S.toList f

private theorem mellin_adjoint_listEulerDenominator_ae (l : List (HeightOneSpectrum ℤ))
    (f : evenSubspace) :
    archimedeanMellinUnitary (ContinuousLinearMap.adjoint
      (l.map ccmPlaceEulerDenominator).prod f) =ᵐ[volume] fun t =>
      (starRingEnd ℂ)
        (l.map (fun v => semilocalPrimeSymbol (placePrime v : ℝ) t)).prod *
          archimedeanMellinUnitary f t := by
  induction l generalizing f with
  | nil => simp
  | cons v l ih =>
    simp only [List.map_cons, List.prod_cons]
    change archimedeanMellinUnitary (ContinuousLinearMap.adjoint
      (ccmPlaceEulerDenominator v ∘L (l.map ccmPlaceEulerDenominator).prod) f) =ᵐ[volume] _
    rw [ContinuousLinearMap.adjoint_comp]
    simp only [ContinuousLinearMap.comp_apply]
    filter_upwards [ih (ContinuousLinearMap.adjoint (ccmPlaceEulerDenominator v) f),
      mellin_adjoint_evenPrimeLocalFactor_ae
        (placePrime v : ℝ) (by exact_mod_cast placePrime_one_lt v) f]
      with t htail hhead
    change archimedeanMellinUnitary
      (ContinuousLinearMap.adjoint (ccmPlaceEulerDenominator v) f) t = _ at hhead
    rw [htail, hhead, map_mul]
    ring

/-- Exact adjoint Mellin formula for the full finite physical Euler denominator. -/
theorem mellin_adjoint_ccmFiniteEulerDenominator_ae
    (S : Finset (HeightOneSpectrum ℤ)) (f : evenSubspace) :
    archimedeanMellinUnitary (ContinuousLinearMap.adjoint (ccmFiniteEulerDenominator S) f)
      =ᵐ[volume] fun t =>
        (starRingEnd ℂ) (ccmFiniteEulerDenominatorSymbol S t) * archimedeanMellinUnitary f t := by
  simpa only [ccmFiniteEulerDenominator, ccmFiniteEulerDenominatorSymbol,
    Finset.prod_map_toList] using mellin_adjoint_listEulerDenominator_ae S.toList f

private theorem primeRatio_mul_localSymbol (p : ℕ) (hp : 1 < p) (t : ℝ) :
    GaloisForLFunctions.RHTower.primeRatio p t * semilocalPrimeSymbol (p : ℝ) t =
      (starRingEnd ℂ) (semilocalPrimeSymbol (p : ℝ) t) := by
  have hcast : (((1 / Real.sqrt (p : ℝ)) : ℝ) : ℂ) =
      (Real.sqrt (p : ℝ) : ℂ)⁻¹ := by push_cast; rw [one_div]
  rw [GaloisForLFunctions.RHTower.primeRatio,
    GaloisForLFunctions.RHTower.primeRadius, if_pos hp,
    GaloisForLFunctions.RHTower.primeLocalRatio, hcast, Complex.exp_neg]
  change (1 - (Real.sqrt (p : ℝ) : ℂ)⁻¹ * MellinL2.mellinCharacter (p : ℝ) t) /
      semilocalPrimeSymbol (p : ℝ) t * semilocalPrimeSymbol (p : ℝ) t = _
  rw [div_mul_cancel₀ _ (semilocalPrimeSymbol_ne_zero (p : ℝ) (by exact_mod_cast hp) t)]
  exact (star_semilocalPrimeSymbol (p : ℝ) t).symm

/-- Every Euler denominator cancels against the literal finite phase with the correct orientation. -/
theorem ccmFiniteEulerRatio_mul_denominatorSymbol
    (S : Finset (HeightOneSpectrum ℤ)) (t : ℝ) :
    (∏ v : ↥S, GaloisForLFunctions.RHTower.primeRatio
      (Rat.HeightOneSpectrum.primesEquiv v.1) t) * ccmFiniteEulerDenominatorSymbol S t =
        (starRingEnd ℂ) (ccmFiniteEulerDenominatorSymbol S t) := by
  change (∏ v : ↥S, GaloisForLFunctions.RHTower.primeRatio (placePrime v.1) t) *
    ccmFiniteEulerDenominatorSymbol S t = _
  rw [Finset.prod_coe_sort S
    (fun v => GaloisForLFunctions.RHTower.primeRatio (placePrime v) t), ccmFiniteEulerDenominatorSymbol,
    ← Finset.prod_mul_distrib, map_prod]
  apply Finset.prod_congr rfl
  intro v _
  exact primeRatio_mul_localSymbol (placePrime v) (placePrime_one_lt v) t

/-- Exact operator-level Euler denominator clearing for the complete finite spherical source. -/
theorem ccmFiniteEulerPhysicalUnitary_mul_denominator
    (S : Finset (HeightOneSpectrum ℤ)) :
    (ccmFiniteEulerPhysicalUnitary S).toLinearIsometry.toContinuousLinearMap *
      ccmFiniteEulerDenominator S = ContinuousLinearMap.adjoint (ccmFiniteEulerDenominator S) := by
  apply ContinuousLinearMap.ext
  intro f
  apply archimedeanMellinUnitary.injective
  change archimedeanMellinUnitary (ccmFiniteEulerPhysicalUnitary S (ccmFiniteEulerDenominator S f)) = _
  rw [archimedeanMellinUnitary_ccmFiniteEulerPhysicalUnitary]
  apply Lp.ext
  filter_upwards [ccmFiniteEulerSpectralUnitary_ae S
      (archimedeanMellinUnitary (ccmFiniteEulerDenominator S f)),
    mellin_ccmFiniteEulerDenominator_ae S f,
    mellin_adjoint_ccmFiniteEulerDenominator_ae S f] with t hphase hpoly hadj
  rw [hphase, hpoly, hadj, ← mul_assoc, ccmFiniteEulerRatio_mul_denominatorSymbol]

private theorem forwardDilation_preserves_unitFourierKernel
    (p : ℝ) (hp : 1 < p) (f : evenSubspace) (hf : evenFourierCutoff 1 f = 0) :
    evenFourierCutoff 1 (evenDilationUnitary p (zero_lt_one.trans hp) f) = 0 := by
  have hsmall : evenFourierCutoff (p⁻¹ * 1) f = 0 := by
    have h := DFunLike.congr_fun
      (evenFourierCutoff_mul_of_le (p⁻¹ * 1) 1
        (by simpa using (inv_lt_one_of_one_lt₀ hp).le)) f
    change evenFourierCutoff (p⁻¹ * 1) (evenFourierCutoff 1 f) =
      evenFourierCutoff (p⁻¹ * 1) f at h
    rw [hf, map_zero] at h
    exact h.symm
  have h := DFunLike.congr_fun
    (evenFourierCutoff_mul_evenDilationCLM 1 p (zero_lt_one.trans hp)) f
  change evenFourierCutoff 1 (evenDilationUnitary p (zero_lt_one.trans hp) f) =
    evenDilationUnitary p (zero_lt_one.trans hp) (evenFourierCutoff (p⁻¹ * 1) f) at h
  rw [h, hsmall, map_zero]

private theorem adjoint_localFactor_preserves_unitFourierKernel
    (p : ℝ) (hp : 1 < p) (f : evenSubspace) (hf : evenFourierCutoff 1 f = 0) :
    evenFourierCutoff 1 (ContinuousLinearMap.adjoint (evenPrimeLocalFactor p hp) f) = 0 := by
  rw [adjoint_evenPrimeLocalFactor_eq_forward]
  change evenFourierCutoff 1
    (f - (Real.sqrt p : ℂ)⁻¹ • evenDilationUnitary p (zero_lt_one.trans hp) f) = 0
  rw [map_sub, map_smul, hf, forwardDilation_preserves_unitFourierKernel p hp f hf,
    smul_zero, sub_self]

private theorem adjoint_listEuler_preserves_unitFourierKernel
    (l : List (HeightOneSpectrum ℤ)) (f : evenSubspace) (hf : evenFourierCutoff 1 f = 0) :
    evenFourierCutoff 1
      (ContinuousLinearMap.adjoint (l.map ccmPlaceEulerDenominator).prod f) = 0 := by
  induction l generalizing f with
  | nil => simpa using hf
  | cons v l ih =>
    simp only [List.map_cons, List.prod_cons, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]
    apply ih
    exact adjoint_localFactor_preserves_unitFourierKernel
      (placePrime v : ℝ) (by exact_mod_cast placePrime_one_lt v) f hf

/-- The actual adjoint finite Euler polynomial has no inward Fourier leakage from Sonin. -/
theorem evenFourierCutoff_mul_adjoint_ccmFiniteEulerDenominator_mul_soninProjection
    (S : Finset (HeightOneSpectrum ℤ)) {b : ℝ} (hb : 1 ≤ b) :
    evenFourierCutoff 1 * ContinuousLinearMap.adjoint (ccmFiniteEulerDenominator S) *
      evenCentralSoninProjection b = 0 := by
  have hRQ : evenFourierCutoff 1 * evenCentralSoninProjection b = 0 := by
    rw [← (evenCentralSoninProjection_mul_of_le hb).2, ← mul_assoc,
      evenFourierCutoff_mul_evenCentralSoninProjection, zero_mul]
  apply ContinuousLinearMap.ext
  intro f
  exact adjoint_listEuler_preserves_unitFourierKernel S.toList
    (evenCentralSoninProjection b f) (DFunLike.congr_fun hRQ f)

end RHTower
