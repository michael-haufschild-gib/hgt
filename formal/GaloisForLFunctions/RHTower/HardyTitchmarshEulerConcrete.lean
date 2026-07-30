import GaloisForLFunctions.RHTower.EvenL2LogUnitary
import GaloisForLFunctions.RHTower.HardyTitchmarshBetaInfinity
import GaloisForLFunctions.RHTower.HardyTitchmarshSourceTransport

/-!
# Concrete archimedean dual Hardy--Titchmarsh Euler corner

This file constructs the source unitary itself. The exact logarithmic Jacobian, multiplicative
Mellin transform, Fourier normalization, and archimedean Gamma weight combine to give

`upsilon_infinity = beta_infinity ∘ U_infinity`.

The source local factor is literal multiplication by `1 - p⁻¹ᐟ²⁻ⁱˢ`; its Gram is literal
multiplication by `|1 - p⁻¹ᐟ²⁻ⁱˢ|²`. The lower corner across the archimedean-norm boundary carrier
pulls back to the exact even Sonin Euler corner and is therefore noncompact.
-/

noncomputable section

open MeasureTheory
open scoped InnerProduct InnerProductSpace

namespace RHTower

/-- The normalized `w_infinity` identification of even physical `L²` with multiplicative Haar
`L²`, obtained by undoing the exponential pullback after the exact logarithmic Jacobian unitary. -/
def evenToMultiplicativeHaarUnitary :
    evenSubspace ≃ₗᵢ[ℂ] Lp ℂ 2 MellinL2.multiplicativeHaar :=
  logEvenUnitary.trans MellinL2.expPullbackUnitary.symm

theorem evenToMultiplicativeHaarUnitary_evenDilation
    (p : ℝ) (hp : 0 < p) (f : evenSubspace) :
    evenToMultiplicativeHaarUnitary (evenDilationUnitary p hp f) =
      MellinL2.positiveScaleUnitary (Real.log p)
        (evenToMultiplicativeHaarUnitary f) := by
  apply MellinL2.expPullbackUnitary.injective
  simp only [evenToMultiplicativeHaarUnitary, LinearIsometryEquiv.trans_apply]
  rw [MellinL2.expPullbackUnitary.apply_symm_apply]
  rw [MellinL2.expPullback_positiveScale]
  rw [MellinL2.expPullbackUnitary.apply_symm_apply]
  exact logEvenUnitary_evenDilation p hp f

/-- The concrete normalized archimedean Mellin unitary with spectral coordinate `s`. -/
def archimedeanMellinUnitary : evenSubspace ≃ₗᵢ[ℂ] SpectralL2 :=
  evenToMultiplicativeHaarUnitary.trans MellinL2.mellinUnitary

theorem archimedeanMellinUnitary_evenDilation
    (p : ℝ) (hp : 0 < p) (f : evenSubspace) :
    archimedeanMellinUnitary (evenDilationUnitary p hp f) =
      MellinL2.mellinCharacterMulUnitary p (archimedeanMellinUnitary f) := by
  change MellinL2.mellinUnitary
      (evenToMultiplicativeHaarUnitary (evenDilationUnitary p hp f)) = _
  rw [evenToMultiplicativeHaarUnitary_evenDilation p hp]
  exact MellinL2.mellin_positiveDilation p (evenToMultiplicativeHaarUnitary f)

/-- The concrete archimedean dual Hardy--Titchmarsh unitary
`upsilon_infinity = beta_infinity U_infinity`. -/
def archimedeanDualHardyTitchmarshUnitary :
    evenSubspace ≃ₗᵢ[ℂ] ArchimedeanWeightedL2 :=
  archimedeanMellinUnitary.trans betaInfinityUnitary

/-- The weighted Hardy--Titchmarsh line is nontrivial because it is unitarily equivalent to
the concretely nontrivial even Sonin carrier. -/
theorem archimedeanWeightedL2_nontrivial : Nontrivial ArchimedeanWeightedL2 := by
  letI : Nontrivial evenSubspace := evenSubspace_nontrivial
  exact Equiv.nontrivial archimedeanDualHardyTitchmarshUnitary.symm.toEquiv

/-- The weighted Hardy--Titchmarsh line is infinite-dimensional by unitary transport of the
infinite orthonormal Sonin shell family. -/
theorem archimedeanWeightedL2_not_finiteDimensional :
    ¬ FiniteDimensional ℂ ArchimedeanWeightedL2 := by
  intro hfd
  letI : FiniteDimensional ℂ ArchimedeanWeightedL2 := hfd
  letI : FiniteDimensional ℂ evenSubspace :=
    FiniteDimensional.of_injective
      archimedeanDualHardyTitchmarshUnitary.toLinearEquiv.toLinearMap
      archimedeanDualHardyTitchmarshUnitary.injective
  exact evenSubspace_not_finiteDimensional inferInstance

theorem archimedeanDualHardyTitchmarshUnitary_evenDilation
    (p : ℝ) (hp : 0 < p) (f : evenSubspace) :
    archimedeanDualHardyTitchmarshUnitary (evenDilationUnitary p hp f) =
      weightedMellinCharacterMulUnitary p
        (archimedeanDualHardyTitchmarshUnitary f) := by
  change betaInfinityUnitary
      (archimedeanMellinUnitary (evenDilationUnitary p hp f)) = _
  rw [archimedeanMellinUnitary_evenDilation p hp]
  exact (betaInfinity_intertwines_mellinCharacter p
    (archimedeanMellinUnitary f)).symm

theorem unitaryPush_archimedean_evenDilation
    (p : ℝ) (hp : 0 < p) :
    unitaryPush archimedeanDualHardyTitchmarshUnitary
      (evenDilationUnitary p hp : evenSubspace →L[ℂ] evenSubspace) =
        (weightedMellinCharacterMulUnitary p :
          ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2) := by
  apply ContinuousLinearMap.ext
  intro g
  simpa [unitaryPush] using
    archimedeanDualHardyTitchmarshUnitary_evenDilation p hp
      (archimedeanDualHardyTitchmarshUnitary.symm g)

theorem unitaryPush_archimedean_evenDilation_symm
    (p : ℝ) (hp : 0 < p) :
    unitaryPush archimedeanDualHardyTitchmarshUnitary
      ((evenDilationUnitary p hp).symm : evenSubspace →L[ℂ] evenSubspace) =
        ((weightedMellinCharacterMulUnitary p).symm :
          ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2) := by
  rw [← LinearIsometryEquiv.adjoint_eq_symm]
  rw [← LinearIsometryEquiv.adjoint_eq_symm]
  rw [← adjoint_unitaryPush]
  rw [unitaryPush_archimedean_evenDilation]

/-- Literal multiplication by the local factor `1-p^(-1/2-is)` on the weighted HT line. -/
def archimedeanPrimeLocalFactor (p : ℝ) :
    ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2 :=
  1 - ((Real.sqrt p : ℂ)⁻¹) •
    ((weightedMellinCharacterMulUnitary p).symm :
      ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2)

/-- Pointwise source formula for the local factor `1-p^(-1/2-is)`. -/
theorem archimedeanPrimeLocalFactor_ae (p : ℝ) (g : ArchimedeanWeightedL2) :
    archimedeanPrimeLocalFactor p g =ᵐ[archimedeanWeightedMeasure]
      fun s => (1 - ((Real.sqrt p : ℂ)⁻¹) *
        (MellinL2.mellinCharacter p s)⁻¹) * g s := by
  change (g - ((Real.sqrt p : ℂ)⁻¹) •
      (weightedMellinCharacterMulUnitary p).symm g : ArchimedeanWeightedL2) =ᵐ[_] _
  filter_upwards [Lp.coeFn_sub g
      (((Real.sqrt p : ℂ)⁻¹) • (weightedMellinCharacterMulUnitary p).symm g),
    Lp.coeFn_smul ((Real.sqrt p : ℂ)⁻¹)
      ((weightedMellinCharacterMulUnitary p).symm g),
    weightedMellinCharacterMulUnitary_symm_ae p g] with s hsub hsmul hphase
  calc
    (g - ((Real.sqrt p : ℂ)⁻¹) •
          (weightedMellinCharacterMulUnitary p).symm g :
        ArchimedeanWeightedL2) s =
        g s - (((Real.sqrt p : ℂ)⁻¹) •
          (weightedMellinCharacterMulUnitary p).symm g :
            ArchimedeanWeightedL2) s := hsub
    _ = g s - ((Real.sqrt p : ℂ)⁻¹) *
          ((weightedMellinCharacterMulUnitary p).symm g) s := by
      rw [hsmul]
      rfl
    _ = g s - ((Real.sqrt p : ℂ)⁻¹) *
          ((MellinL2.mellinCharacter p s)⁻¹ * g s) := by rw [hphase]
    _ = (1 - ((Real.sqrt p : ℂ)⁻¹) *
          (MellinL2.mellinCharacter p s)⁻¹) * g s := by ring

theorem hardyTitchmarshLocalFactor_archimedean_eq
    (p : ℝ) (hp : 1 < p) :
    hardyTitchmarshLocalFactor archimedeanDualHardyTitchmarshUnitary p hp =
      archimedeanPrimeLocalFactor p := by
  rw [hardyTitchmarshLocalFactor, evenPrimeLocalFactor,
    unitaryPush_sub, unitaryPush_one, unitaryPush_smul,
    unitaryPush_archimedean_evenDilation_symm]
  rfl

/-- Literal multiplication by `|1-p^(-1/2-is)|²` on the weighted archimedean HT line. -/
def archimedeanPrimeEulerGram (p : ℝ) :
    ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2 :=
  (archimedeanPrimeLocalFactor p)† * archimedeanPrimeLocalFactor p

theorem hardyTitchmarshEulerGram_archimedean_eq
    (p : ℝ) (hp : 1 < p) :
    hardyTitchmarshEulerGram archimedeanDualHardyTitchmarshUnitary p hp =
      archimedeanPrimeEulerGram p := by
  rw [hardyTitchmarshEulerGram, archimedeanPrimeEulerGram,
    hardyTitchmarshLocalFactor_archimedean_eq]

/-- The positive Euler weight in the concrete weighted spectral coordinate. -/
def archimedeanPrimeEulerWeight (p s : ℝ) : ℂ :=
  ((1 + p⁻¹ : ℝ) : ℂ) + (-((Real.sqrt p : ℂ)⁻¹)) *
    (MellinL2.mellinCharacter p s + (MellinL2.mellinCharacter p s)⁻¹)

theorem archimedeanPrimeEulerWeight_eq_normSq
    (p : ℝ) (hp : 1 < p) (s : ℝ) :
    archimedeanPrimeEulerWeight p s =
      ((Complex.normSq
        (1 - ((Real.sqrt p : ℂ)⁻¹) *
          (MellinL2.mellinCharacter p s)⁻¹) : ℝ) : ℂ) := by
  let m := MellinL2.mellinCharacter p s
  have hm0 : m ≠ 0 := by
    simp [m, MellinL2.mellinCharacter]
  have hmstar : starRingEnd ℂ m = m⁻¹ := MellinL2.star_mellinCharacter p s
  have hmInvStar : starRingEnd ℂ m⁻¹ = m := by
    rw [map_inv₀, hmstar, inv_inv]
  have hr :
      (Real.sqrt p : ℂ)⁻¹ = (((Real.sqrt p)⁻¹ : ℝ) : ℂ) := by
    norm_cast
  have hrstar :
      starRingEnd ℂ ((Real.sqrt p : ℂ)⁻¹) =
        (Real.sqrt p : ℂ)⁻¹ := by
    rw [map_inv₀]
    simp
  have hpinv : (p : ℂ)⁻¹ = ((p⁻¹ : ℝ) : ℂ) := by
    norm_cast
  have hrsq :
      ((((Real.sqrt p)⁻¹ : ℝ) : ℂ)) * ((((Real.sqrt p)⁻¹ : ℝ) : ℂ)) =
        ((p⁻¹ : ℝ) : ℂ) := by
    norm_cast
    rw [← mul_inv]
    rw [Real.mul_self_sqrt (le_of_lt (zero_lt_one.trans hp))]
  rw [show MellinL2.mellinCharacter p s = m by rfl]
  unfold archimedeanPrimeEulerWeight
  rw [← Complex.mul_conj]
  rw [map_sub, map_one, map_mul, hmInvStar, hrstar, hr]
  change ((1 + p⁻¹ : ℝ) : ℂ) +
      (-((((Real.sqrt p)⁻¹ : ℝ) : ℂ))) * (m + m⁻¹) =
    (1 - ((((Real.sqrt p)⁻¹ : ℝ) : ℂ)) * m⁻¹) *
      (1 - ((((Real.sqrt p)⁻¹ : ℝ) : ℂ)) * m)
  let r : ℂ := (((Real.sqrt p)⁻¹ : ℝ) : ℂ)
  change ((1 + p⁻¹ : ℝ) : ℂ) + (-r) * (m + m⁻¹) =
    (1 - r * m⁻¹) * (1 - r * m)
  calc
    ((1 + p⁻¹ : ℝ) : ℂ) + (-r) * (m + m⁻¹) =
        1 + r * r - r * (m + m⁻¹) := by
      dsimp [r]
      push_cast
      rw [hpinv, ← hrsq, hr]
      ring
    _ = 1 - r * m - r * m⁻¹ + r * r * (m⁻¹ * m) := by
      rw [inv_mul_cancel₀ hm0]
      ring
    _ = (1 - r * m⁻¹) * (1 - r * m) := by ring

theorem archimedeanPrimeEulerWeight_eq_norm_sq
    (p : ℝ) (hp : 1 < p) (s : ℝ) :
    archimedeanPrimeEulerWeight p s =
      ((‖1 - ((Real.sqrt p : ℂ)⁻¹) *
        (MellinL2.mellinCharacter p s)⁻¹‖ ^ 2 : ℝ) : ℂ) := by
  rw [← Complex.normSq_eq_norm_sq]
  exact archimedeanPrimeEulerWeight_eq_normSq p hp s

theorem archimedeanPrimeEulerGram_eq_affine
    (p : ℝ) (hp : 1 < p) :
    archimedeanPrimeEulerGram p =
      ((1 + p⁻¹ : ℝ) : ℂ) •
        (1 : ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2) +
      (-((Real.sqrt p : ℂ)⁻¹)) •
        ((weightedMellinCharacterMulUnitary p :
            ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2) +
          ((weightedMellinCharacterMulUnitary p).symm :
            ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2)) := by
  rw [← hardyTitchmarshEulerGram_archimedean_eq p hp,
    hardyTitchmarshLocalFactor_adjoint_comp_self,
    evenPositiveEulerOperator,
    ← evenDilationUnitarySum_eq_evenDilationSum p hp,
    evenDilationUnitarySum,
    unitaryPush_add, unitaryPush_smul, unitaryPush_one, unitaryPush_smul,
    unitaryPush_add,
    unitaryPush_archimedean_evenDilation,
    unitaryPush_archimedean_evenDilation_symm]

/-- Pointwise source formula `M_(w_p)` for the positive Euler Gram. -/
theorem archimedeanPrimeEulerGram_ae
    (p : ℝ) (hp : 1 < p) (g : ArchimedeanWeightedL2) :
    archimedeanPrimeEulerGram p g =ᵐ[archimedeanWeightedMeasure]
      fun s => archimedeanPrimeEulerWeight p s * g s := by
  rw [archimedeanPrimeEulerGram_eq_affine p hp]
  change (((((1 + p⁻¹ : ℝ) : ℂ) • g) +
      (-((Real.sqrt p : ℂ)⁻¹)) •
        ((weightedMellinCharacterMulUnitary p g) +
          ((weightedMellinCharacterMulUnitary p).symm g))) :
            ArchimedeanWeightedL2) =ᵐ[_] _
  filter_upwards [Lp.coeFn_add
      ((((1 + p⁻¹ : ℝ) : ℂ) • g))
      ((-((Real.sqrt p : ℂ)⁻¹)) •
        (weightedMellinCharacterMulUnitary p g +
          (weightedMellinCharacterMulUnitary p).symm g)),
    Lp.coeFn_smul (((1 + p⁻¹ : ℝ) : ℂ)) g,
    Lp.coeFn_smul (-((Real.sqrt p : ℂ)⁻¹))
      (weightedMellinCharacterMulUnitary p g +
        (weightedMellinCharacterMulUnitary p).symm g),
    Lp.coeFn_add (weightedMellinCharacterMulUnitary p g)
      ((weightedMellinCharacterMulUnitary p).symm g),
    weightedMellinCharacterMulUnitary_ae p g,
    weightedMellinCharacterMulUnitary_symm_ae p g] with
      s hout hconst hscale hsum hplus hminus
  calc
    (((((1 + p⁻¹ : ℝ) : ℂ) • g) +
        (-((Real.sqrt p : ℂ)⁻¹)) •
          (weightedMellinCharacterMulUnitary p g +
            (weightedMellinCharacterMulUnitary p).symm g)) :
              ArchimedeanWeightedL2) s =
        ((((1 + p⁻¹ : ℝ) : ℂ) • g : ArchimedeanWeightedL2) s) +
          (((-((Real.sqrt p : ℂ)⁻¹)) •
            (weightedMellinCharacterMulUnitary p g +
              (weightedMellinCharacterMulUnitary p).symm g) :
                ArchimedeanWeightedL2) s) := hout
    _ = ((1 + p⁻¹ : ℝ) : ℂ) * g s +
          (-((Real.sqrt p : ℂ)⁻¹)) *
            ((weightedMellinCharacterMulUnitary p g +
              (weightedMellinCharacterMulUnitary p).symm g :
                ArchimedeanWeightedL2) s) := by
      rw [hconst, hscale]
      rfl
    _ = ((1 + p⁻¹ : ℝ) : ℂ) * g s +
          (-((Real.sqrt p : ℂ)⁻¹)) *
            ((weightedMellinCharacterMulUnitary p g) s +
              ((weightedMellinCharacterMulUnitary p).symm g) s) := by
      rw [hsum]
      rfl
    _ = ((1 + p⁻¹ : ℝ) : ℂ) * g s +
          (-((Real.sqrt p : ℂ)⁻¹)) *
            (MellinL2.mellinCharacter p s * g s +
              (MellinL2.mellinCharacter p s)⁻¹ * g s) := by
      rw [hplus, hminus]
    _ = archimedeanPrimeEulerWeight p s * g s := by
      simp only [archimedeanPrimeEulerWeight]
      ring

/-- The actual archimedean-norm boundary carrier projection `Pi^B_(a,infinity)`. -/
def archimedeanBoundaryCarrierProjection (a : ℝ) :
    ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2 :=
  hardyTitchmarshCarrierProjection archimedeanDualHardyTitchmarshUnitary a

/-- The literal source Euler corner `(1-Pi) M_(w_p) Pi`. -/
def archimedeanPrimeEulerCorner (a p : ℝ) :
    ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2 :=
  crossBoundary (archimedeanBoundaryCarrierProjection a)
    (archimedeanPrimeEulerGram p)

theorem archimedeanPrimeEulerCorner_eq_sourceCorner
    (a p : ℝ) (hp : 1 < p) :
    archimedeanPrimeEulerCorner a p =
      hardyTitchmarshEulerCorner archimedeanDualHardyTitchmarshUnitary a p hp := by
  rw [archimedeanPrimeEulerCorner, archimedeanBoundaryCarrierProjection,
    hardyTitchmarshEulerCorner, hardyTitchmarshEulerGram_archimedean_eq]

theorem archimedeanPrimeEulerCorner_pullback
    (a p : ℝ) (hp : 1 < p) :
    conjugateOperator archimedeanDualHardyTitchmarshUnitary.toContinuousLinearEquiv
      (archimedeanPrimeEulerCorner a p) =
        evenCentralPositiveEulerCorner a p hp := by
  rw [archimedeanPrimeEulerCorner_eq_sourceCorner (hp := hp)]
  exact hardyTitchmarshEulerCorner_pullback
    archimedeanDualHardyTitchmarshUnitary a p hp

theorem archimedeanPrimeEulerCorner_not_isCompactOperator
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    ¬ IsCompactOperator (archimedeanPrimeEulerCorner a p) := by
  rw [archimedeanPrimeEulerCorner_eq_sourceCorner (hp := hp)]
  exact hardyTitchmarshEulerCorner_not_isCompactOperator
    archimedeanDualHardyTitchmarshUnitary a p ha hp

theorem archimedeanPrimeEulerCorner_natPrime_not_isCompactOperator
    (a : ℝ) (p : ℕ) (ha : 0 < a) (hp : p.Prime) :
    ¬ IsCompactOperator (archimedeanPrimeEulerCorner a (p : ℝ)) :=
  archimedeanPrimeEulerCorner_not_isCompactOperator a (p : ℝ) ha (by
    exact_mod_cast hp.one_lt)

/-! ### The one-prime Fredholm seam -/

/-- Every physical one-prime Euler local factor is invertible.  The coefficient
`p⁻¹ᐟ²` has norm strictly below one, so the inverse is its norm-convergent geometric series. -/
theorem evenPrimeLocalFactor_isUnit (p : ℝ) (hp : 1 < p) :
    IsUnit (evenPrimeLocalFactor p hp) := by
  rw [evenPrimeLocalFactor]
  refine isUnit_one_sub_of_norm_lt_one
    (x := ((Real.sqrt p : ℂ)⁻¹) •
      ((evenDilationUnitary p (zero_lt_one.trans hp)).symm :
        evenSubspace →L[ℂ] evenSubspace)) ?_
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hsqrt0 : 0 < Real.sqrt p := Real.sqrt_pos.2 hp0
  have hsqrtSq : (Real.sqrt p) ^ 2 = p := by
    rw [sq, Real.mul_self_sqrt hp0.le]
  have hsqrt1 : 1 < Real.sqrt p := by nlinarith
  have hc : ‖(Real.sqrt p : ℂ)⁻¹‖ < 1 := by
    norm_cast
    rw [norm_inv, Real.norm_eq_abs, abs_of_pos hsqrt0]
    exact inv_lt_one_of_one_lt₀ hsqrt1
  calc
    ‖((Real.sqrt p : ℂ)⁻¹) •
        ((evenDilationUnitary p (zero_lt_one.trans hp)).symm :
          evenSubspace →L[ℂ] evenSubspace)‖
        ≤ ‖(Real.sqrt p : ℂ)⁻¹‖ *
            ‖((evenDilationUnitary p (zero_lt_one.trans hp)).symm :
              evenSubspace →L[ℂ] evenSubspace)‖ :=
            ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖(Real.sqrt p : ℂ)⁻¹‖ * 1 := by
      gcongr
      exact (evenDilationUnitary p
        (zero_lt_one.trans hp)).symm.toLinearIsometry.norm_toContinuousLinearMap_le
    _ < 1 := by simpa using hc

/-- The concrete spectral local factor is invertible: unitary transport preserves the inverse
constructed on the even physical carrier. -/
theorem archimedeanPrimeLocalFactor_isUnit (p : ℝ) (hp : 1 < p) :
    IsUnit (archimedeanPrimeLocalFactor p) := by
  rw [← hardyTitchmarshLocalFactor_archimedean_eq p hp,
    hardyTitchmarshLocalFactor]
  obtain ⟨v, hv⟩ := evenPrimeLocalFactor_isUnit p hp
  refine ⟨{
    val := unitaryPush archimedeanDualHardyTitchmarshUnitary v
    inv := unitaryPush archimedeanDualHardyTitchmarshUnitary (↑(v⁻¹))
    val_inv := ?_
    inv_val := ?_ }, ?_⟩
  · rw [← unitaryPush_mul]
    simp
  · rw [← unitaryPush_mul]
    simp
  · simp [hv]

/-- The positive one-prime Euler Gram is invertible. -/
theorem archimedeanPrimeEulerGram_isUnit (p : ℝ) (hp : 1 < p) :
    IsUnit (archimedeanPrimeEulerGram p) := by
  rw [archimedeanPrimeEulerGram]
  exact (archimedeanPrimeLocalFactor_isUnit p hp).star.mul
    (archimedeanPrimeLocalFactor_isUnit p hp)

/-- **One-prime Fredholm obstruction.**  Although the Euler Gram is invertible, its commutator
with the canonical archimedean Hardy--Titchmarsh carrier projection is not compact.  Indeed,
compactness of the commutator would make its lower corner compact, contradicting the concrete
noncompact Euler-corner theorem.  Thus the standard Toeplitz/Fredholm index mechanism is already
outside its compact-commutator domain at one prime. -/
theorem archimedeanPrimeEuler_projectionCommutator_not_isCompactOperator
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    ¬ IsCompactOperator
      (archimedeanBoundaryCarrierProjection a * archimedeanPrimeEulerGram p -
        archimedeanPrimeEulerGram p * archimedeanBoundaryCarrierProjection a :
          ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2) := by
  let Q := archimedeanBoundaryCarrierProjection a
  let G := archimedeanPrimeEulerGram p
  have hQ : IsIdempotentElem Q := by
    dsimp [Q, archimedeanBoundaryCarrierProjection,
      hardyTitchmarshCarrierProjection]
    exact (hardyTitchmarshBoundaryCarrier
      archimedeanDualHardyTitchmarshUnitary a).isIdempotentElem_starProjection
  intro hcomm
  have hleft := hcomm.clm_comp (1 - Q)
  have hcornerComm : IsCompactOperator ((1 - Q) * (Q * G - G * Q) :
      ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2) := by
    simpa only [mul_apply_eq_comp, Function.comp_apply] using! hleft
  have hcorner : IsCompactOperator (crossBoundary Q G :
      ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2) := by
    rw [crossBoundary_eq_corner_commutator hQ]
    exact hcornerComm.neg
  exact archimedeanPrimeEulerCorner_not_isCompactOperator a p ha hp (by
    simpa [Q, G, archimedeanPrimeEulerCorner] using hcorner)

end RHTower
