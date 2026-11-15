import GaloisForLFunctions.RHTower.Deninger.DeningerPositiveSteinbergSquare

/-!
# The two rational-sign components of the positive Steinberg ideal

Modulo positive-rational augmentation generators, every positive basis label
becomes `1` and every negative label becomes `[-1]`. The ordinary and sign
augmentations recover these two coefficients, so their kernel intersection is
exactly the positive augmentation ideal. They are comaximal because `2` is
invertible over `ℂ`.

Consequently the positive Steinberg ideal is the intersection of the squares
of the two augmentation kernels. Both rational-sign components are retained.
-/

noncomputable section
namespace RHTower
open GaloisForLFunctions.RHTower

private abbrev SignQuotient := RouteRMultiplierKOne.KummerGroupRing ⧸ deningerPositiveAugmentationIdeal

private def signQuotientMap : RouteRMultiplierKOne.KummerGroupRing →ₐ[ℂ] SignQuotient :=
  Ideal.Quotient.mkₐ ℂ deningerPositiveAugmentationIdeal

private def negativeBasis : RouteRMultiplierKOne.KummerGroupRing :=
  deningerSteinbergBasis ⟨(-1 : ℚˣ)⟩

private theorem signAugmentation_negative : deningerKummerSignAugmentation negativeBasis = -1 := by
  rw [negativeBasis, deningerSteinbergBasis, deningerKummerSignAugmentation, MonoidAlgebra.lift_of]
  change (SignType.castHom (signHom (-1 : ℚ)) : ℂ) = -1
  norm_num [signHom]

private theorem signAugmentation_basis_pos (g : CCMRationalAdelicScaling) (hg : 0 < (g.val : ℚ)) :
    deningerKummerSignAugmentation (deningerSteinbergBasis g) = 1 := by
  rw [deningerSteinbergBasis, deningerKummerSignAugmentation, MonoidAlgebra.lift_of]
  change (SignType.castHom (signHom (g.val : ℚ)) : ℂ) = 1
  simp [signHom, sign_pos hg]

private theorem signAugmentation_basis_neg (g : CCMRationalAdelicScaling) (hg : (g.val : ℚ) < 0) :
    deningerKummerSignAugmentation (deningerSteinbergBasis g) = -1 := by
  rw [deningerSteinbergBasis, deningerKummerSignAugmentation, MonoidAlgebra.lift_of]
  change (SignType.castHom (signHom (g.val : ℚ)) : ℂ) = -1
  simp [signHom, sign_neg hg]

private theorem signQuotient_positive (g : CCMRationalAdelicScaling) (hg : 0 < (g.val : ℚ)) :
    signQuotientMap (deningerSteinbergBasis g) = 1 := by
  have he : deningerScalingOfPositiveRational (g.val : ℚ) hg = g := by
    apply ccmRationalAdelicScalingEquiv.injective
    apply Units.ext
    rfl
  have hm : deningerSteinbergBasis g - 1 ∈ deningerPositiveAugmentationIdeal := by
    rw [← he]
    exact Ideal.subset_span (Set.mem_range_self (⟨(g.val : ℚ), hg⟩ : {q : ℚ // 0 < q}))
  have hz : signQuotientMap (deningerSteinbergBasis g - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hm
  rwa [map_sub, map_one, sub_eq_zero] at hz

private theorem signQuotient_negative (g : CCMRationalAdelicScaling) (hg : (g.val : ℚ) < 0) :
    signQuotientMap (deningerSteinbergBasis g) = signQuotientMap negativeBasis := by
  let p : CCMRationalAdelicScaling := ⟨-g.val⟩
  have hp : 0 < (p.val : ℚ) := neg_pos.mpr hg
  have he : (⟨(-1 : ℚˣ)⟩ : CCMRationalAdelicScaling) * p = g := by
    apply ccmRationalAdelicScalingEquiv.injective
    apply Units.ext
    change (-1 : ℚ) * -(g.val : ℚ) = (g.val : ℚ)
    ring
  calc
    signQuotientMap (deningerSteinbergBasis g) =
      signQuotientMap (negativeBasis * deningerSteinbergBasis p) := by
        rw [negativeBasis, ← deningerSteinbergBasis_mul, he]
    _ = signQuotientMap negativeBasis := by rw [map_mul, signQuotient_positive p hp, mul_one]

private def signReconstruction : RouteRMultiplierKOne.KummerGroupRing →ₗ[ℂ] SignQuotient :=
  (deningerKummerAugmentation.toLinearMap + deningerKummerSignAugmentation.toLinearMap).smulRight
      ((2 : ℂ)⁻¹ • (1 : SignQuotient)) +
  (deningerKummerAugmentation.toLinearMap - deningerKummerSignAugmentation.toLinearMap).smulRight
      ((2 : ℂ)⁻¹ • signQuotientMap negativeBasis)

private theorem signQuotient_reconstruction (v : RouteRMultiplierKOne.KummerGroupRing) :
    signQuotientMap v = signReconstruction v := by
  have h : signQuotientMap.toLinearMap = signReconstruction := by
    apply (MonoidAlgebra.basis CCMRationalAdelicScaling ℂ).ext
    intro g
    change signQuotientMap (deningerSteinbergBasis g) = _
    have hne : (g.val : ℚ) ≠ 0 := Units.ne_zero g.val
    rcases lt_or_gt_of_ne hne with hg | hg
    · rw [signQuotient_negative g hg]
      norm_num [signReconstruction,
        show deningerKummerAugmentation (MonoidAlgebra.single g 1) = 1 from
          deningerKummerAugmentation_basis g,
        show deningerKummerSignAugmentation (MonoidAlgebra.single g 1) = -1 from
          signAugmentation_basis_neg g hg, smul_smul]
    · rw [signQuotient_positive g hg]
      norm_num [signReconstruction,
        show deningerKummerAugmentation (MonoidAlgebra.single g 1) = 1 from
          deningerKummerAugmentation_basis g,
        show deningerKummerSignAugmentation (MonoidAlgebra.single g 1) = 1 from
          signAugmentation_basis_pos g hg, smul_smul]
  exact LinearMap.congr_fun h v

/-- The kernel of sign-weighted coefficient summation. -/
def deningerSignAugmentationIdeal : Ideal RouteRMultiplierKOne.KummerGroupRing :=
  RingHom.ker deningerKummerSignAugmentation.toRingHom

/-- Positive augmentation generators impose vanishing at both sign characters. -/
theorem deningerPositiveAugmentationIdeal_eq_inf : deningerPositiveAugmentationIdeal =
    deningerKummerAugmentationIdeal ⊓ deningerSignAugmentationIdeal := by
  apply le_antisymm
  · rw [deningerPositiveAugmentationIdeal, Ideal.span_le]
    rintro _ ⟨q, rfl⟩
    constructor
    · exact deningerSteinbergBasis_sub_one_mem_augmentationIdeal _
    · change deningerKummerSignAugmentation (_ - 1) = 0
      rw [map_sub, deningerKummerSignAugmentation_positive, map_one, sub_self]
  · intro v hv
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change signQuotientMap v = 0
    rw [signQuotient_reconstruction]
    have h1 : deningerKummerAugmentation v = 0 := hv.1
    have h2 : deningerKummerSignAugmentation v = 0 := hv.2
    simp [signReconstruction, h1, h2]

/-- The two character ideals are comaximal. -/
theorem deningerSignedAugmentations_coprime : deningerKummerAugmentationIdeal ⊔
    deningerSignAugmentationIdeal = ⊤ := by
  apply top_unique
  intro v _
  suffices h1 : (1 : RouteRMultiplierKOne.KummerGroupRing) ∈
      deningerKummerAugmentationIdeal ⊔ deningerSignAugmentationIdeal by
    simpa only [mul_one] using
      (deningerKummerAugmentationIdeal ⊔ deningerSignAugmentationIdeal).mul_mem_left v h1
  have ha : 1 - negativeBasis ∈ deningerKummerAugmentationIdeal := by
    change deningerKummerAugmentation (1 - negativeBasis) = 0
    simp [negativeBasis]
  have hb : 1 + negativeBasis ∈ deningerSignAugmentationIdeal := by
    change deningerKummerSignAugmentation (1 + negativeBasis) = 0
    rw [map_add, map_one, signAugmentation_negative, add_neg_cancel]
  have hs := (deningerKummerAugmentationIdeal ⊔ deningerSignAugmentationIdeal).add_mem
    (show (algebraMap ℂ _ (2⁻¹ : ℂ)) * (1 - negativeBasis) ∈
        deningerKummerAugmentationIdeal ⊔ deningerSignAugmentationIdeal from
      (show deningerKummerAugmentationIdeal ≤
        deningerKummerAugmentationIdeal ⊔ deningerSignAugmentationIdeal from le_sup_left)
        (deningerKummerAugmentationIdeal.mul_mem_left _ ha))
    (show (algebraMap ℂ _ (2⁻¹ : ℂ)) * (1 + negativeBasis) ∈
        deningerKummerAugmentationIdeal ⊔ deningerSignAugmentationIdeal from
      (show deningerSignAugmentationIdeal ≤
        deningerKummerAugmentationIdeal ⊔ deningerSignAugmentationIdeal from le_sup_right)
        (deningerSignAugmentationIdeal.mul_mem_left _ hb))
  have he : (algebraMap ℂ RouteRMultiplierKOne.KummerGroupRing (2⁻¹ : ℂ)) *
      (1 - negativeBasis) + (algebraMap ℂ _ (2⁻¹ : ℂ)) * (1 + negativeBasis) = 1 := by
    calc
      _ = algebraMap ℂ RouteRMultiplierKOne.KummerGroupRing (2⁻¹ : ℂ) * 2 := by ring
      _ = algebraMap ℂ RouteRMultiplierKOne.KummerGroupRing ((2⁻¹ : ℂ) * 2) := by
        rw [map_mul, map_ofNat]
      _ = 1 := by rw [inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), map_one]
  exact he ▸ hs

/-- The positive Steinberg ideal is the intersection of both character-ideal squares. -/
theorem deningerSteinberg_eq_signed_squares : deningerKummerSteinbergIdeal =
    deningerKummerAugmentationIdeal^2 ⊓ deningerSignAugmentationIdeal^2 := by
  rw [deningerKummerSteinbergIdeal_eq_positiveAugmentationIdeal_sq, deningerPositiveAugmentationIdeal_eq_inf,
    ← Ideal.mul_eq_inf_of_coprime deningerSignedAugmentations_coprime, mul_pow,
    Ideal.mul_eq_inf_of_coprime (Ideal.pow_sup_pow_eq_top deningerSignedAugmentations_coprime)]

#print axioms deningerPositiveAugmentationIdeal_eq_inf
#print axioms deningerSteinberg_eq_signed_squares
end RHTower
