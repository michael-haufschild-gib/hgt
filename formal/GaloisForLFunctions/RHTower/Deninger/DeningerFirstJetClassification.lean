import GaloisForLFunctions.HTGeometry.GroupAlgebras.CharacterFirstJet
import GaloisForLFunctions.RHTower.Deninger.DeningerSignedAugmentationSquares

/-!
# Complete first-order classification of the rational Steinberg quotient

The universal first jets at the trivial and sign characters have kernels equal
to the respective augmentation squares. Their intersection is the positive
Steinberg ideal. Chinese remaindering realizes the two jets independently and
identifies the actual source quotient with the product of two square-zero algebras.
-/

noncomputable section
namespace RHTower
open GaloisForLFunctions.RHTower GaloisForLFunctions.HTGeometry.GroupAlgebraFirstJet

abbrev DeningerMomentSpace := MomentSpace ℂ CCMRationalAdelicScaling

/-- Augmentation and the universal first moment of rational scaling labels. -/
def deningerFirstJet : RouteRMultiplierKOne.KummerGroupRing →ₐ[ℂ]
    TrivSqZeroExt ℂ DeningerMomentSpace := jet ℂ CCMRationalAdelicScaling

private theorem augmentation_eq_native :
    augmentation ℂ CCMRationalAdelicScaling = deningerKummerAugmentation := by
  apply AlgHom.toLinearMap_injective
  apply (MonoidAlgebra.basis CCMRationalAdelicScaling ℂ).ext
  intro g
  change augmentation ℂ CCMRationalAdelicScaling (MonoidAlgebra.of ℂ _ g) = _
  rw [augmentation_of]
  exact (deningerKummerAugmentation_basis g).symm

/-- The sign character, read from the source's existing sign augmentation. -/
def deningerSignCharacter : CCMRationalAdelicScaling →* ℂ :=
  deningerKummerSignAugmentation.toMonoidHom.comp (MonoidAlgebra.of ℂ CCMRationalAdelicScaling)

private theorem characterAugmentation_eq_native :
    characterAugmentation deningerSignCharacter = deningerKummerSignAugmentation := by
  apply AlgHom.toLinearMap_injective
  apply (MonoidAlgebra.basis CCMRationalAdelicScaling ℂ).ext
  intro g
  change characterAugmentation deningerSignCharacter (MonoidAlgebra.of ℂ _ g) = _
  rw [characterAugmentation, MonoidAlgebra.lift_of]
  rfl

/-- First jet at the sign character. -/
def deningerSignedFirstJet : RouteRMultiplierKOne.KummerGroupRing →ₐ[ℂ]
    TrivSqZeroExt ℂ DeningerMomentSpace :=
  (jet ℂ CCMRationalAdelicScaling).comp (twist deningerSignCharacter)

theorem deningerFirstJet_kernel : RingHom.ker deningerFirstJet.toRingHom =
    deningerKummerAugmentationIdeal^2 := by
  rw [deningerFirstJet, jet_ker_eq_square, augmentationIdeal, augmentation_eq_native]
  rfl

theorem deningerSignedFirstJet_kernel : RingHom.ker deningerSignedFirstJet.toRingHom =
    deningerSignAugmentationIdeal^2 := by
  rw [deningerSignedFirstJet, character_jet_ker, characterAugmentation_eq_native]
  rfl

theorem deningerFirstJet_fst (v : RouteRMultiplierKOne.KummerGroupRing) :
    (deningerFirstJet v).fst = deningerKummerAugmentation v := by
  change (jet ℂ CCMRationalAdelicScaling v).fst = _
  rw [jet_fst, augmentation_eq_native]

theorem deningerSignedFirstJet_fst (v : RouteRMultiplierKOne.KummerGroupRing) :
    (deningerSignedFirstJet v).fst = deningerKummerSignAugmentation v := by
  change (jet ℂ CCMRationalAdelicScaling (twist deningerSignCharacter v)).fst = _
  rw [jet_fst, augmentation_twist, characterAugmentation_eq_native]

/-- Both rational-sign sectors are needed to detect the positive Steinberg ideal exactly. -/
theorem deningerSteinberg_mem_iff_first_jets (v : RouteRMultiplierKOne.KummerGroupRing) :
    v ∈ deningerKummerSteinbergIdeal ↔ deningerFirstJet v = 0 ∧ deningerSignedFirstJet v = 0 := by
  rw [deningerSteinberg_eq_signed_squares, ← deningerFirstJet_kernel,
    ← deningerSignedFirstJet_kernel]
  rfl

/-- The simultaneous first jets at the trivial and sign characters. -/
def deningerPairedFirstJet : RouteRMultiplierKOne.KummerGroupRing →ₐ[ℂ]
    (TrivSqZeroExt ℂ DeningerMomentSpace × TrivSqZeroExt ℂ DeningerMomentSpace) :=
  deningerFirstJet.prod deningerSignedFirstJet

theorem deningerPairedFirstJet_kernel : RingHom.ker deningerPairedFirstJet.toRingHom =
    deningerKummerSteinbergIdeal := by
  ext v
  rw [deningerSteinberg_mem_iff_first_jets]
  change (deningerFirstJet v, deningerSignedFirstJet v) = (0, 0) ↔ _
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨h1, h2⟩
    exact Prod.ext h1 h2

/-- The two first-order sectors can be prescribed independently by Chinese remaindering. -/
theorem deningerPairedFirstJet_surjective : Function.Surjective deningerPairedFirstJet := by
  intro z
  obtain ⟨a, ha⟩ := jet_surjective ℂ CCMRationalAdelicScaling z.1
  obtain ⟨b, hb⟩ := jet_surjective ℂ CCMRationalAdelicScaling z.2
  let b' := (twistEquiv deningerSignCharacter).symm b
  have hb' : deningerSignedFirstJet b' = z.2 := by
    change jet ℂ CCMRationalAdelicScaling
      (twistEquiv deningerSignCharacter ((twistEquiv deningerSignCharacter).symm b)) = _
    rw [AlgEquiv.apply_symm_apply]
    exact hb
  let I := RingHom.ker deningerFirstJet.toRingHom
  let J := RingHom.ker deningerSignedFirstJet.toRingHom
  have hc : IsCoprime I J := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    change RingHom.ker deningerFirstJet.toRingHom ⊔
      RingHom.ker deningerSignedFirstJet.toRingHom = ⊤
    rw [deningerFirstJet_kernel, deningerSignedFirstJet_kernel]
    exact Ideal.pow_sup_pow_eq_top deningerSignedAugmentations_coprime
  obtain ⟨q, hq⟩ := (Ideal.quotientInfEquivQuotientProd I J hc).surjective
    (Ideal.Quotient.mk I a, Ideal.Quotient.mk J b')
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective q
  have h1 : Ideal.Quotient.mk I v = Ideal.Quotient.mk I a := by
    simpa using congrArg Prod.fst hq
  have h2 : Ideal.Quotient.mk J v = Ideal.Quotient.mk J b' := by
    simpa using congrArg Prod.snd hq
  have hv1 : deningerFirstJet v = deningerFirstJet a :=
    congrArg (RingHom.kerLift deningerFirstJet.toRingHom) h1
  have hv2 : deningerSignedFirstJet v = deningerSignedFirstJet b' :=
    congrArg (RingHom.kerLift deningerSignedFirstJet.toRingHom) h2
  exact ⟨v, Prod.ext (hv1.trans ha) (hv2.trans hb')⟩

/-- The full Steinberg quotient is the product of its two square-zero first-order sectors. -/
def deningerSteinbergFirstJetEquiv :
    (RouteRMultiplierKOne.KummerGroupRing ⧸ deningerKummerSteinbergIdeal) ≃ₐ[ℂ]
      (TrivSqZeroExt ℂ DeningerMomentSpace × TrivSqZeroExt ℂ DeningerMomentSpace) := by
  rw [← deningerPairedFirstJet_kernel]
  exact Ideal.quotientKerAlgEquivOfSurjective deningerPairedFirstJet_surjective

#print axioms deningerSteinberg_mem_iff_first_jets
#print axioms deningerSteinbergFirstJetEquiv
end RHTower
