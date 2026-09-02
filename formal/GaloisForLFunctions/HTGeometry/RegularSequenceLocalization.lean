import GaloisForLFunctions.HTGeometry.LocalizationQuotient
import GaloisForLFunctions.HTGeometry.RegularSequenceBridge
import Mathlib.RingTheory.Flat.Localization

/-!
# Ring-regular sequences are local at maximal ideals

This file supplies the local-to-global direction missing from mathlib's regular-sequence API.  A
sequence in a nontrivial commutative ring is ring-regular if its image is ring-regular in every
maximal localization.  For each prefix, multiplication on its quotient is tested after localizing
at every maximal ideal.  The quotient of a localization is the corresponding localization of the
quotient, so maximal-localization injectivity descends the required nonzerodivisor statement.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

open RingTheory.Sequence

/-- **Ring-regularity is detected by all maximal localizations.** -/
theorem isRingRegularSeq_of_localizationAtMaximal
    {D : Type u} [CommRing D] [Nontrivial D]
    (rs : List D)
    (hlocal : ∀ (q : Ideal D) [q.IsMaximal],
      IsRingRegularSeq
        (rs.map (algebraMap D (Localization.AtPrime q)))) :
    IsRingRegularSeq rs := by
  constructor
  · intro i hi
    let I := Ideal.ofList (rs.take i)
    let r := rs[i]
    apply (isSMulRegular_quotient_iff I r).mp
    refine injective_of_isLocalized_maximal
      (fun q _ => LocalizedModule.AtPrime q (D ⧸ I))
      (fun q _ => LocalizedModule.mkLinearMap q.primeCompl (D ⧸ I))
      (fun q _ => LocalizedModule.AtPrime q (D ⧸ I))
      (fun q _ => LocalizedModule.mkLinearMap q.primeCompl (D ⧸ I))
      (LinearMap.lsmul D (D ⧸ I) r) ?_
    intro q hq
    let B := Localization.AtPrime q
    let IQ : Ideal B := Ideal.map (algebraMap D B) I
    let Q := B ⧸ IQ
    letI := (localizationQuotientMap (S := B) I).toAlgebra
    letI : IsLocalization
        (q.primeCompl.map (Ideal.Quotient.mk I)) Q :=
      isLocalization_localizationQuotientMap q.primeCompl I
    letI : IsScalarTower D (D ⧸ I) Q :=
      IsScalarTower.of_algebraMap_eq fun z => rfl
    let fQ : (D ⧸ I) →ₗ[D] Q :=
      (IsScalarTower.toAlgHom D (D ⧸ I) Q).toLinearMap
    haveI : IsLocalizedModule q.primeCompl fQ := by
      apply isLocalizedModule_iff_isLocalization.mpr
      simpa [Algebra.algebraMapSubmonoid, Ideal.Quotient.algebraMap_eq] using
        (inferInstance : IsLocalization
          (q.primeCompl.map (Ideal.Quotient.mk I)) Q)
    apply (IsLocalizedModule.map_injective_iff_localizedModuleMap_injective fQ fQ).mp
    have hregLocal := (hlocal q).regular i (by simpa using hi)
    have hregQ : IsSMulRegular Q r := by
      have hregQB : IsSMulRegular Q (algebraMap D B r) := by
        apply (isSMulRegular_quotient_iff IQ (algebraMap D B r)).mpr
        simpa [I, r, IQ, ← List.map_take] using hregLocal
      rw [isSMulRegular_iff_right_eq_zero_of_smul] at hregQB ⊢
      intro z hz
      apply hregQB
      simpa only [IsScalarTower.algebraMap_smul B r] using hz
    have hmap :
        (IsLocalizedModule.map q.primeCompl fQ fQ)
            (LinearMap.lsmul D (D ⧸ I) r) =
          LinearMap.lsmul D Q r := by
      apply IsLocalizedModule.linearMap_ext q.primeCompl fQ fQ
      apply LinearMap.ext
      intro z
      rw [LinearMap.comp_apply, LinearMap.comp_apply,
        IsLocalizedModule.map_apply]
      simp only [LinearMap.lsmul_apply, map_smul]
    rw [hmap]
    exact hregQ
  · intro htop
    obtain ⟨q, hq⟩ := Ideal.exists_maximal D
    letI : q.IsMaximal := hq
    have hp := (hlocal q).proper
    apply hp
    rw [← Ideal.map_ofList, htop, Ideal.map_top]

end

end GaloisForLFunctions.HTGeometry
