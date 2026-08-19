import GaloisForLFunctions.HTGeometry.CriticalSchurSourceIntegralClosure
import GaloisForLFunctions.HTGeometry.AnnihilatorLocalization
import GaloisForLFunctions.HTGeometry.DifferentIdealKaehlerAnnihilator
import GaloisForLFunctions.HTGeometry.CriticalRawCotangentBasis

/-!
# The ramification index of the source Schur place is exactly two

The Kähler different at the source Schur place is the maximal ideal, and the annihilator of a
localized module is the extension of the annihilator, so the Dedekind different of the source
integral closure has order exactly one at the Schur prime:

```text
criticalSchur_differentIdeal_eq_annihilator      Dedekind different = Kähler different
criticalSchur_differentIdeal_not_le_sq           the different is not inside the square
criticalSchur_source_ramificationIdx_le_two      by pow_sub_one_dvd_differentIdeal
criticalSchur_source_ramificationIdx_eq_two
    ** e(source Schur place / observation Schur place) = 2 **
```

The lower bound is the local ramification statement of the Schur place transported to the
localization of the integral closure, exactly as for the normal closure.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsLocalRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)

/-- Ground-field constants make the residue field of the observation Schur DVR characteristic
zero. -/
instance criticalSchurObservationResidueField_charZero :
    CharZero (IsLocalRing.ResidueField (criticalSchurObservationValuationSubring K hm hn)) :=
  (RingHom.charZero_iff
    (((IsLocalRing.residue (criticalSchurObservationValuationSubring K hm hn)).comp
      (criticalObservationSchurConstantBaseMap K hm hn)).injective)).mp inferInstance

instance criticalSchurSourceIntegralClosure_isTorsionFree :
    Module.IsTorsionFree (criticalSchurObservationValuationSubring K hm hn)
      (CriticalSchurSourceIntegralClosure K hm hn) :=
  (Module.isTorsionFree_iff_algebraMap_injective).mpr
    (FaithfulSMul.algebraMap_injective _ _)

theorem criticalSchur_maxExt_ne_bot :
    maxExt (criticalSchurObservationValuationSubring K hm hn)
      (CriticalSchurSourceIntegralClosure K hm hn) ≠ ⊥ := by
  intro hbot
  have hle : (IsLocalRing.maximalIdeal (criticalSchurObservationValuationSubring K hm hn))
      ≤ (⊥ : Ideal (CriticalSchurSourceIntegralClosure K hm hn)).comap
        (algebraMap (criticalSchurObservationValuationSubring K hm hn)
          (CriticalSchurSourceIntegralClosure K hm hn)) := by
    rw [← hbot]
    exact le_comap_maxExt _ _
  rw [← RingHom.ker_eq_comap_bot,
    (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective
      (criticalSchurObservationValuationSubring K hm hn)
      (CriticalSchurSourceIntegralClosure K hm hn))] at hle
  exact IsDiscreteValuationRing.not_a_field
    (criticalSchurObservationValuationSubring K hm hn) (le_bot_iff.mp hle)

/-- **The different of the source integral closure is the Kähler different.** -/
theorem criticalSchur_differentIdeal_eq_annihilator :
    differentIdeal (criticalSchurObservationValuationSubring K hm hn)
        (CriticalSchurSourceIntegralClosure K hm hn)
      = Module.annihilator (CriticalSchurSourceIntegralClosure K hm hn)
          Ω[CriticalSchurSourceIntegralClosure K hm hn⁄
            criticalSchurObservationValuationSubring K hm hn] := by
  haveI : FiniteDimensional (criticalObservationField K m n) (criticalSourceField K m n) :=
    criticalSourceField_finiteDimensional_criticalObservationField K hm hn
  exact differentIdeal_eq_annihilator_kaehler
    (criticalSchurObservationValuationSubring K hm hn)
    (criticalObservationField K m n)
    (L := criticalSourceField K m n)
    (B := CriticalSchurSourceIntegralClosure K hm hn)
    (criticalSchur_maxExt_ne_bot K hm hn)

instance criticalSchurSourceIntegralClosureUpperTower :
    IsScalarTower (criticalSchurObservationValuationSubring K hm hn)
      (CriticalSchurSourceIntegralClosure K hm hn)
      (criticalSchurSourceValuationSubring K hm hn) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

section Facts

variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- Nakayama in the source Schur valuation ring. -/
theorem criticalSchurSource_not_maximalIdeal_le_sq :
    ¬ (maximalIdeal (criticalSchurSourceValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n))
      ≤ (maximalIdeal (criticalSchurSourceValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n))) ^ 2) := by
  intro h
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
    (maximalIdeal (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)))
    (maximalIdeal (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)))
    (IsNoetherian.noetherian _) (by rwa [smul_eq_mul, ← pow_two])
    (IsLocalRing.maximalIdeal_le_jacobson _)
  exact IsDiscreteValuationRing.not_a_field
    (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) hbot

/-- The maximal ideal of the source Schur valuation ring is inside the extension of the
different. -/
theorem criticalSchur_maximalIdeal_le_map_differentIdeal :
    maximalIdeal (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      ≤ (differentIdeal
          (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
          (CriticalSchurSourceIntegralClosure K (Fact.out : 0 < m) (Fact.out : 0 < n))).map
        (algebraMap (CriticalSchurSourceIntegralClosure K (Fact.out : 0 < m) (Fact.out : 0 < n))
          (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))) := by
  rw [criticalSchur_differentIdeal_eq_annihilator K (Fact.out : 0 < m) (Fact.out : 0 < n),
    ← criticalSchur_annihilator_kaehler_eq_maximalIdeal K]
  exact annihilator_le_map_annihilator_of_isLocalizedModule
    (criticalSchurSourceIntegralClosurePrime K (Fact.out : 0 < m) (Fact.out : 0 < n)).primeCompl
    (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
    (KaehlerDifferential.map
      (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      (CriticalSchurSourceIntegralClosure K (Fact.out : 0 < m) (Fact.out : 0 < n))
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)))

/-- **The different of the source Schur place has order exactly one.** -/
theorem criticalSchur_differentIdeal_not_le_sq :
    ¬ (differentIdeal
        (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
        (CriticalSchurSourceIntegralClosure K (Fact.out : 0 < m) (Fact.out : 0 < n))
      ≤ (criticalSchurSourceIntegralClosurePrime K (Fact.out : 0 < m) (Fact.out : 0 < n)) ^ 2) := by
  intro hle
  have h1 := le_trans (criticalSchur_maximalIdeal_le_map_differentIdeal K) (Ideal.map_mono hle)
  rw [Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal] at h1
  exact criticalSchurSource_not_maximalIdeal_le_sq K h1

attribute [local instance] FractionRing.liftAlgebra

/-- **The ramification index of the source Schur place is at most two.** -/
theorem criticalSchur_source_ramificationIdx_le_two :
    Ideal.ramificationIdx'
        (maximalIdeal (criticalSchurObservationValuationSubring K (Fact.out : 0 < m)
          (Fact.out : 0 < n)))
        (criticalSchurSourceIntegralClosurePrime K (Fact.out : 0 < m) (Fact.out : 0 < n))
      ≤ 2 := by
  by_contra hgt
  push Not at hgt
  have hp : maximalIdeal (criticalSchurObservationValuationSubring K (Fact.out : 0 < m)
      (Fact.out : 0 < n)) ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have hdvd : (criticalSchurSourceIntegralClosurePrime K (Fact.out : 0 < m)
        (Fact.out : 0 < n)) ^ (Ideal.ramificationIdx'
        (maximalIdeal (criticalSchurObservationValuationSubring K (Fact.out : 0 < m)
          (Fact.out : 0 < n)))
        (criticalSchurSourceIntegralClosurePrime K (Fact.out : 0 < m) (Fact.out : 0 < n)))
      ∣ (maximalIdeal (criticalSchurObservationValuationSubring K (Fact.out : 0 < m)
          (Fact.out : 0 < n))).map
          (algebraMap (criticalSchurObservationValuationSubring K (Fact.out : 0 < m)
            (Fact.out : 0 < n))
            (CriticalSchurSourceIntegralClosure K (Fact.out : 0 < m) (Fact.out : 0 < n))) :=
    Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx'
  have hsub := pow_sub_one_dvd_differentIdeal
    (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
    (criticalSchurSourceIntegralClosurePrime K (Fact.out : 0 < m) (Fact.out : 0 < n)) _ hp hdvd
  refine criticalSchur_differentIdeal_not_le_sq (K := K) (m := m) (n := n) (Ideal.dvd_iff_le.mp ?_)
  exact dvd_trans (pow_dvd_pow _ (by omega)) hsub

/-- The source Schur valuation ring as the localization at the contracted prime. -/
def criticalSchurSourceLocalizationUpperEquiv :
    CriticalSchurSourceLocalization K (Fact.out : 0 < m) (Fact.out : 0 < n) ≃+*
      criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n) :=
  RingEquiv.ofBijective
    (criticalSchurSourceLocalizationToUpper K (Fact.out : 0 < m) (Fact.out : 0 < n))
    (criticalSchurSourceLocalizationToUpper_bijective K (Fact.out : 0 < m) (Fact.out : 0 < n))

theorem criticalSchurSourceLocalizationUpperEquiv_comp :
    (criticalSchurSourceLocalizationUpperEquiv K (m := m) (n := n)).toRingHom.comp
        (algebraMap (criticalSchurObservationValuationSubring K (Fact.out : 0 < m)
          (Fact.out : 0 < n))
          (CriticalSchurSourceLocalization K (Fact.out : 0 < m) (Fact.out : 0 < n)))
      = algebraMap (criticalSchurObservationValuationSubring K (Fact.out : 0 < m)
          (Fact.out : 0 < n))
          (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) := by
  refine RingHom.ext fun x => ?_
  show criticalSchurSourceLocalizationToUpper K (Fact.out : 0 < m) (Fact.out : 0 < n)
      (algebraMap (criticalSchurObservationValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n))
        (CriticalSchurSourceLocalization K (Fact.out : 0 < m) (Fact.out : 0 < n)) x) = _
  rw [IsScalarTower.algebraMap_apply
      (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      (CriticalSchurSourceIntegralClosure K (Fact.out : 0 < m) (Fact.out : 0 < n))
      (CriticalSchurSourceLocalization K (Fact.out : 0 < m) (Fact.out : 0 < n)),
    criticalSchurSourceLocalizationToUpper_algebraMap K (Fact.out : 0 < m) (Fact.out : 0 < n)]
  rfl

instance criticalSchurSourceLocalizationUpperEquiv_isLocalHom :
    IsLocalHom (criticalSchurSourceLocalizationUpperEquiv K (m := m) (n := n)).toRingHom :=
  ⟨fun a ha => by
    simpa using ha.map (criticalSchurSourceLocalizationUpperEquiv K (m := m) (n := n)).symm⟩

theorem criticalSchurSourceLocalizationUpperEquiv_map_maximalIdeal :
    Ideal.map (criticalSchurSourceLocalizationUpperEquiv K (m := m) (n := n)).toRingHom
        (maximalIdeal
          (CriticalSchurSourceLocalization K (Fact.out : 0 < m) (Fact.out : 0 < n)))
      = maximalIdeal (criticalSchurSourceValuationSubring K (Fact.out : 0 < m)
          (Fact.out : 0 < n)) := by
  conv_lhs =>
    rw [← IsLocalRing.maximalIdeal_comap
      (criticalSchurSourceLocalizationUpperEquiv K (m := m) (n := n)).toRingHom]
  exact Ideal.map_comap_of_surjective _
    (criticalSchurSourceLocalizationUpperEquiv K (m := m) (n := n)).surjective _

theorem criticalSchur_source_map_maximalIdeal_localization_ne :
    (maximalIdeal (criticalSchurObservationValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n))).map
        (algebraMap (criticalSchurObservationValuationSubring K (Fact.out : 0 < m)
          (Fact.out : 0 < n))
          (CriticalSchurSourceLocalization K (Fact.out : 0 < m) (Fact.out : 0 < n)))
      ≠ maximalIdeal
          (CriticalSchurSourceLocalization K (Fact.out : 0 < m) (Fact.out : 0 < n)) := by
  intro h
  have key := congrArg (fun I => Ideal.map
    (criticalSchurSourceLocalizationUpperEquiv K (m := m) (n := n)).toRingHom I) h
  rw [Ideal.map_map, criticalSchurSourceLocalizationUpperEquiv_comp,
    criticalSchurSourceLocalizationUpperEquiv_map_maximalIdeal] at key
  exact criticalSchurSource_not_maximalIdeal_le_sq K
    (key ▸ criticalSchur_map_maximalIdeal_le_sq K)

/-- **The ramification index of the source Schur place over the observation Schur place is
exactly two.** -/
theorem criticalSchur_source_ramificationIdx_eq_two :
    Ideal.ramificationIdx'
        (maximalIdeal (criticalSchurObservationValuationSubring K (Fact.out : 0 < m)
          (Fact.out : 0 < n)))
        (criticalSchurSourceIntegralClosurePrime K (Fact.out : 0 < m) (Fact.out : 0 < n))
      = 2 := by
  haveI hlies := criticalSchurSourceIntegralClosurePrime_liesOver K
    (Fact.out : 0 < m) (Fact.out : 0 < n)
  have hp : maximalIdeal (criticalSchurObservationValuationSubring K (Fact.out : 0 < m)
      (Fact.out : 0 < n)) ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have hpP := Ideal.map_le_iff_le_comap.mpr (le_of_eq hlies.over)
  have h0 := Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver
    (criticalSchurSourceIntegralClosurePrime K (Fact.out : 0 < m) (Fact.out : 0 < n)) hp
  have h1 : Ideal.ramificationIdx'
      (maximalIdeal (criticalSchurObservationValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n)))
      (criticalSchurSourceIntegralClosurePrime K (Fact.out : 0 < m) (Fact.out : 0 < n))
      ≠ 1 := by
    rw [Ne, Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff
      (criticalSchurSourceIntegralClosurePrime_ne_bot K (Fact.out : 0 < m) (Fact.out : 0 < n))
      hpP]
    exact criticalSchur_source_map_maximalIdeal_localization_ne K
  have h2 := criticalSchur_source_ramificationIdx_le_two K (m := m) (n := n)
  omega

end Facts

end

end GaloisForLFunctions.HTGeometry
