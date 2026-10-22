import GaloisForLFunctions.HTGeometry.Critical.Schur.Ramifies
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import GaloisForLFunctions.HTGeometry.Critical.Schur.RamificationInertia

/-!
# Transport of Schur ramification to the normal closure

The local ramification statement at the source Schur place travels up to the chosen Schur place of
the normal closure, and from there to the localization of the normal integral closure:

```text
criticalSchur_normalUpper_map_maximalIdeal_le_sq
    𝔪(observation Schur place) · V  ⊆  𝔪(V)²,  V the normal-closure Schur valuation ring
criticalNormalUpper_not_maximalIdeal_le_sq       Nakayama in a discrete valuation ring
criticalSchur_map_maximalIdeal_localization_ne
    ** the extended maximal ideal is not the maximal ideal of the localization **
```

The last statement is exactly the hypothesis that rules out ramification index one at the Schur
prime of the normal integral closure.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsLocalRing

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- The source Schur valuation ring inside the chosen normal-closure Schur valuation ring. -/
def criticalSchurSourceToNormalUpper :
    criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n) →+*
      criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n) :=
  (criticalSchurSourceValuationToNormalClosure K (Fact.out : 0 < m)
      (Fact.out : 0 < n)).codRestrict
    (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
      (Fact.out : 0 < n)).toSubring
    (criticalNormalClosureSchurValuationSubring_source_mem K (Fact.out : 0 < m)
      (Fact.out : 0 < n))

instance criticalSchurSourceToNormalUpper_isLocalHom :
    IsLocalHom (criticalSchurSourceToNormalUpper K (m := m) (n := n)) :=
  criticalSchurSourceValuationToNormalClosure_isLocalHom K (Fact.out : 0 < m) (Fact.out : 0 < n)

omit [IsAlgClosed K] [Fact (1 < m)] [Fact (1 < n)] in
theorem criticalSchurSourceToNormalUpper_comp :
    (criticalSchurSourceToNormalUpper K (m := m) (n := n)).comp
        (algebraMap
          (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
          (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)))
      = criticalSchurObservationValuationToNormalClosure K (Fact.out : 0 < m)
          (Fact.out : 0 < n) := by
  refine RingHom.ext fun x => ?_
  apply Subtype.ext
  exact (criticalSourceNormalClosureEmbedding K m n).commutes _

/-- The extended maximal ideal of the observation Schur place lies in the square of the maximal
ideal of the chosen normal-closure Schur place. -/
theorem criticalSchur_normalUpper_map_maximalIdeal_le_sq :
    (maximalIdeal
        (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))).map
        (criticalSchurObservationValuationToNormalClosure K (Fact.out : 0 < m)
          (Fact.out : 0 < n))
      ≤ (maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
          (Fact.out : 0 < n))) ^ (2 : ℕ) := by
  rw [← criticalSchurSourceToNormalUpper_comp K, ← Ideal.map_map]
  refine le_trans (Ideal.map_mono (criticalSchur_map_maximalIdeal_le_sq K)) ?_
  rw [Ideal.map_pow]
  refine pow_le_pow_left' ?_ 2
  exact Ideal.map_le_iff_le_comap.mpr
    (le_of_eq (IsLocalRing.maximalIdeal_comap
      (criticalSchurSourceToNormalUpper K (m := m) (n := n))).symm)

omit [Fact (1 < m)] [Fact (1 < n)] in
/-- Nakayama: the maximal ideal of a discrete valuation ring is not contained in its square. -/
theorem criticalNormalUpper_not_maximalIdeal_le_sq :
    ¬ (maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n))
      ≤ (maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n))) ^ (2 : ℕ)) := by
  intro h
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
    (maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
      (Fact.out : 0 < n)))
    (maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
      (Fact.out : 0 < n)))
    (IsNoetherian.noetherian _) (by rwa [smul_eq_mul, ← pow_two])
    (IsLocalRing.maximalIdeal_le_jacobson _)
  exact IsDiscreteValuationRing.not_a_field
    (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) hbot

/-- The extended maximal ideal is a proper subideal of the maximal ideal of the chosen
normal-closure Schur place. -/
theorem criticalSchur_normalUpper_map_maximalIdeal_ne :
    (maximalIdeal
        (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))).map
        (criticalSchurObservationValuationToNormalClosure K (Fact.out : 0 < m)
          (Fact.out : 0 < n))
      ≠ maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
          (Fact.out : 0 < n)) := by
  intro h
  exact criticalNormalUpper_not_maximalIdeal_le_sq K
    (h ▸ criticalSchur_normalUpper_map_maximalIdeal_le_sq K)

/-- The canonical isomorphism from the Schur-prime localization of the normal integral closure
onto the chosen normal-closure Schur valuation ring. -/
def criticalSchurNormalLocalizationUpperEquiv :
    CriticalSchurNormalLocalization K (Fact.out : 0 < m) (Fact.out : 0 < n) ≃+*
      criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n) :=
  (criticalSchurNormalLocalizationEquivUpper K (Fact.out : 0 < m)
    (Fact.out : 0 < n)).toRingEquiv

omit [Fact (1 < m)] [Fact (1 < n)] in
/-- The isomorphism is compatible with the observation Schur place. -/
theorem criticalSchurNormalLocalizationUpperEquiv_comp :
    (criticalSchurNormalLocalizationUpperEquiv K (m := m) (n := n)).toRingHom.comp
        (algebraMap (CriticalSchurNormalBaseRing K (Fact.out : 0 < m) (Fact.out : 0 < n))
          (CriticalSchurNormalLocalization K (Fact.out : 0 < m) (Fact.out : 0 < n)))
      = criticalSchurObservationValuationToNormalClosure K (Fact.out : 0 < m)
          (Fact.out : 0 < n) := by
  refine RingHom.ext fun x => ?_
  show (criticalSchurNormalLocalizationEquivUpper K (Fact.out : 0 < m) (Fact.out : 0 < n))
      (algebraMap (CriticalSchurNormalBaseRing K (Fact.out : 0 < m) (Fact.out : 0 < n))
        (CriticalSchurNormalLocalization K (Fact.out : 0 < m) (Fact.out : 0 < n)) x) = _
  rw [IsScalarTower.algebraMap_apply
      (CriticalSchurNormalBaseRing K (Fact.out : 0 < m) (Fact.out : 0 < n))
      (CriticalSchurNormalIntegralClosure K (Fact.out : 0 < m) (Fact.out : 0 < n))
      (CriticalSchurNormalLocalization K (Fact.out : 0 < m) (Fact.out : 0 < n))]
  exact (criticalSchurNormalLocalizationEquivUpper K (Fact.out : 0 < m)
    (Fact.out : 0 < n)).commutes _

omit [Fact (1 < m)] [Fact (1 < n)] in
instance criticalSchurNormalLocalizationUpperEquiv_isLocalHom :
    IsLocalHom (criticalSchurNormalLocalizationUpperEquiv K (m := m) (n := n)).toRingHom :=
  ⟨fun a ha => by
    simpa using ha.map (criticalSchurNormalLocalizationUpperEquiv K (m := m) (n := n)).symm⟩

omit [Fact (1 < m)] [Fact (1 < n)] in
/-- The isomorphism carries the maximal ideal of the localization onto the maximal ideal of the
chosen normal-closure Schur valuation ring. -/
theorem criticalSchurNormalLocalizationUpperEquiv_map_maximalIdeal :
    Ideal.map (criticalSchurNormalLocalizationUpperEquiv K (m := m) (n := n)).toRingHom
        (maximalIdeal
          (CriticalSchurNormalLocalization K (Fact.out : 0 < m) (Fact.out : 0 < n)))
      = maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
          (Fact.out : 0 < n)) := by
  conv_lhs =>
    rw [← IsLocalRing.maximalIdeal_comap
      (criticalSchurNormalLocalizationUpperEquiv K (m := m) (n := n)).toRingHom]
  exact Ideal.map_comap_of_surjective _
    (criticalSchurNormalLocalizationUpperEquiv K (m := m) (n := n)).surjective _

/-- In the localization of the normal integral closure at the Schur prime, the extended maximal
ideal of the observation Schur place is not the whole maximal ideal. -/
theorem criticalSchur_map_maximalIdeal_localization_ne :
    (maximalIdeal
        (CriticalSchurNormalBaseRing K (Fact.out : 0 < m) (Fact.out : 0 < n))).map
        (algebraMap (CriticalSchurNormalBaseRing K (Fact.out : 0 < m) (Fact.out : 0 < n))
          (CriticalSchurNormalLocalization K (Fact.out : 0 < m) (Fact.out : 0 < n)))
      ≠ maximalIdeal
          (CriticalSchurNormalLocalization K (Fact.out : 0 < m) (Fact.out : 0 < n)) := by
  intro h
  refine criticalSchur_normalUpper_map_maximalIdeal_ne (K := K) (m := m) (n := n) ?_
  have key := congrArg (fun I => Ideal.map
    (criticalSchurNormalLocalizationUpperEquiv K (m := m) (n := n)).toRingHom I) h
  rw [Ideal.map_map, criticalSchurNormalLocalizationUpperEquiv_comp,
    criticalSchurNormalLocalizationUpperEquiv_map_maximalIdeal] at key
  exact key

end

end GaloisForLFunctions.HTGeometry
