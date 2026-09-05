import GaloisForLFunctions.HTGeometry.RankOneCenteredObservationCoordinates
import GaloisForLFunctions.HTGeometry.CriticalReciprocalSourceCoordinates

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

set_option synthInstance.maxHeartbeats 200000

variable {K : Type*} [Field K] [CharZero K] {m : ℕ}

noncomputable def coRankOneObservationIndexEquiv :
    Fin 1 ⊕ Fin m ≃ Fin m ⊕ Unit :=
  (Equiv.sumComm (Fin 1) (Fin m)).trans
    (Equiv.sumCongr (Equiv.refl _) (Equiv.ofUnique _ _))

noncomputable def coRankOneObservationRationalReindexEquiv :
    FractionRing (MvPolynomial (Fin 1 ⊕ Fin m) K) ≃ₐ[K]
      FractionRing (MvPolynomial (Fin m ⊕ Unit) K) :=
  IsFractionRing.fieldEquivOfAlgEquiv K
    (FractionRing (MvPolynomial (Fin 1 ⊕ Fin m) K))
    (FractionRing (MvPolynomial (Fin m ⊕ Unit) K))
    (MvPolynomial.renameEquiv K (coRankOneObservationIndexEquiv (m := m)))

@[simp] theorem coRankOneObservationRationalReindexEquiv_X (i : Fin 1 ⊕ Fin m) :
    coRankOneObservationRationalReindexEquiv (K := K) (m := m)
        (algebraMap (MvPolynomial (Fin 1 ⊕ Fin m) K)
          (FractionRing (MvPolynomial (Fin 1 ⊕ Fin m) K)) (MvPolynomial.X i)) =
      algebraMap (MvPolynomial (Fin m ⊕ Unit) K)
        (FractionRing (MvPolynomial (Fin m ⊕ Unit) K))
        (MvPolynomial.X (coRankOneObservationIndexEquiv (m := m) i)) := by
  change (IsFractionRing.ringEquivOfRingEquiv
      (MvPolynomial.renameEquiv K (coRankOneObservationIndexEquiv (m := m))).toRingEquiv)
      (algebraMap (MvPolynomial (Fin 1 ⊕ Fin m) K)
        (FractionRing (MvPolynomial (Fin 1 ⊕ Fin m) K)) (MvPolynomial.X i)) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp

noncomputable def coRankOneCriticalObservationFieldEquiv
    [IsAlgClosed K] (hm : 0 < m) :
    criticalObservationField K m 1 ≃ₐ[K] TailRatFree K m :=
  (criticalObservationFieldEquiv K (m := m) (n := 1) hm (by omega)).symm |>.trans
    (coRankOneObservationRationalReindexEquiv (K := K) (m := m)) |>.trans
    (iteratedRationalFieldEquiv (K := K) (n := m))

@[simp] theorem coRankOneCriticalObservationFieldEquiv_recip
    [IsAlgClosed K] (hm : 0 < m) (j : Fin m) :
    coRankOneCriticalObservationFieldEquiv (K := K) hm
        (criticalObservationRecip K m 1 j) =
      iteratedRationalFamily (K := K) (n := m) (Sum.inl j) := by
  have hcrit :
      (criticalObservationFieldEquiv K (m := m) (n := 1) hm (by omega)).symm
          (criticalObservationRecip K m 1 j) =
        algebraMap (MvPolynomial (Fin 1 ⊕ Fin m) K)
          (FractionRing (MvPolynomial (Fin 1 ⊕ Fin m) K))
          (MvPolynomial.X (Sum.inr j)) := by
    apply (criticalObservationFieldEquiv K (m := m) (n := 1) hm (by omega)).injective
    simp only [AlgEquiv.apply_symm_apply]
    apply Subtype.ext
    simp [criticalObservationFieldEquiv, criticalObservationRecip,
      criticalFieldObservation]
  rw [coRankOneCriticalObservationFieldEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    hcrit, coRankOneObservationRationalReindexEquiv_X, iteratedRationalFieldEquiv_X]
  rfl

@[simp] theorem coRankOneCriticalObservationFieldEquiv_raw
    [IsAlgClosed K] (hm : 0 < m) (i : Fin 1) :
    coRankOneCriticalObservationFieldEquiv (K := K) hm
        (criticalObservationRaw K m 1 i) =
      iteratedRationalFamily (K := K) (n := m) (Sum.inr Unit.unit) := by
  have hcrit :
      (criticalObservationFieldEquiv K (m := m) (n := 1) hm (by omega)).symm
          (criticalObservationRaw K m 1 i) =
        algebraMap (MvPolynomial (Fin 1 ⊕ Fin m) K)
          (FractionRing (MvPolynomial (Fin 1 ⊕ Fin m) K))
          (MvPolynomial.X (Sum.inl i)) := by
    apply (criticalObservationFieldEquiv K (m := m) (n := 1) hm (by omega)).injective
    simp only [AlgEquiv.apply_symm_apply]
    apply Subtype.ext
    simp [criticalObservationFieldEquiv, criticalObservationRaw,
      criticalFieldObservation]
  rw [coRankOneCriticalObservationFieldEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    hcrit, coRankOneObservationRationalReindexEquiv_X, iteratedRationalFieldEquiv_X]
  congr 2

theorem coRankOneCriticalObservationFieldEquiv_aeval_recip
    [IsAlgClosed K] (hm : 0 < m) (P : MvPolynomial (Fin m) K) :
    coRankOneCriticalObservationFieldEquiv (K := K) hm
        (MvPolynomial.aeval (criticalObservationRecip K m 1) P) =
      algebraMap (TailRat K m) (TailRatFree K m)
        (algebraMap (MvPolynomial (Fin m) K) (TailRat K m) P) := by
  let e := coRankOneCriticalObservationFieldEquiv (K := K) hm
  let lhs : MvPolynomial (Fin m) K →ₐ[K] TailRatFree K m :=
    e.toAlgHom.comp (MvPolynomial.aeval (criticalObservationRecip K m 1))
  let rhs : MvPolynomial (Fin m) K →ₐ[K] TailRatFree K m :=
    (IsScalarTower.toAlgHom K (TailRat K m) (TailRatFree K m)).comp
      (IsScalarTower.toAlgHom K (MvPolynomial (Fin m) K) (TailRat K m))
  have hhom : lhs = rhs := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [lhs, rhs, e]
  exact DFunLike.congr_fun hhom P

noncomputable def coRankOneCriticalCenteredCoeff
    [IsAlgClosed K] (hm : 0 < m) (j : Fin m) :
    criticalObservationField K m 1 :=
  MvPolynomial.aeval (criticalObservationRecip K m 1) (tailCoeff K m j) /
    criticalObservationRaw K m 1 (0 : Fin 1)

noncomputable def coRankOneCriticalObservationToCenteredCoeffFreeEquiv
    [IsAlgClosed K] (hm : 0 < m) :
    criticalObservationField K m 1 ≃ₐ[K]
      FractionRing (Polynomial (centeredCoeffField K m.succ)) :=
  (coRankOneCriticalObservationFieldEquiv (K := K) hm).trans
    (rankOneRawToCenteredCoeffFreeEquiv (K := K) hm)

@[simp] theorem coRankOneCriticalObservationToCenteredCoeffFreeEquiv_centered
    [IsAlgClosed K] (hm : 0 < m) (j : Fin m) :
    coRankOneCriticalObservationToCenteredCoeffFreeEquiv (K := K) hm
        (coRankOneCriticalCenteredCoeff (K := K) hm j) =
      algebraMap (Polynomial (centeredCoeffField K m.succ))
        (FractionRing (Polynomial (centeredCoeffField K m.succ)))
        (Polynomial.C (centeredCoeffIn K m.succ (rankOneCenteredIndex j))) := by
  have hmap :
      coRankOneCriticalObservationFieldEquiv (K := K) hm
          (coRankOneCriticalCenteredCoeff (K := K) hm j) =
        algebraMap (TailRat K m) (TailRatFree K m) (tailCoeffIn K m j) /
          fracX (TailRat K m) := by
    rw [coRankOneCriticalCenteredCoeff]
    calc
      coRankOneCriticalObservationFieldEquiv (K := K) hm
          (MvPolynomial.aeval (criticalObservationRecip K m 1) (tailCoeff K m j) /
            criticalObservationRaw K m 1 (0 : Fin 1)) =
          coRankOneCriticalObservationFieldEquiv (K := K) hm
              (MvPolynomial.aeval (criticalObservationRecip K m 1) (tailCoeff K m j)) /
            coRankOneCriticalObservationFieldEquiv (K := K) hm
              (criticalObservationRaw K m 1 (0 : Fin 1)) :=
        map_div₀ _ _ _
      _ = _ := by
        rw [coRankOneCriticalObservationFieldEquiv_aeval_recip,
          coRankOneCriticalObservationFieldEquiv_raw, iteratedRationalFamily_inr]
        rfl
  rw [coRankOneCriticalObservationToCenteredCoeffFreeEquiv, AlgEquiv.trans_apply, hmap]
  exact rankOneRawToCenteredCoeffFreeEquiv_centered (K := K) hm j

@[simp] theorem coRankOneCriticalObservationToCenteredCoeffFreeEquiv_free
    [IsAlgClosed K] (hm : 0 < m) :
    coRankOneCriticalObservationToCenteredCoeffFreeEquiv (K := K) hm
        (criticalObservationRecip K m 1 (⟨0, hm⟩ : Fin m)) =
      fracX (centeredCoeffField K m.succ) := by
  rw [coRankOneCriticalObservationToCenteredCoeffFreeEquiv, AlgEquiv.trans_apply,
    coRankOneCriticalObservationFieldEquiv_recip, iteratedRationalFamily_inl]
  exact rankOneRawToCenteredCoeffFreeEquiv_free (K := K) hm

end
end GaloisForLFunctions.HTGeometry
