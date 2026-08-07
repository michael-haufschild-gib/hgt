import GaloisForLFunctions.HTGeometry.CriticalNormalClosureArcReduction

/-!
# Characteristic of the common-scale normal-closure residue field

Constants from the algebraically closed characteristic-zero ground field have valuation at most
one on the common-scale arc.  Their composite map into the chosen normal-closure residue field is
a field embedding, proving that residue field also has characteristic zero.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped LaurentSeries

noncomputable section

private abbrev ArcBaseRing
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :=
  CriticalNormalClosureArcBaseRing K m n hm hn

private abbrev ArcIntegralClosure
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :=
  CriticalNormalClosureArcIntegralClosure K m n hm hn

private abbrev ArcValuationRing
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :=
  CriticalNormalClosureArcValuationRing K m n hm hn

theorem criticalObservationArc_algebraMap_mem
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (x : K) :
    algebraMap K (criticalObservationField K m n) x ∈
      ArcBaseRing K m n hm hn := by
  rw [Valuation.mem_valuationSubring_iff, criticalObservationArcValuation,
    Valuation.comap_apply]
  change Valued.v (criticalObservationArcEmbedding K hm hn
    (algebraMap K (criticalObservationField K m n) x)) ≤ 1
  rw [(criticalObservationArcEmbedding K hm hn).commutes x]
  apply (LaurentSeries.val_le_one_iff_eq_coe (CriticalArcConstants K m n) _).2
  refine ⟨PowerSeries.C (algebraMap K (CriticalArcConstants K m n) x), ?_⟩
  rw [HahnSeries.algebraMap_apply' ℤ]
  rw [PowerSeries.algebraMap_apply]

/-- Ground-field constants as elements of the base common-scale DVR. -/
noncomputable def criticalObservationArcConstantBaseMap
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    K →+* ArcBaseRing K m n hm hn :=
  RingHom.codRestrict (algebraMap K (criticalObservationField K m n))
    (ArcBaseRing K m n hm hn)
    (criticalObservationArc_algebraMap_mem K hm hn)

/-- Composite embedding of ground-field constants into the residue field of the chosen normal-
closure place. -/
noncomputable def criticalNormalClosureArcConstantResidueMap
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    K →+* IsLocalRing.ResidueField (ArcValuationRing K m n hm hn) :=
  (IsLocalRing.residue (ArcValuationRing K m n hm hn)).comp
    ((algebraMap (ArcIntegralClosure K m n hm hn)
      (ArcValuationRing K m n hm hn)).comp
      ((algebraMap (ArcBaseRing K m n hm hn)
        (ArcIntegralClosure K m n hm hn)).comp
        (criticalObservationArcConstantBaseMap K hm hn)))

noncomputable instance criticalNormalClosureArcResidue_charZero
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    CharZero (IsLocalRing.ResidueField (ArcValuationRing K m n hm hn)) :=
  (RingHom.charZero_iff
    (criticalNormalClosureArcConstantResidueMap K hm hn).injective).mp inferInstance

end


end GaloisForLFunctions.HTGeometry
