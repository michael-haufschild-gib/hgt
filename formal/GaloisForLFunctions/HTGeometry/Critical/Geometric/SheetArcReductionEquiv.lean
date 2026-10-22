import GaloisForLFunctions.HTGeometry.Critical.Geometric.DegreeExact

/-!
# Geometric sheets are exactly the pure factors at the common-scale arc

Every actual geometric sheet has a distinct reduction to a pure factorisation at the chosen
normal-closure arc place.  Exactness of the geometric degree and the universal pure-factorisation
upper bound force that reduction to be surjective as well.  Thus the valuative reduction is a
canonical equivalence, rather than only an injection used for a cardinality estimate.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 1000000

private abbrev ArcValuationRing
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :=
  CriticalNormalClosureArcValuationRing K m n hm hn

/-- The pure-factorisation target of normal-closure arc reduction has exactly the critical
multiplicity. -/
theorem natCard_criticalNormalClosureArcPureFactorization_eq
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Nat.card (MonicFactorization
      (pureCriticalCyclicPolynomial
        (K := IsLocalRing.ResidueField (ArcValuationRing K m n hm hn)) (m + n)) m n) =
      criticalHorizonMultiplicity m n := by
  let k := IsLocalRing.ResidueField (ArcValuationRing K m n hm hn)
  letI : Finite (MonicFactorization
      (pureCriticalCyclicPolynomial (K := k) (m + n)) m n) :=
    finite_pureCriticalMonicFactorization k (by omega)
  apply le_antisymm
  · exact natCard_pureCriticalMonicFactorization_le k (m := m) (n := n) (by omega)
  · rw [← natCard_criticalGeometricSheet_eq_criticalHorizonMultiplicity K hm hn]
    exact Nat.card_le_card_of_injective
      (criticalGeometricSheetArcReduction K hm hn)
      (criticalGeometricSheetArcReduction_injective K hm hn)

/-- Every pure factorisation in the residue field of the chosen arc place is the reduction of an
actual geometric sheet. -/
theorem criticalGeometricSheetArcReduction_surjective
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Function.Surjective (criticalGeometricSheetArcReduction K hm hn) := by
  let k := IsLocalRing.ResidueField (ArcValuationRing K m n hm hn)
  letI : Finite (MonicFactorization
      (pureCriticalCyclicPolynomial (K := k) (m + n)) m n) :=
    finite_pureCriticalMonicFactorization k (by omega)
  letI : Finite (criticalGeometricSheet K m n) :=
    Finite.of_injective (criticalGeometricSheetArcReduction K hm hn)
      (criticalGeometricSheetArcReduction_injective K hm hn)
  letI : Fintype (criticalGeometricSheet K m n) := Fintype.ofFinite _
  letI : Fintype (MonicFactorization
      (pureCriticalCyclicPolynomial (K := k) (m + n)) m n) := Fintype.ofFinite _
  exact ((Fintype.bijective_iff_injective_and_card
    (criticalGeometricSheetArcReduction K hm hn)).2
      ⟨criticalGeometricSheetArcReduction_injective K hm hn, by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
          natCard_criticalGeometricSheet_eq_criticalHorizonMultiplicity K hm hn,
          natCard_criticalNormalClosureArcPureFactorization_eq K hm hn]⟩).2

/-- Canonical identification of actual geometric sheets with pure factorisations: the forward map
is literal residue reduction at the chosen normal-closure arc place. -/
noncomputable def criticalGeometricSheetArcReductionEquiv
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalGeometricSheet K m n ≃
      MonicFactorization
        (pureCriticalCyclicPolynomial
          (K := IsLocalRing.ResidueField (ArcValuationRing K m n hm hn)) (m + n)) m n :=
  Equiv.ofBijective (criticalGeometricSheetArcReduction K hm hn)
    ⟨criticalGeometricSheetArcReduction_injective K hm hn,
      criticalGeometricSheetArcReduction_surjective K hm hn⟩

@[simp] theorem criticalGeometricSheetArcReductionEquiv_apply
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (σ : criticalGeometricSheet K m n) :
    criticalGeometricSheetArcReductionEquiv K hm hn σ =
      criticalGeometricSheetArcReduction K hm hn σ :=
  rfl

end

end GaloisForLFunctions.HTGeometry
