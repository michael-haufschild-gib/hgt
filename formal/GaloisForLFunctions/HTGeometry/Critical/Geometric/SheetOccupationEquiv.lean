import GaloisForLFunctions.HTGeometry.Critical.Geometric.SheetArcReductionEquiv
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import GaloisForLFunctions.HTGeometry.OccupationFactorInjective

/-!
# Canonical occupation labels for actual geometric sheets

The ground field is algebraically closed, so it already contains every root of the pure cyclic
polynomial.  Mapping the canonical root enumeration into the residue field of the chosen
normal-closure arc place turns every occupation state into a pure monic factorisation there.

The occupation map is injective by distinctness of the roots.  The exact pure-factorisation count
from `CriticalGeometricSheetArcReductionEquiv` makes it surjective.  Composing its inverse with
literal arc reduction gives a canonical equivalence from actual geometric sheets to occupation
states; no arbitrary finite-set enumeration is used.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

set_option synthInstance.maxHeartbeats 1000000

private abbrev ArcValuationRing
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :=
  CriticalNormalClosureArcValuationRing K m n hm hn

/-- Canonical roots of the pure cyclic polynomial, mapped from the algebraically closed ground
field into the residue field of the chosen normal-closure arc place. -/
noncomputable def criticalNormalClosureArcPureRoot
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Fin (m + n) → IsLocalRing.ResidueField (ArcValuationRing K m n hm hn) :=
  fun i => criticalNormalClosureArcConstantResidueMap K hm hn
    (pureCriticalRootLabeling (K := K) (by omega) i)

theorem criticalNormalClosureArcPureRoot_injective
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Function.Injective (criticalNormalClosureArcPureRoot K hm hn) :=
  (criticalNormalClosureArcConstantResidueMap K hm hn).injective.comp
    (pureCriticalRootLabeling_injective (K := K) (by omega))

/-- Selected and complementary root factors over the arc residue field multiply to the pure cyclic
polynomial. -/
theorem criticalNormalClosureArcPureRoot_factors_mul
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (S : criticalHorizonOccupationStates m n) :
    criticalHorizonLeftFactorFromRoots (criticalNormalClosureArcPureRoot K hm hn) S *
      criticalHorizonRightFactorFromRoots (criticalNormalClosureArcPureRoot K hm hn) S =
      pureCriticalCyclicPolynomial
        (K := IsLocalRing.ResidueField (ArcValuationRing K m n hm hn)) (m + n) := by
  let φ := criticalNormalClosureArcConstantResidueMap K hm hn
  have h := congrArg (Polynomial.map φ)
    (pureCriticalRootFactors_mul (K := K) (by omega) S)
  simpa only [criticalNormalClosureArcPureRoot, criticalHorizonLeftFactorFromRoots,
    criticalHorizonRightFactorFromRoots, Polynomial.map_mul, Polynomial.map_prod,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    pureCriticalCyclicPolynomial, Polynomial.map_add, Polynomial.map_one,
    Polynomial.map_pow] using h

/-- The pure factorisation attached to an occupation state, over the residue field of the chosen
normal-closure arc place. -/
noncomputable def criticalNormalClosureArcOccupationFactorization
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalHorizonOccupationStates m n →
      MonicFactorization
        (pureCriticalCyclicPolynomial
          (K := IsLocalRing.ResidueField (ArcValuationRing K m n hm hn)) (m + n)) m n := by
  intro S
  let root := criticalNormalClosureArcPureRoot K hm hn
  let A := criticalHorizonLeftFactorFromRoots root S
  let B := criticalHorizonRightFactorFromRoots root S
  exact ⟨(Polynomial.MonicDegreeEq.mk A
      (monic_criticalHorizonLeftFactorFromRoots root S)
      (natDegree_criticalHorizonLeftFactorFromRoots root S),
    Polynomial.MonicDegreeEq.mk B
      (monic_criticalHorizonRightFactorFromRoots root S)
      (natDegree_criticalHorizonRightFactorFromRoots root S)),
    criticalNormalClosureArcPureRoot_factors_mul K hm hn S⟩

theorem criticalNormalClosureArcOccupationFactorization_injective
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Function.Injective (criticalNormalClosureArcOccupationFactorization K hm hn) := by
  intro S T hST
  apply criticalHorizonLeftFactorFromRoots_injective
    (criticalNormalClosureArcPureRoot_injective K hm hn)
  exact congrArg (fun q => (q.1.1 :
    (IsLocalRing.ResidueField (ArcValuationRing K m n hm hn))[X])) hST

theorem criticalNormalClosureArcOccupationFactorization_surjective
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Function.Surjective (criticalNormalClosureArcOccupationFactorization K hm hn) := by
  let k := IsLocalRing.ResidueField (ArcValuationRing K m n hm hn)
  letI : Finite (MonicFactorization
      (pureCriticalCyclicPolynomial (K := k) (m + n)) m n) :=
    finite_pureCriticalMonicFactorization k (by omega)
  letI : Fintype (MonicFactorization
      (pureCriticalCyclicPolynomial (K := k) (m + n)) m n) := Fintype.ofFinite _
  exact ((Fintype.bijective_iff_injective_and_card
    (criticalNormalClosureArcOccupationFactorization K hm hn)).2
      ⟨criticalNormalClosureArcOccupationFactorization_injective K hm hn, by
        rw [card_criticalHorizonOccupationStates, ← Nat.card_eq_fintype_card,
          natCard_criticalNormalClosureArcPureFactorization_eq K hm hn]⟩).2

/-- Occupation states are exactly the pure factorisations in the residue field of the chosen arc
place, through the canonical ground-field root enumeration. -/
noncomputable def criticalNormalClosureArcOccupationFactorizationEquiv
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalHorizonOccupationStates m n ≃
      MonicFactorization
        (pureCriticalCyclicPolynomial
          (K := IsLocalRing.ResidueField (ArcValuationRing K m n hm hn)) (m + n)) m n :=
  Equiv.ofBijective (criticalNormalClosureArcOccupationFactorization K hm hn)
    ⟨criticalNormalClosureArcOccupationFactorization_injective K hm hn,
      criticalNormalClosureArcOccupationFactorization_surjective K hm hn⟩

@[simp] theorem criticalNormalClosureArcOccupationFactorizationEquiv_apply
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (S : criticalHorizonOccupationStates m n) :
    criticalNormalClosureArcOccupationFactorizationEquiv K hm hn S =
      criticalNormalClosureArcOccupationFactorization K hm hn S :=
  rfl

/-- Canonical occupation label of an actual geometric sheet.  It is defined by reducing the sheet
at the normal-closure arc place and reading the resulting factors against the canonical roots. -/
noncomputable def criticalGeometricSheetOccupationEquiv
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalGeometricSheet K m n ≃ criticalHorizonOccupationStates m n :=
  (criticalGeometricSheetArcReductionEquiv K hm hn).trans
    (criticalNormalClosureArcOccupationFactorizationEquiv K hm hn).symm

theorem criticalNormalClosureArcOccupationFactorization_label
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (σ : criticalGeometricSheet K m n) :
    criticalNormalClosureArcOccupationFactorization K hm hn
        (criticalGeometricSheetOccupationEquiv K hm hn σ) =
      criticalGeometricSheetArcReduction K hm hn σ := by
  exact (criticalNormalClosureArcOccupationFactorizationEquiv K hm hn).apply_symm_apply
    (criticalGeometricSheetArcReductionEquiv K hm hn σ)

end

end GaloisForLFunctions.HTGeometry
