import GaloisForLFunctions.HTGeometry.FiniteQuotientPrimeDifferentialDuality
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Oligomorphic prime differential spectrum

Apply finite-quotient prime differential duality to the orbit relations of a group on every finite
tuple power.  At each arity the quotient indicators give an exact differential basis whose rank is
the orbit count.  Across all arities, equality of the embedded field spectrum is equivalent to
equality of every finite-tuple orbit relation.
-/

namespace GaloisForLFunctions.HTGeometry

open Set
open scoped Differential

noncomputable section

universe u v

variable {G H : Type u} {X : Type v}
  [Group G] [Group H] [MulAction G X] [MulAction H X]

abbrev TupleOrbitSetoid (G : Type u) (X : Type v)
    [Group G] [MulAction G X] (n : ℕ) : Setoid (Fin n → X) :=
  MulAction.orbitRel G (Fin n → X)

abbrev OligomorphicTupleRank (G : Type u) (X : Type v)
    [Group G] [MulAction G X] (n : ℕ)
    [Fintype (Quotient (TupleOrbitSetoid G X n))] : ℕ :=
  FiniteQuotientRank (TupleOrbitSetoid G X n)

def universalTupleOrbitShiftField
    (G : Type u) (X : Type v) [Group G] [MulAction G X]
    [Nonempty X] [Countable X] (n : ℕ) (a : ℂ) :
    IntermediateField finitePrimeRationalCoefficientField
      arithmeticFunctionRationalCoordinateField :=
  universalPrimeFiniteQuotientShiftField (Fin n → X)
    (TupleOrbitSetoid G X n) a

theorem universalTupleOrbitCarrier_differentialIndependent
    [Nonempty X] [Countable X] [TopologicalSpace X] [DiscreteTopology X]
    (n : ℕ) [Fintype (Quotient (TupleOrbitSetoid G X n))] (a : ℂ) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
      (fun j : Fin (OligomorphicTupleRank G X n) ↦
        tailDenseObservableShiftCarrier
          (universalCountablePrimeProfile (Fin n → X))
          (finiteClassDeltaObservable (TupleOrbitSetoid G X n) j) a) := by
  exact universalPrimeFiniteQuotientCarrier_differentialIndependent
    (TupleOrbitSetoid G X n) a

theorem universalTupleOrbitField_le_iff_reverseOrbitRelation
    [Nonempty X] [Countable X] [TopologicalSpace X] [DiscreteTopology X]
    (n : ℕ)
    [Fintype (Quotient (TupleOrbitSetoid G X n))]
    [Fintype (Quotient (TupleOrbitSetoid H X n))] (a : ℂ) :
    universalTupleOrbitShiftField G X n a ≤
        universalTupleOrbitShiftField H X n a ↔
      TupleOrbitSetoid H X n ≤ TupleOrbitSetoid G X n := by
  exact universalPrimeFiniteQuotientField_le_iff_reverseSetoid
    (TupleOrbitSetoid G X n) (TupleOrbitSetoid H X n) a

/-- The complete arity-indexed differential-field spectrum remembers every finite-tuple orbit
relation.  For closed permutation groups, the classical orbit-reconstruction theorem therefore
recovers the group from this spectrum. -/
theorem universalTupleOrbitField_spectrum_eq_iff_orbitSetoid_spectrum_eq
    [Nonempty X] [Countable X] [TopologicalSpace X] [DiscreteTopology X]
    (hG : ∀ n, Fintype (Quotient (TupleOrbitSetoid G X n)))
    (hH : ∀ n, Fintype (Quotient (TupleOrbitSetoid H X n)))
    (a : ℂ) :
    (∀ n, universalTupleOrbitShiftField G X n a =
        universalTupleOrbitShiftField H X n a) ↔
      ∀ n, TupleOrbitSetoid G X n = TupleOrbitSetoid H X n := by
  constructor
  · intro hfield n
    letI : Fintype (Quotient (TupleOrbitSetoid G X n)) := hG n
    letI : Fintype (Quotient (TupleOrbitSetoid H X n)) := hH n
    exact (universalPrimeFiniteQuotientField_eq_iff_setoid_eq
      (TupleOrbitSetoid G X n) (TupleOrbitSetoid H X n) a).mp (hfield n)
  · intro hrel n
    unfold universalTupleOrbitShiftField
    rw [hrel n]

end

end GaloisForLFunctions.HTGeometry
