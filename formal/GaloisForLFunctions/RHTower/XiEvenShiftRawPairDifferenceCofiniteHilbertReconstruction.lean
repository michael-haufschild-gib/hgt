import GaloisForLFunctions.HTGeometry.CofiniteTailHilbertReconstruction
import GaloisForLFunctions.HTGeometry.PointedCollisionIncidenceLinearBridge
import GaloisForLFunctions.RHTower.XiEvenShiftRawDefectCofiniteHilbertReconstruction
import GaloisForLFunctions.HTGeometry.UpperEndDifferentialInstances

/-!
# Cofinite Hilbert reconstruction of raw Xi pair differences

For an arbitrary finite vertex family, repeated even-shift grades are collapsed and grade zero is
the distinguished loop label.  The resulting pointed collision incidence matroid already
classifies differential independence of raw completed-Xi edge differences.  This module connects
that exact graph law to literal complex-valued functions and Hilbert reconstruction.

A full finite edge family admits deletion-robust distinct sampling nodes, exact dual coefficient
recovery, a positive-definite Gram, and positive Gram determinant exactly when the complete
collision-quotient incidence row family is independent.  Equivalently, it is differentially
independent over both the rational coordinate field and the complete scalar valuation-layer
field.  No root, injective grade, positivity, or independence hypothesis remains in the final
interfaces.
-/

open scoped BigOperators ComplexOrder Differential

namespace RHTower

open Complex Filter
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

open scoped UpperEndDifferentialInstances

/-- Literal upper-end rotation of one actual raw even-shift completed-Xi defect. -/
def xiEvenShiftRawLogDerivDefectRotated (m : ℕ) (z : ℂ) : ℂ :=
  logDeriv xi (-Complex.I * z + (2 * m : ℕ)) - logDeriv xi (-Complex.I * z)

/-- Literal pair difference between two actual raw even translates of `logDeriv xi`. -/
def xiEvenShiftRawPairDifferenceRotatedFamily
    {V E : Type*} (grade : V → ℕ) (tail head : E → V) : E → ℂ → ℂ :=
  fun e z => logDeriv xi (-Complex.I * z + (2 * grade (head e) : ℕ)) -
    logDeriv xi (-Complex.I * z + (2 * grade (tail e) : ℕ))

/-- Subtracting two basepoint defects cancels the common basepoint literally. -/
theorem xiEvenShiftRawPairDifferenceRotatedFamily_eq_vertexDifference
    {V E : Type*} (grade : V → ℕ) (tail head : E → V) :
    xiEvenShiftRawPairDifferenceRotatedFamily grade tail head =
      fun e => xiEvenShiftRawLogDerivDefectRotated (grade (head e)) -
        xiEvenShiftRawLogDerivDefectRotated (grade (tail e)) := by
  funext e z
  simp only [xiEvenShiftRawPairDifferenceRotatedFamily,
    xiEvenShiftRawLogDerivDefectRotated, Pi.sub_apply]
  ring

/-- Exact complex incidence phase of a full finite edge family after collapsing repeated grades
and the zero grade. -/
def XiEvenShiftRawPairIncidenceIndependent
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (grade : V → ℕ) (tail head : E → V) : Prop :=
  (pointedCollisionIncidenceMatroid
    (C := ℂ) grade 0 tail head).Indep Set.univ

/-- Actual raw Xi defects at all occupied nonzero grades are complex-linearly independent as
literal functions.  Repeated vertex labels have already been removed by the support type. -/
theorem linearIndependent_xiEvenShiftRawLogDerivDefectRotated_occupiedGrades
    {V : Type} [Fintype V] (grade : V → ℕ) :
    LinearIndependent ℂ
      (fun q : pointedCollisionIncidenceSupport grade 0 =>
        xiEvenShiftRawLogDerivDefectRotated q) := by
  apply linearIndependent_literal_of_upperEndMero
    (fun q : pointedCollisionIncidenceSupport grade 0 =>
      xiEvenShiftRawLogDerivDefectRotated q)
    (fun q => xiEvenShiftRawLogDerivDefectUpperEndAnalytic q)
  · intro q
    change ((xiEvenShiftRawLogDerivDefectUpperEndAnalytic (q : ℕ) :
        upperEndAnalyticSubring) : Germ upperEndFilter ℂ) =
      xiEvenShiftRawLogDerivDefectUpperEndGerm q
    exact xiEvenShiftRawLogDerivDefectUpperEndCarrier_germ_eq q
  · let support := pointedCollisionIncidenceSupport grade 0
    have hsub : DifferentialIndependent upperEndRationalCoordinateField
        (fun q : ↑(Set.univ : Set support) =>
          xiEvenShiftRawLogDerivDefectUpperEndCarrier (q : support)) := by
      apply (xiEvenShiftRawLogDerivDefectUpperEndCarrier_differentialIndependent_iff
        (fun q : support => (q : ℕ)) Set.univ).2
      constructor
      · intro i _ j _ hij
        exact Subtype.ext hij
      · intro q _
        exact (Finset.mem_erase.mp q.property).1
    have hdiff : DifferentialIndependent upperEndRationalCoordinateField
        (fun q : support => xiEvenShiftRawLogDerivDefectUpperEndCarrier q) :=
      hsub.comp
        (fun q => ⟨q, Set.mem_univ q⟩)
        (fun _ _ hij => congrArg Subtype.val hij)
    have hdiffC : DifferentialIndependent ℂ
        (fun q : support => xiEvenShiftRawLogDerivDefectUpperEndCarrier q) :=
      GaloisForLFunctions.HTGeometry.DifferentialIndependent.restrictScalars hdiff
    have hlinear := hdiffC.algebraicIndependent.linearIndependent
    simpa only [xiEvenShiftRawLogDerivDefectUpperEndCarrier_eq_algebraMap] using hlinear

/-- **Literal raw-Xi edge incidence law.** Linear independence of the complete literal edge
family is exactly independence of the pointed collision incidence matroid. -/
theorem linearIndependent_xiEvenShiftRawPairDifferenceRotatedFamily_iff_incidence
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (grade : V → ℕ) (tail head : E → V) :
    LinearIndependent ℂ
        (xiEvenShiftRawPairDifferenceRotatedFamily grade tail head) ↔
      XiEvenShiftRawPairIncidenceIndependent grade tail head := by
  rw [xiEvenShiftRawPairDifferenceRotatedFamily_eq_vertexDifference]
  exact linearIndependent_gradedPairwiseDifferences_iff_pointedCollisionIncidence
    grade 0 tail head xiEvenShiftRawLogDerivDefectRotated (by
      funext z
      simp [xiEvenShiftRawLogDerivDefectRotated])
    (linearIndependent_xiEvenShiftRawLogDerivDefectRotated_occupiedGrades grade)

/-- Full raw edge differential independence over the rational coordinate field has exactly the
same characteristic-zero incidence phase as literal complex independence. -/
theorem
    xiEvenShiftRawPairDifferenceUpperEndCarrier_full_differentialIndependent_iff_incidence
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (grade : V → ℕ) (tail head : E → V) :
    DifferentialIndependent upperEndRationalCoordinateField
        (xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head) ↔
      XiEvenShiftRawPairIncidenceIndependent grade tail head := by
  constructor
  · intro hdiff
    have hsub := hdiff.comp
      (fun e : (Set.univ : Set E) => e.1) Subtype.val_injective
    have hmat :=
      (xiEvenShiftRawPairDifferenceUpperEndCarrier_differentialIndependent_iff_pointedCollisionIncidence
        grade tail head Set.univ).1 hsub
    rwa [pointedCollisionIncidenceMatroid_charZero_eq
      (C := upperEndRationalCoordinateField) (D := ℂ) grade 0 tail head] at hmat
  · intro hmat
    have hmat' : (pointedCollisionIncidenceMatroid
        (C := upperEndRationalCoordinateField) grade 0 tail head).Indep Set.univ := by
      rwa [pointedCollisionIncidenceMatroid_charZero_eq
        (C := upperEndRationalCoordinateField) (D := ℂ) grade 0 tail head]
    have hsub :=
      (xiEvenShiftRawPairDifferenceUpperEndCarrier_differentialIndependent_iff_pointedCollisionIncidence
        grade tail head Set.univ).2 hmat'
    exact hsub.comp
      (fun e => ⟨e, Set.mem_univ e⟩)
      (fun _ _ hij => congrArg Subtype.val hij)

/-- The full edge packet has the identical incidence classification over the complete scalar
valuation-layer field. -/
theorem
    xiEvenShiftRawPairDifferenceUpperEndCarrier_allValuation_full_differentialIndependent_iff_incidence
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (grade : V → ℕ) (tail head : E → V) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head) ↔
      XiEvenShiftRawPairIncidenceIndependent grade tail head := by
  constructor
  · intro hdiff
    have hsub := hdiff.comp
      (fun e : (Set.univ : Set E) => e.1) Subtype.val_injective
    have hmat :=
      (xiEvenShiftRawPairDifferenceUpperEndCarrier_allValuation_differentialIndependent_iff_pointedCollisionIncidence
        grade tail head Set.univ).1 hsub
    rwa [pointedCollisionIncidenceMatroid_charZero_eq
      (C := analyticScalarValuationLayerDifferentialField) (D := ℂ)
      grade 0 tail head] at hmat
  · intro hmat
    have hmat' : (pointedCollisionIncidenceMatroid
        (C := analyticScalarValuationLayerDifferentialField)
        grade 0 tail head).Indep Set.univ := by
      rwa [pointedCollisionIncidenceMatroid_charZero_eq
        (C := analyticScalarValuationLayerDifferentialField) (D := ℂ)
        grade 0 tail head]
    have hsub :=
      (xiEvenShiftRawPairDifferenceUpperEndCarrier_allValuation_differentialIndependent_iff_pointedCollisionIncidence
        grade tail head Set.univ).2 hmat'
    exact hsub.comp
      (fun e => ⟨e, Set.mem_univ e⟩)
      (fun _ _ hij => congrArg Subtype.val hij)

/-- **Deletion-robust raw-Xi edge law.** Literal edge independence survives every finite deletion
of the complex sampling domain exactly in the pointed incidence phase. -/
theorem tailCoefficientIndependent_xiEvenShiftRawPairDifferenceRotatedFamily_iff_incidence
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (grade : V → ℕ) (tail head : E → V) :
    TailCoefficientIndependent
        (xiEvenShiftRawPairDifferenceRotatedFamily grade tail head) ↔
      XiEvenShiftRawPairIncidenceIndependent grade tail head := by
  constructor
  · intro htail
    exact (linearIndependent_xiEvenShiftRawPairDifferenceRotatedFamily_iff_incidence
      grade tail head).1
        (htail.linearIndependent
          (xiEvenShiftRawPairDifferenceRotatedFamily grade tail head))
  · intro hincidence
    apply tailCoefficientIndependent_literal_of_upperEndMero
      (xiEvenShiftRawPairDifferenceRotatedFamily grade tail head)
      (xiEvenShiftRawPairDifferenceUpperEndAnalytic grade tail head)
    · intro e
      change ((xiEvenShiftRawPairDifferenceUpperEndAnalytic grade tail head e :
          upperEndAnalyticSubring) : Germ upperEndFilter ℂ) =
        xiEvenShiftRawPairDifferenceUpperEndGerm grade tail head e
      exact xiEvenShiftRawPairDifferenceUpperEndCarrier_germ_eq grade tail head e
    · have hdiff : DifferentialIndependent upperEndRationalCoordinateField
          (xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head) :=
        (xiEvenShiftRawPairDifferenceUpperEndCarrier_full_differentialIndependent_iff_incidence
          grade tail head).2 hincidence
      have hdiffC : DifferentialIndependent ℂ
          (xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head) :=
        GaloisForLFunctions.HTGeometry.DifferentialIndependent.restrictScalars hdiff
      have hlinear := hdiffC.algebraicIndependent.linearIndependent
      have hfamily :
          (fun e => algebraMap upperEndAnalyticSubring upperEndMeroField
            (xiEvenShiftRawPairDifferenceUpperEndAnalytic grade tail head e)) =
            xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head := by
        funext e
        exact (xiEvenShiftRawPairDifferenceUpperEndCarrier_eq_algebraMap
          grade tail head e).symm
      rw [hfamily]
      exact hlinear

/-- Strict square evaluation Grams survive every finite complex deletion exactly in the
collision-quotient incidence phase. -/
theorem xiEvenShiftRawPairDifferenceCofiniteEvaluationGram_posDef_iff_incidence
    {V : Type} [Fintype V] {d : ℕ}
    (grade : V → ℕ) (tail head : Fin d → V) :
    (∀ F : Set ℂ, F.Finite →
      ∃ points : Fin d → {z : ℂ // z ∉ F},
        (cofiniteEvaluationGram
          (xiEvenShiftRawPairDifferenceRotatedFamily grade tail head) F points).PosDef) ↔
      XiEvenShiftRawPairIncidenceIndependent grade tail head := by
  calc
    _ ↔ TailCoefficientIndependent
        (xiEvenShiftRawPairDifferenceRotatedFamily grade tail head) :=
      (tailCoefficientIndependent_iff_cofinite_posDef_evaluationGram
        (xiEvenShiftRawPairDifferenceRotatedFamily grade tail head)).symm
    _ ↔ _ :=
      tailCoefficientIndependent_xiEvenShiftRawPairDifferenceRotatedFamily_iff_incidence
        grade tail head

/-- In the incidence phase, every finite deletion leaves distinct nodes with exact dual edge
coefficient recovery, positive-definite Gram, and positive volume. -/
theorem exists_injective_xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction
    {V : Type} [Fintype V] {d : ℕ}
    (grade : V → ℕ) (tail head : Fin d → V)
    (hincidence : XiEvenShiftRawPairIncidenceIndependent grade tail head)
    (F : Set ℂ) (hF : F.Finite) :
    ∃ (points : Fin d → {z : ℂ // z ∉ F}) (dual : Fin d → Fin d → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
        xiEvenShiftRawPairDifferenceRotatedFamily grade tail head r (points i) =
          if q = r then 1 else 0) ∧
      (∀ (a : Fin d → ℂ) q,
        ∑ i, dual q i *
          (∑ r, a r *
            xiEvenShiftRawPairDifferenceRotatedFamily grade tail head r (points i)) = a q) ∧
      (cofiniteEvaluationGram
        (xiEvenShiftRawPairDifferenceRotatedFamily grade tail head) F points).PosDef ∧
      0 < (cofiniteEvaluationGram
        (xiEvenShiftRawPairDifferenceRotatedFamily grade tail head) F points).det := by
  exact
    exists_injective_cofiniteEvaluationHilbertReconstruction_of_tailCoefficientIndependent
      (xiEvenShiftRawPairDifferenceRotatedFamily grade tail head)
      ((tailCoefficientIndependent_xiEvenShiftRawPairDifferenceRotatedFamily_iff_incidence
        grade tail head).2 hincidence) F hF

/-- Complete cofinite Hilbert reconstruction phase of a finite raw Xi edge family. -/
def XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction
    {V : Type} [Fintype V] {d : ℕ}
    (grade : V → ℕ) (tail head : Fin d → V) : Prop :=
  CofiniteEvaluationHilbertReconstruction
    (xiEvenShiftRawPairDifferenceRotatedFamily grade tail head)

/-- **Unconditional raw-Xi edge reconstruction classification.** Complete cofinite Hilbert
recovery is exactly pointed collision incidence independence. -/
theorem xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_incidence
    {V : Type} [Fintype V] {d : ℕ}
    (grade : V → ℕ) (tail head : Fin d → V) :
    XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction grade tail head ↔
      XiEvenShiftRawPairIncidenceIndependent grade tail head := by
  calc
    _ ↔ TailCoefficientIndependent
        (xiEvenShiftRawPairDifferenceRotatedFamily grade tail head) :=
      cofiniteEvaluationHilbertReconstruction_iff_tailCoefficientIndependent
        (xiEvenShiftRawPairDifferenceRotatedFamily grade tail head)
    _ ↔ _ :=
      tailCoefficientIndependent_xiEvenShiftRawPairDifferenceRotatedFamily_iff_incidence
        grade tail head

/-- Literal cofinite recovery is equivalent to rational-coordinate differential independence of
the complete raw edge carrier family. -/
theorem
    xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_differentialIndependent
    {V : Type} [Fintype V] {d : ℕ}
    (grade : V → ℕ) (tail head : Fin d → V) :
    XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction grade tail head ↔
      DifferentialIndependent upperEndRationalCoordinateField
        (xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head) := by
  rw [xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_incidence,
    xiEvenShiftRawPairDifferenceUpperEndCarrier_full_differentialIndependent_iff_incidence]

/-- Literal cofinite recovery also detects differential independence after every scalar valuation
layer has been adjoined. -/
theorem
    xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_allValuation_differentialIndependent
    {V : Type} [Fintype V] {d : ℕ}
    (grade : V → ℕ) (tail head : Fin d → V) :
    XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction grade tail head ↔
      DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head) := by
  rw [xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_incidence,
    xiEvenShiftRawPairDifferenceUpperEndCarrier_allValuation_full_differentialIndependent_iff_incidence]

/-- **Universal raw-Xi edge Hilbert phase law.** One graph condition simultaneously controls
literal reconstruction and differential independence over both coefficient fields. -/
theorem xiEvenShiftRawPairDifferenceCofiniteHilbertPhase_iff
    {V : Type} [Fintype V] {d : ℕ}
    (grade : V → ℕ) (tail head : Fin d → V) :
    XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction grade tail head ↔
      XiEvenShiftRawPairIncidenceIndependent grade tail head ∧
        DifferentialIndependent upperEndRationalCoordinateField
          (xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head) ∧
        DifferentialIndependent analyticScalarValuationLayerDifferentialField
          (xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head) := by
  constructor
  · intro hrec
    exact ⟨
      (xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_incidence
        grade tail head).1 hrec,
      (xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_differentialIndependent
        grade tail head).1 hrec,
      (xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_allValuation_differentialIndependent
        grade tail head).1 hrec⟩
  · rintro ⟨hincidence, _hrational, _hallValuation⟩
    exact (xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_incidence
      grade tail head).2 hincidence

end

end RHTower
