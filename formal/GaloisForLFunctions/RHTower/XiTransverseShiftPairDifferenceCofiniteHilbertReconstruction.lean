import GaloisForLFunctions.HTGeometry.CofiniteTailHilbertReconstruction
import GaloisForLFunctions.HTGeometry.PointedCollisionIncidenceLinearBridge
import GaloisForLFunctions.RHTower.XiTransverseShiftDefectCofiniteHilbertReconstruction
import GaloisForLFunctions.RHTower.XiTransverseShiftCollisionIncidenceRank
import GaloisForLFunctions.RHTower.XiTransverseShiftCollisionIncidenceAllValuationRank
import GaloisForLFunctions.RHTower.XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction
import GaloisForLFunctions.HTGeometry.UpperEndDifferentialInstances

/-!
# Cofinite Hilbert reconstruction of corrected Xi pair differences

Arbitrary integral corrected completed-Xi shift defects admit an exact graph-level literal
reconstruction law. Repeated shifts are collapsed and shift zero is the distinguished loop label.
The full edge family has deletion-robust sampling, exact dual recovery, positive-definite Gram,
and positive Gram determinant exactly when the resulting pointed collision incidence rows are
independent. The same condition classifies differential independence over both the rational
coordinate field and the complete scalar valuation-layer field.

Injective label reparametrization then identifies this phase, after doubling every label, with the
raw even-shift pair-difference phase. Thus the archimedean correction changes the literal edge
functions but not their complete Hilbert/differential reconstruction phase. No injectivity,
nonzero-label, graph, tail-independence, or reconstruction hypothesis remains in the interfaces.
-/

open scoped BigOperators ComplexOrder Differential

namespace RHTower

open Complex Filter
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

open scoped UpperEndDifferentialInstances

/-- Literal upper-end rotation of one actual corrected completed-Xi shift defect. -/
def xiTransverseShiftPrimeDefectRotated (m : ℕ) (z : ℂ) : ℂ :=
  xiTransverseShiftPrimeDefect m (-Complex.I * z)

/-- Literal oriented pair difference of actual corrected completed-Xi shift defects. -/
def xiTransverseShiftPairDifferenceRotatedFamily
    {V E : Type*} (shift : V → ℕ) (tail head : E → V) : E → ℂ → ℂ :=
  fun e z => xiTransverseShiftPrimeDefect (shift (head e)) (-Complex.I * z) -
    xiTransverseShiftPrimeDefect (shift (tail e)) (-Complex.I * z)

/-- The literal corrected edge family is the pairwise-difference family of its vertex defects. -/
theorem xiTransverseShiftPairDifferenceRotatedFamily_eq_vertexDifference
    {V E : Type*} (shift : V → ℕ) (tail head : E → V) :
    xiTransverseShiftPairDifferenceRotatedFamily shift tail head =
      fun e => xiTransverseShiftPrimeDefectRotated (shift (head e)) -
        xiTransverseShiftPrimeDefectRotated (shift (tail e)) := by
  rfl

/-- Exact complex incidence phase after repeated shifts and shift zero are collapsed. -/
def XiTransverseShiftPairIncidenceIndependent
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (shift : V → ℕ) (tail head : E → V) : Prop :=
  (pointedCollisionIncidenceMatroid
    (C := ℂ) shift 0 tail head).Indep Set.univ

/-- Actual corrected Xi defects at all occupied nonzero shifts are complex-linearly independent
as literal functions. Repeated vertex labels have already been removed by the support type. -/
theorem linearIndependent_xiTransverseShiftPrimeDefectRotated_occupiedShifts
    {V : Type} [Fintype V] (shift : V → ℕ) :
    LinearIndependent ℂ
      (fun q : pointedCollisionIncidenceSupport shift 0 =>
        xiTransverseShiftPrimeDefectRotated q) := by
  apply linearIndependent_literal_of_upperEndMero
    (fun q : pointedCollisionIncidenceSupport shift 0 =>
      xiTransverseShiftPrimeDefectRotated q)
    (fun q => finiteAbscissaLSeriesToUpperEndAnalytic
      (xiTransverseShiftFiniteAbscissaSource q))
  · intro q
    change finiteAbscissaLSeriesToUpperEndGerm
        (xiTransverseShiftFiniteAbscissaSource (q : ℕ)) =
      xiTransverseShiftPrimeDefectUpperEndGerm q
    exact xiTransverseShiftUpperEndGerm_eq_xiTransverseShiftPrimeDefect q
  · have hdiff :=
      xiTransverseShiftUpperEndCarrier_pointedCollisionSupport_differentialIndependent shift
    have hdiffC : DifferentialIndependent ℂ
        (fun q : pointedCollisionIncidenceSupport shift 0 =>
          xiTransverseShiftUpperEndCarrier q) :=
      GaloisForLFunctions.HTGeometry.DifferentialIndependent.restrictScalars hdiff
    have hlinear := hdiffC.algebraicIndependent.linearIndependent
    simpa [xiTransverseShiftUpperEndCarrier,
      finiteAbscissaLSeriesToUpperEndMero_eq_algebraMap] using hlinear

/-- **Literal corrected-Xi edge incidence law.** Linear independence of the complete literal
edge family is exactly pointed collision incidence independence. -/
theorem linearIndependent_xiTransverseShiftPairDifferenceRotatedFamily_iff_incidence
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (shift : V → ℕ) (tail head : E → V) :
    LinearIndependent ℂ
        (xiTransverseShiftPairDifferenceRotatedFamily shift tail head) ↔
      XiTransverseShiftPairIncidenceIndependent shift tail head := by
  rw [xiTransverseShiftPairDifferenceRotatedFamily_eq_vertexDifference]
  exact linearIndependent_gradedPairwiseDifferences_iff_pointedCollisionIncidence
    shift 0 tail head xiTransverseShiftPrimeDefectRotated (by
      funext z
      simp [xiTransverseShiftPrimeDefectRotated,
        xiTransverseShiftPrimeDefect, xiTransverseShiftRawLogDerivDefect,
        xiTransverseShiftArchimedeanCorrection])
    (linearIndependent_xiTransverseShiftPrimeDefectRotated_occupiedShifts shift)

/-- Rational-coordinate differential independence has the same characteristic-zero incidence
phase as literal complex independence. -/
theorem
    xiTransverseShiftPairDifferenceUpperEndCarrier_full_differentialIndependent_iff_incidence
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (shift : V → ℕ) (tail head : E → V) :
    DifferentialIndependent upperEndRationalCoordinateField
        (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) ↔
      XiTransverseShiftPairIncidenceIndependent shift tail head := by
  constructor
  · intro hdiff
    have hsub := hdiff.comp
      (fun e : (Set.univ : Set E) => e.1) Subtype.val_injective
    have hmat :=
      (xiTransverseShiftPairDifferenceUpperEndCarrier_differentialIndependent_iff_pointedCollisionIncidence
        shift tail head Set.univ).1 hsub
    rwa [pointedCollisionIncidenceMatroid_charZero_eq
      (C := upperEndRationalCoordinateField) (D := ℂ) shift 0 tail head] at hmat
  · intro hmat
    have hmat' : (pointedCollisionIncidenceMatroid
        (C := upperEndRationalCoordinateField) shift 0 tail head).Indep Set.univ := by
      rwa [pointedCollisionIncidenceMatroid_charZero_eq
        (C := upperEndRationalCoordinateField) (D := ℂ) shift 0 tail head]
    have hsub :=
      (xiTransverseShiftPairDifferenceUpperEndCarrier_differentialIndependent_iff_pointedCollisionIncidence
        shift tail head Set.univ).2 hmat'
    exact hsub.comp
      (fun e => ⟨e, Set.mem_univ e⟩)
      (fun _ _ hij => congrArg Subtype.val hij)

/-- All-valuation differential independence has the identical incidence classification. -/
theorem
    xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_full_differentialIndependent_iff_incidence
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (shift : V → ℕ) (tail head : E → V) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) ↔
      XiTransverseShiftPairIncidenceIndependent shift tail head := by
  constructor
  · intro hdiff
    have hsub := hdiff.comp
      (fun e : (Set.univ : Set E) => e.1) Subtype.val_injective
    have hmat :=
      (xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_differentialIndependent_iff_pointedCollisionIncidence
        shift tail head Set.univ).1 hsub
    rwa [pointedCollisionIncidenceMatroid_charZero_eq
      (C := analyticScalarValuationLayerDifferentialField) (D := ℂ)
      shift 0 tail head] at hmat
  · intro hmat
    have hmat' : (pointedCollisionIncidenceMatroid
        (C := analyticScalarValuationLayerDifferentialField)
        shift 0 tail head).Indep Set.univ := by
      rwa [pointedCollisionIncidenceMatroid_charZero_eq
        (C := analyticScalarValuationLayerDifferentialField) (D := ℂ)
        shift 0 tail head]
    have hsub :=
      (xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_differentialIndependent_iff_pointedCollisionIncidence
        shift tail head Set.univ).2 hmat'
    exact hsub.comp
      (fun e => ⟨e, Set.mem_univ e⟩)
      (fun _ _ hij => congrArg Subtype.val hij)

/-- Literal corrected edge independence survives every finite deletion exactly in the pointed
incidence phase. -/
theorem tailCoefficientIndependent_xiTransverseShiftPairDifferenceRotatedFamily_iff_incidence
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (shift : V → ℕ) (tail head : E → V) :
    TailCoefficientIndependent
        (xiTransverseShiftPairDifferenceRotatedFamily shift tail head) ↔
      XiTransverseShiftPairIncidenceIndependent shift tail head := by
  constructor
  · intro htail
    exact (linearIndependent_xiTransverseShiftPairDifferenceRotatedFamily_iff_incidence
      shift tail head).1
        (htail.linearIndependent
          (xiTransverseShiftPairDifferenceRotatedFamily shift tail head))
  · intro hincidence
    apply tailCoefficientIndependent_literal_of_upperEndMero
      (xiTransverseShiftPairDifferenceRotatedFamily shift tail head)
      (xiTransverseShiftPairDifferenceUpperEndAnalytic shift tail head)
    · intro e
      change ((xiTransverseShiftPairDifferenceUpperEndAnalytic shift tail head e :
          upperEndAnalyticSubring) : Germ upperEndFilter ℂ) =
        xiTransverseShiftPairDifferenceUpperEndGerm shift tail head e
      exact xiTransverseShiftPairDifferenceUpperEndCarrier_germ_eq shift tail head e
    · have hdiff : DifferentialIndependent upperEndRationalCoordinateField
          (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) :=
        (xiTransverseShiftPairDifferenceUpperEndCarrier_full_differentialIndependent_iff_incidence
          shift tail head).2 hincidence
      have hdiffC : DifferentialIndependent ℂ
          (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) :=
        GaloisForLFunctions.HTGeometry.DifferentialIndependent.restrictScalars hdiff
      have hlinear := hdiffC.algebraicIndependent.linearIndependent
      have hfamily :
          (fun e => algebraMap upperEndAnalyticSubring upperEndMeroField
            (xiTransverseShiftPairDifferenceUpperEndAnalytic shift tail head e)) =
            xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head := by
        funext e
        exact (xiTransverseShiftPairDifferenceUpperEndCarrier_eq_algebraMap
          shift tail head e).symm
      rw [hfamily]
      exact hlinear

/-- Strict square evaluation Grams survive every finite complex deletion exactly in the pointed
collision incidence phase. -/
theorem xiTransverseShiftPairDifferenceCofiniteEvaluationGram_posDef_iff_incidence
    {V : Type} [Fintype V] {d : ℕ}
    (shift : V → ℕ) (tail head : Fin d → V) :
    (∀ F : Set ℂ, F.Finite →
      ∃ points : Fin d → {z : ℂ // z ∉ F},
        (cofiniteEvaluationGram
          (xiTransverseShiftPairDifferenceRotatedFamily shift tail head) F points).PosDef) ↔
      XiTransverseShiftPairIncidenceIndependent shift tail head := by
  calc
    _ ↔ TailCoefficientIndependent
        (xiTransverseShiftPairDifferenceRotatedFamily shift tail head) :=
      (tailCoefficientIndependent_iff_cofinite_posDef_evaluationGram
        (xiTransverseShiftPairDifferenceRotatedFamily shift tail head)).symm
    _ ↔ _ :=
      tailCoefficientIndependent_xiTransverseShiftPairDifferenceRotatedFamily_iff_incidence
        shift tail head

/-- In the incidence phase, every finite deletion leaves distinct nodes with exact dual edge
coefficient recovery, positive-definite Gram, and positive volume. -/
theorem exists_injective_xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
    {V : Type} [Fintype V] {d : ℕ}
    (shift : V → ℕ) (tail head : Fin d → V)
    (hincidence : XiTransverseShiftPairIncidenceIndependent shift tail head)
    (F : Set ℂ) (hF : F.Finite) :
    ∃ (points : Fin d → {z : ℂ // z ∉ F}) (dual : Fin d → Fin d → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
        xiTransverseShiftPairDifferenceRotatedFamily shift tail head r (points i) =
          if q = r then 1 else 0) ∧
      (∀ (a : Fin d → ℂ) q,
        ∑ i, dual q i *
          (∑ r, a r *
            xiTransverseShiftPairDifferenceRotatedFamily shift tail head r (points i)) = a q) ∧
      (cofiniteEvaluationGram
        (xiTransverseShiftPairDifferenceRotatedFamily shift tail head) F points).PosDef ∧
      0 < (cofiniteEvaluationGram
        (xiTransverseShiftPairDifferenceRotatedFamily shift tail head) F points).det := by
  exact
    exists_injective_cofiniteEvaluationHilbertReconstruction_of_tailCoefficientIndependent
      (xiTransverseShiftPairDifferenceRotatedFamily shift tail head)
      ((tailCoefficientIndependent_xiTransverseShiftPairDifferenceRotatedFamily_iff_incidence
        shift tail head).2 hincidence) F hF

/-- Complete cofinite Hilbert reconstruction phase of a corrected Xi edge family. -/
def XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
    {V : Type} [Fintype V] {d : ℕ}
    (shift : V → ℕ) (tail head : Fin d → V) : Prop :=
  CofiniteEvaluationHilbertReconstruction
    (xiTransverseShiftPairDifferenceRotatedFamily shift tail head)

/-- **Unconditional corrected-Xi edge reconstruction classification.** Complete cofinite Hilbert
recovery is exactly pointed collision incidence independence. -/
theorem xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_incidence
    {V : Type} [Fintype V] {d : ℕ}
    (shift : V → ℕ) (tail head : Fin d → V) :
    XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction shift tail head ↔
      XiTransverseShiftPairIncidenceIndependent shift tail head := by
  calc
    _ ↔ TailCoefficientIndependent
        (xiTransverseShiftPairDifferenceRotatedFamily shift tail head) :=
      cofiniteEvaluationHilbertReconstruction_iff_tailCoefficientIndependent
        (xiTransverseShiftPairDifferenceRotatedFamily shift tail head)
    _ ↔ _ :=
      tailCoefficientIndependent_xiTransverseShiftPairDifferenceRotatedFamily_iff_incidence
        shift tail head

/-- Literal cofinite recovery is equivalent to rational-coordinate differential independence of
the complete corrected edge carrier family. -/
theorem
    xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_differentialIndependent
    {V : Type} [Fintype V] {d : ℕ}
    (shift : V → ℕ) (tail head : Fin d → V) :
    XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction shift tail head ↔
      DifferentialIndependent upperEndRationalCoordinateField
        (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) := by
  rw [xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_incidence,
    xiTransverseShiftPairDifferenceUpperEndCarrier_full_differentialIndependent_iff_incidence]

/-- Literal cofinite recovery also detects differential independence after every scalar valuation
layer has been adjoined. -/
theorem
    xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_allValuation_differentialIndependent
    {V : Type} [Fintype V] {d : ℕ}
    (shift : V → ℕ) (tail head : Fin d → V) :
    XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction shift tail head ↔
      DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) := by
  rw [xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_incidence,
    xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_full_differentialIndependent_iff_incidence]

/-- Corrected-Xi analytic reconstruction is equivalent to an exact finite reconstruction on
distinct occupied-shift incidence coordinates supplied by the Hilbert unisolvence theorem. -/
theorem
    xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_incidenceCoordinateReconstruction
    {V : Type} [Fintype V] {d : ℕ}
    (shift : V → ℕ) (tail head : Fin d → V) :
    XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction shift tail head ↔
      PointedCollisionIncidenceCoordinateReconstruction shift 0 tail head := by
  rw [xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_incidence]
  change (pointedCollisionIncidenceMatroid
      (C := ℂ) shift 0 tail head).Indep Set.univ ↔
    PointedCollisionIncidenceCoordinateReconstruction shift 0 tail head
  rw [pointedCollisionIncidenceMatroid_charZero_eq
    (C := ℂ) (D := ℝ) shift 0 tail head]
  exact pointedCollisionIncidenceMatroid_univ_indep_iff_coordinateReconstruction
    shift 0 tail head

/-- Raw even-Xi analytic reconstruction has the same exact finite reconstruction certificate on
distinct occupied-grade incidence coordinates. -/
theorem
    xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_incidenceCoordinateReconstruction
    {V : Type} [Fintype V] {d : ℕ}
    (grade : V → ℕ) (tail head : Fin d → V) :
    XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction grade tail head ↔
      PointedCollisionIncidenceCoordinateReconstruction grade 0 tail head := by
  rw [xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_incidence]
  change (pointedCollisionIncidenceMatroid
      (C := ℂ) grade 0 tail head).Indep Set.univ ↔
    PointedCollisionIncidenceCoordinateReconstruction grade 0 tail head
  rw [pointedCollisionIncidenceMatroid_charZero_eq
    (C := ℂ) (D := ℝ) grade 0 tail head]
  exact pointedCollisionIncidenceMatroid_univ_indep_iff_coordinateReconstruction
    grade 0 tail head

/-- Corrected-Xi cofinite reconstruction is equivalent to triviality of every real Kirchhoff flow
on the occupied-shift quotient, including its collapsed zero-shift vertex. -/
theorem
    xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_vertexConservation
    {V : Type} [Fintype V] {d : ℕ}
    (shift : V → ℕ) (tail head : Fin d → V) :
    XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction shift tail head ↔
      ∀ weight : Fin d → ℝ,
        (∀ q : pointedCollisionIncidenceVertex shift 0,
          (∑ e, if pointedCollisionIncidenceVertexOf shift 0
              (head e) = q then weight e else 0) =
            ∑ e, if pointedCollisionIncidenceVertexOf shift 0
              (tail e) = q then weight e else 0) →
          ∀ e, weight e = 0 := by
  rw [xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_incidenceCoordinateReconstruction,
    pointedCollisionIncidenceCoordinateReconstruction_iff_vertexConservation]

/-- Raw even-Xi cofinite reconstruction has the identical concrete Kirchhoff classifier on the
occupied-grade quotient. -/
theorem
    xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_vertexConservation
    {V : Type} [Fintype V] {d : ℕ}
    (grade : V → ℕ) (tail head : Fin d → V) :
    XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction grade tail head ↔
      ∀ weight : Fin d → ℝ,
        (∀ q : pointedCollisionIncidenceVertex grade 0,
          (∑ e, if pointedCollisionIncidenceVertexOf grade 0
              (head e) = q then weight e else 0) =
            ∑ e, if pointedCollisionIncidenceVertexOf grade 0
              (tail e) = q then weight e else 0) →
          ∀ e, weight e = 0 := by
  rw [xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_incidenceCoordinateReconstruction,
    pointedCollisionIncidenceCoordinateReconstruction_iff_vertexConservation]

/-- One graph condition simultaneously controls literal reconstruction and differential
independence over both coefficient fields. -/
theorem xiTransverseShiftPairDifferenceCofiniteHilbertPhase_iff
    {V : Type} [Fintype V] {d : ℕ}
    (shift : V → ℕ) (tail head : Fin d → V) :
    XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction shift tail head ↔
      XiTransverseShiftPairIncidenceIndependent shift tail head ∧
        PointedCollisionIncidenceCoordinateReconstruction shift 0 tail head ∧
        (∀ weight : Fin d → ℝ,
          (∀ q : pointedCollisionIncidenceVertex shift 0,
            (∑ e, if pointedCollisionIncidenceVertexOf shift 0
                (head e) = q then weight e else 0) =
              ∑ e, if pointedCollisionIncidenceVertexOf shift 0
                (tail e) = q then weight e else 0) →
            ∀ e, weight e = 0) ∧
        DifferentialIndependent upperEndRationalCoordinateField
          (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) ∧
        DifferentialIndependent analyticScalarValuationLayerDifferentialField
          (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) := by
  constructor
  · intro hrec
    exact ⟨
      (xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_incidence
        shift tail head).1 hrec,
      (xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_incidenceCoordinateReconstruction
        shift tail head).1 hrec,
      (xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_vertexConservation
        shift tail head).1 hrec,
      (xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_differentialIndependent
        shift tail head).1 hrec,
      (xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_allValuation_differentialIndependent
        shift tail head).1 hrec⟩
  · rintro ⟨hincidence, _hcoordinate, _hkirchhoff, _hrational, _hallValuation⟩
    exact (xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_incidence
      shift tail head).2 hincidence

/-- **Universal raw/corrected incidence reparametrization.** Any injective relabelling that fixes
zero preserves the complete pair phase. The raw even-shift grading therefore agrees with every
such corrected-shift coordinate system, not only with doubling. -/
theorem xiTransverseShiftPairIncidenceIndependent_reparam_iff_raw
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (grade : V → ℕ) (embed : ℕ → ℕ) (hinj : Function.Injective embed)
    (hzero : embed 0 = 0) (tail head : E → V) :
    XiTransverseShiftPairIncidenceIndependent
        (embed ∘ grade) tail head ↔
      XiEvenShiftRawPairIncidenceIndependent grade tail head := by
  have hmat := pointedCollisionIncidenceMatroid_comp_injective_eq
    (C := ℂ) grade 0 embed hinj tail head
  rw [hzero] at hmat
  simpa [XiTransverseShiftPairIncidenceIndependent,
    XiEvenShiftRawPairIncidenceIndependent] using
      congrArg (fun M => M.Indep Set.univ) hmat

/-- With the same grade labels, raw even and corrected integral pair families have definitionally
the same complete incidence phase. -/
theorem xiTransverseShiftPairIncidenceIndependent_iff_raw
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (grade : V → ℕ) (tail head : E → V) :
    XiTransverseShiftPairIncidenceIndependent grade tail head ↔
      XiEvenShiftRawPairIncidenceIndependent grade tail head := by
  rfl

/-- **Universal raw/corrected reconstruction reparametrization.** Injective zero-preserving label
changes leave the exact cofinite Hilbert phase unchanged. -/
theorem xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_reparam_iff_raw
    {V : Type} [Fintype V] {d : ℕ}
    (grade : V → ℕ) (embed : ℕ → ℕ) (hinj : Function.Injective embed)
    (hzero : embed 0 = 0) (tail head : Fin d → V) :
    XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
        (embed ∘ grade) tail head ↔
      XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction grade tail head := by
  rw [xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_incidence,
    xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_incidence]
  exact xiTransverseShiftPairIncidenceIndependent_reparam_iff_raw
    grade embed hinj hzero tail head

/-- Raw even and corrected integral pair families with the same labels have the same exact
cofinite Hilbert reconstruction phase. -/
theorem xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_raw
    {V : Type} [Fintype V] {d : ℕ}
    (grade : V → ℕ) (tail head : Fin d → V) :
    XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction grade tail head ↔
      XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction grade tail head := by
  exact xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_reparam_iff_raw
    grade id Function.injective_id rfl tail head

/-- Doubling integral labels preserves the complete pointed collision incidence phase. -/
theorem xiTransverseShiftPairIncidenceIndependent_double_iff_raw
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (grade : V → ℕ) (tail head : E → V) :
    XiTransverseShiftPairIncidenceIndependent
        (fun v => 2 * grade v) tail head ↔
      XiEvenShiftRawPairIncidenceIndependent grade tail head := by
  have hdouble : Function.Injective (fun n : ℕ => 2 * n) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (by exact Nat.zero_lt_succ 1) hab
  simpa [Function.comp_def] using
    xiTransverseShiftPairIncidenceIndependent_reparam_iff_raw
      grade (fun n : ℕ => 2 * n) hdouble rfl tail head

/-- **Raw/corrected pair reconstruction invariance.** After doubling labels, archimedean
correction changes literal functions but not the exact cofinite Hilbert reconstruction phase. -/
theorem xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_double_iff_raw
    {V : Type} [Fintype V] {d : ℕ}
    (grade : V → ℕ) (tail head : Fin d → V) :
    XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
        (fun v => 2 * grade v) tail head ↔
      XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction grade tail head := by
  have hdouble : Function.Injective (fun n : ℕ => 2 * n) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (by exact Nat.zero_lt_succ 1) hab
  simpa [Function.comp_def] using
    xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_reparam_iff_raw
      grade (fun n : ℕ => 2 * n) hdouble rfl tail head

/-- **Universal raw/corrected edge Hilbert phase under reparametrization.** Every injective
zero-preserving corrected-shift coordinate system simultaneously detects raw reconstruction,
real incidence-coordinate reconstruction, Kirchhoff rigidity, and differential independence of
both carrier families over both coefficient fields. -/
theorem xiPairDifferenceRawCorrectedCofiniteHilbertPhase_reparam_iff
    {V : Type} [Fintype V] {d : ℕ}
    (grade : V → ℕ) (embed : ℕ → ℕ) (hinj : Function.Injective embed)
    (hzero : embed 0 = 0) (tail head : Fin d → V) :
    XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
        (embed ∘ grade) tail head ↔
      XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction grade tail head ∧
        PointedCollisionIncidenceCoordinateReconstruction grade 0 tail head ∧
        (∀ weight : Fin d → ℝ,
          (∀ q : pointedCollisionIncidenceVertex grade 0,
            (∑ e, if pointedCollisionIncidenceVertexOf grade 0
                (head e) = q then weight e else 0) =
              ∑ e, if pointedCollisionIncidenceVertexOf grade 0
                (tail e) = q then weight e else 0) →
            ∀ e, weight e = 0) ∧
        DifferentialIndependent upperEndRationalCoordinateField
          (xiTransverseShiftPairDifferenceUpperEndCarrier
            (embed ∘ grade) tail head) ∧
        DifferentialIndependent analyticScalarValuationLayerDifferentialField
          (xiTransverseShiftPairDifferenceUpperEndCarrier
            (embed ∘ grade) tail head) ∧
        DifferentialIndependent upperEndRationalCoordinateField
          (xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head) ∧
        DifferentialIndependent analyticScalarValuationLayerDifferentialField
          (xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head) := by
  constructor
  · intro hcorrected
    have hraw :=
      (xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_reparam_iff_raw
        grade embed hinj hzero tail head).1 hcorrected
    exact ⟨hraw,
      (xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_incidenceCoordinateReconstruction
        grade tail head).1 hraw,
      (xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_vertexConservation
        grade tail head).1 hraw,
      (xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_differentialIndependent
        (embed ∘ grade) tail head).1 hcorrected,
      (xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_allValuation_differentialIndependent
        (embed ∘ grade) tail head).1 hcorrected,
      (xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_differentialIndependent
        grade tail head).1 hraw,
      (xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_allValuation_differentialIndependent
        grade tail head).1 hraw⟩
  · rintro ⟨hraw, _hcoordinate, _hkirchhoff,
      _hcorrectedRational, _hcorrectedAllValuation,
      _hrawRational, _hrawAllValuation⟩
    exact (xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_reparam_iff_raw
      grade embed hinj hzero tail head).2 hraw

/-- **Universal raw/corrected edge Hilbert phase law.** Corrected reconstruction after doubling
simultaneously characterizes raw reconstruction and differential independence of both carrier
families over both coefficient fields. -/
theorem xiPairDifferenceRawCorrectedCofiniteHilbertPhase_iff
    {V : Type} [Fintype V] {d : ℕ}
    (grade : V → ℕ) (tail head : Fin d → V) :
    XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
        (fun v => 2 * grade v) tail head ↔
      XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction grade tail head ∧
        PointedCollisionIncidenceCoordinateReconstruction grade 0 tail head ∧
        (∀ weight : Fin d → ℝ,
          (∀ q : pointedCollisionIncidenceVertex grade 0,
            (∑ e, if pointedCollisionIncidenceVertexOf grade 0
                (head e) = q then weight e else 0) =
              ∑ e, if pointedCollisionIncidenceVertexOf grade 0
                (tail e) = q then weight e else 0) →
            ∀ e, weight e = 0) ∧
        DifferentialIndependent upperEndRationalCoordinateField
          (xiTransverseShiftPairDifferenceUpperEndCarrier
            (fun v => 2 * grade v) tail head) ∧
        DifferentialIndependent analyticScalarValuationLayerDifferentialField
          (xiTransverseShiftPairDifferenceUpperEndCarrier
            (fun v => 2 * grade v) tail head) ∧
        DifferentialIndependent upperEndRationalCoordinateField
          (xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head) ∧
        DifferentialIndependent analyticScalarValuationLayerDifferentialField
          (xiEvenShiftRawPairDifferenceUpperEndCarrier grade tail head) := by
  have hdouble : Function.Injective (fun n : ℕ => 2 * n) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (by exact Nat.zero_lt_succ 1) hab
  simpa [Function.comp_def] using
    xiPairDifferenceRawCorrectedCofiniteHilbertPhase_reparam_iff
      grade (fun n : ℕ => 2 * n) hdouble rfl tail head

end

end RHTower
