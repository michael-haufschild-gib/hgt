import GaloisForLFunctions.HTGeometry.AnalyticNevanlinnaCarrierRelationFree
import GaloisForLFunctions.HTGeometry.InfiniteSupportProbabilityLaws
import GaloisForLFunctions.HTGeometry.ProjectiveFiniteConstraintCarrierAperture

/-!
# Intrinsic translation-differential freeness for probability carriers

The compact-patch Nevanlinna theorem is stated in density coordinates.  This file packages the
same actual Cauchy-jet relation directly as a predicate of the resulting probability measure.
It is therefore independent of the chosen positive chart representing that measure.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory OnePoint Set
open ClassicalAnalyticNevanlinnaCarrierFamily
open scoped ENNReal OnePoint

noncomputable section

/-- The simultaneous finite packet of actual Cauchy-transform derivatives of a probability law. -/
def probabilityCarrierExpandedPacketValue
    {row ι : Type} [Fintype ι]
    (nu : ProbabilityMeasure ℝ) (orders : ι → ℕ)
    (packet : InjectiveProjectiveRowPacket row)
    (shift : InjectiveShiftConfiguration ι) :
    row × Fin (Fintype.card (Σ i, Fin (orders i))) → ℂ :=
  fun p =>
    let j := (Fintype.equivFin (Σ i, Fin (orders i))).symm p.2
    iteratedDeriv j.2
      (fun z => ∫ x, ((x : ℂ) - z)⁻¹ ∂(nu : Measure ℝ))
      (packet.1 p.1 + shift.1 j.1)

/-- One finite polynomial-coefficient differential relation on the translated Cauchy family of a
probability law. -/
def probabilityCarrierExpandedPatternRelationHolds
    {row κ ι : Type} [Fintype κ] [Fintype ι]
    (nu : ProbabilityMeasure ℝ)
    (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (shift : InjectiveShiftConfiguration ι)
    (coeff : κ × Fin (degree + 1) → ℂ) : Prop :=
  ∀ packet : InjectiveProjectiveRowPacket row,
    (∀ x, 0 < (combinedProjectiveRowShiftPacket packet shift x).im) →
    ∀ r, ∑ col, coeff col *
      expandedDifferentialEvaluationMatrix degree
        (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
        (probabilityCarrierExpandedPacketValue nu orders packet shift) r col = 0

/-- One admissible row packet witnesses full coefficient rank for the literal Cauchy jets of a
probability carrier.  Unlike relation-freeness, this is a finite open certificate once the shift
configuration is fixed. -/
def probabilityCarrierExpandedFullRankWitness
    {row κ ι : Type} [Fintype κ] [Fintype ι]
    (nu : ProbabilityMeasure ℝ)
    (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (shift : InjectiveShiftConfiguration ι) : Prop :=
  ∃ packet : InjectiveProjectiveRowPacket row,
    (∀ x, 0 < (combinedProjectiveRowShiftPacket packet shift x).im) ∧
      Function.Injective
        (expandedDifferentialEvaluationMatrix degree
          (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
          (probabilityCarrierExpandedPacketValue nu orders packet shift)).mulVec

/-- A literal full-rank packet certificate kills every coefficient of a finite relation on the
same probability carrier. -/
theorem probabilityCarrierExpandedPatternRelation_coefficients_eq_zero_of_fullRankWitness
    {row κ ι : Type} [Fintype row] [Fintype κ] [DecidableEq κ] [Fintype ι]
    (nu : ProbabilityMeasure ℝ)
    (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (shift : InjectiveShiftConfiguration ι)
    (hwitness : probabilityCarrierExpandedFullRankWitness
      (row := row) (nu := nu) degree orders exponent shift)
    (coeff : κ × Fin (degree + 1) → ℂ)
    (hrelation : probabilityCarrierExpandedPatternRelationHolds
      (row := row) nu degree orders exponent shift coeff) :
    ∀ col, coeff col = 0 := by
  obtain ⟨packet, hupper, hinjective⟩ := hwitness
  let A := expandedDifferentialEvaluationMatrix degree
    (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
    (probabilityCarrierExpandedPacketValue nu orders packet shift)
  have hmul : A.mulVec coeff = 0 := by
    funext r
    simpa [A, Matrix.mulVec, dotProduct, mul_comm] using hrelation packet hupper r
  have hcoeff : coeff = 0 := hinjective (by simpa [A] using hmul)
  intro col
  exact congrFun hcoeff col

/-- Maximal finite-configuration translation-differential freeness of a probability carrier.
Every polynomial-coefficient relation among every finite family of distinct complex translates
and finite jet depths has zero coefficient vector. -/
def MaximalTranslationDifferentialFree (nu : ProbabilityMeasure ℝ) : Prop :=
  ∀ (p : FiniteDifferentialPattern Unit)
    (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
    (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
    probabilityCarrierExpandedPatternRelationHolds
      (row := CarrierPatternRow p) nu p.coefficientDegree p.orders
        (carrierPatternExponent p) shift coeff →
      ∀ col, coeff col = 0

/-- The simultaneous intrinsic full-rank phase for every canonical finite differential pattern
and every finite tuple of distinct complex translations. -/
def MaximalTranslationFullRankWitness (nu : ProbabilityMeasure ℝ) : Prop :=
  ∀ (p : FiniteDifferentialPattern Unit)
    (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
    probabilityCarrierExpandedFullRankWitness
      (row := CarrierPatternRow p) (nu := nu)
      p.coefficientDegree p.orders (carrierPatternExponent p) shift

/-- The full-rank witness phase is contained in the maximal translation-differentially free
phase. -/
theorem maximalTranslationDifferentialFree_of_fullRankWitness
    {nu : ProbabilityMeasure ℝ}
    (hfull : MaximalTranslationFullRankWitness nu) :
    MaximalTranslationDifferentialFree nu := by
  intro p shift coeff hrelation
  exact probabilityCarrierExpandedPatternRelation_coefficients_eq_zero_of_fullRankWitness
    nu p.coefficientDegree p.orders (carrierPatternExponent p) shift
      (hfull p shift) coeff hrelation

namespace ClassicalAnalyticNevanlinnaCarrierFamily

variable {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)

/-- An abstract compact-patch full-rank witness is the same finite certificate for the intrinsic
Cauchy jets of the resulting normalized probability carrier. -/
theorem probabilityCarrierExpandedFullRankWitness_weightedBoundaryProbabilityCarrier
    {row κ ι : Type} [Fintype row] [Fintype κ] [DecidableEq κ] [Fintype ι]
    (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta]
    (baseDensity : Lp ℝ (⊤ : ENNReal) eta)
    (S : Submodule ℝ (Lp ℝ (⊤ : ENNReal) eta)) (w : S)
    (hw : LinftyStrictlyPositive eta (baseDensity + w.1))
    (hint : ∫ t, (baseDensity + w.1) t ∂eta = 1)
    (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (shift : InjectiveShiftConfiguration ι)
    (hupperMap : ∀ z, 0 < z.im → 0 < (F.quotient z).im)
    (hfull : actualNevanlinnaExpandedFullRankWitness
      (row := row) (κ := κ) (ι := ι)
      F.background F.amplitude F.quotient degree orders exponent
        eta baseDensity S w shift) :
    probabilityCarrierExpandedFullRankWitness
      (row := row)
      (weightedBoundaryProbabilityCarrier F.base.toBoundaryFamily
        eta (baseDensity + w.1) hw hint)
      degree orders exponent shift := by
  obtain ⟨packet, hupper, hinjective⟩ := hfull
  refine ⟨packet, hupper, ?_⟩
  have hpacket :=
    F.weightedBoundaryCarrierExpandedPacketValue_eq_actualNevanlinnaExpandedPacketValue
      eta baseDensity S w hw hint orders packet shift hupperMap hupper
  simpa only [probabilityCarrierExpandedPacketValue] using
    (show Function.Injective
        (expandedDifferentialEvaluationMatrix degree
          (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
          (F.weightedBoundaryCarrierExpandedPacketValue
            eta (baseDensity + w.1) orders packet shift)).mulVec by
      rw [hpacket]
      exact hinjective)

/-- The intrinsic carrier predicate is definitionally the actual-carrier predicate used by the
Nevanlinna compact-patch theorem. -/
theorem maximalTranslationDifferentialFree_weightedBoundaryProbabilityCarrier
    (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta]
    (density : Lp ℝ (⊤ : ENNReal) eta)
    (hpositive : LinftyStrictlyPositive eta density)
    (hintegral : ∫ t, density t ∂eta = 1)
    (hfree : ∀ (p : FiniteDifferentialPattern Unit)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      F.weightedBoundaryCarrierExpandedPatternRelationHolds
        (row := CarrierPatternRow p) eta density p.coefficientDegree p.orders
          (carrierPatternExponent p) shift coeff →
        ∀ col, coeff col = 0) :
    MaximalTranslationDifferentialFree
      (weightedBoundaryProbabilityCarrier F.base.toBoundaryFamily
        eta density hpositive hintegral) := by
  intro p shift coeff hrelation
  apply hfree p shift coeff
  exact hrelation

/-- Maximal translation-differential freeness implies literal hypertranscendence of the unshifted
Cauchy transform. -/
theorem hypertranscendental_weightedBoundaryProbabilityCarrierCauchy
    (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta]
    (density : Lp ℝ (⊤ : ENNReal) eta)
    (hpositive : LinftyStrictlyPositive eta density)
    (hintegral : ∫ t, density t ∂eta = 1)
    (hfree : MaximalTranslationDifferentialFree
      (weightedBoundaryProbabilityCarrier F.base.toBoundaryFamily
        eta density hpositive hintegral)) :
    Hypertranscendental
      (fun z => ∫ x, ((x : ℂ) - z)⁻¹
        ∂(weightedBoundaryProbabilityCarrier F.base.toBoundaryFamily
          eta density hpositive hintegral : Measure ℝ)) := by
  apply hypertranscendental_weightedBoundaryCarrierCauchy_of_allFinitePatterns_relationFree F
  intro p shift coeff hrelation
  apply hfree p shift coeff
  exact hrelation

end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry
