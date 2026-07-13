import GaloisForLFunctions.HTGeometry.AnalyticNevanlinnaCarrierBridge

/-!
# Residual relation freeness for actual analytic Nevanlinna carriers

This file transports the compact-patch rank theorem through the literal analytic carrier bridge.
The resulting relation predicate is written only in terms of derivatives of the Cauchy transform
of the weighted carrier.  It then intersects the residual rank locus with the open positive
mass-one chart of the normalized frozen tangent.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory OnePoint Filter Set Topology
open scoped ENNReal OnePoint Topology

noncomputable section

namespace ClassicalAnalyticNevanlinnaCarrierFamily

variable {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)

/-- A polynomial-coefficient relation evaluated on the actual derivatives of the Cauchy
transform of one weighted Nevanlinna carrier. -/
def weightedBoundaryCarrierExpandedPatternRelationHolds
    {row κ ι : Type} [Fintype row] [Fintype κ] [DecidableEq κ] [Fintype ι]
    (eta : Measure (OnePoint ℝ)) [IsFiniteMeasure eta]
    (density : Lp ℝ (⊤ : ENNReal) eta)
    (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (shift : InjectiveShiftConfiguration ι)
    (coeff : κ × Fin (degree + 1) → ℂ) : Prop :=
  ∀ packet : InjectiveProjectiveRowPacket row,
    (∀ x, 0 < (combinedProjectiveRowShiftPacket packet shift x).im) →
    ∀ r, ∑ col, coeff col *
      expandedDifferentialEvaluationMatrix degree
        (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
        (F.weightedBoundaryCarrierExpandedPacketValue
          eta density orders packet shift) r col = 0

/-- Abstract relation rigidity from the compact-patch theorem becomes literal relation rigidity
for derivatives of the weighted carrier transform. -/
theorem weightedBoundaryCarrierExpandedPatternRelation_coefficients_eq_zero
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
    (hfree : ∀ coeff : κ × Fin (degree + 1) → ℂ,
      actualNevanlinnaExpandedPatternRelationHolds
        (row := row) F.background F.amplitude F.quotient degree orders exponent
          eta baseDensity S w shift coeff →
        ∀ col, coeff col = 0)
    (coeff : κ × Fin (degree + 1) → ℂ)
    (hrelation : F.weightedBoundaryCarrierExpandedPatternRelationHolds
      (row := row) eta (baseDensity + w.1) degree orders exponent shift coeff) :
    ∀ col, coeff col = 0 := by
  apply hfree coeff
  intro packet hupper r
  have hpacket :=
    F.weightedBoundaryCarrierExpandedPacketValue_eq_actualNevanlinnaExpandedPacketValue
      eta baseDensity S w hw hint orders packet shift hupperMap hupper
  rw [← hpacket]
  exact hrelation packet hupper r

/-- **Positive-chart actual-carrier residual law.**  A residual abstract relation-free locus in a
normalized frozen tangent pulls back to a dense residual family of strictly positive mass-one
densities whose actual weighted-carrier Cauchy transforms satisfy the same relation rigidity. -/
theorem normalizedPositiveChart_actualCarrier_relationFree_dense_residual
    {ιf : Type*} [Fintype ιf]
    (zf : ιf → ℂ) (nf : ιf → ℕ)
    (haf : ∀ i, F.amplitude (zf i) ≠ 0)
    (hqdf : ∀ i, deriv F.quotient (zf i) ≠ 0)
    (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta]
    (hupperf : ∀ i, 0 < (F.quotient (zf i)).im)
    (row κ ι : ℕ → Type)
    [∀ n, Fintype (row n)]
    [∀ n, Fintype (κ n)] [∀ n, DecidableEq (κ n)]
    [∀ n, Fintype (ι n)]
    (degree : ℕ → ℕ) (orders : ∀ n, ι n → ℕ)
    (exponent : ∀ n,
      κ n → (Fin (Fintype.card (Σ i, Fin (orders n i))) →₀ ℕ))
    (hupperMap : ∀ z, 0 < z.im → 0 < (F.quotient z).im)
    (relationFree : Set (LinearMap.ker
      (normalizedProjectiveNevanlinnaJetLinftyContinuousControl
        F.amplitude F.quotient zf nf haf hqdf eta hupperf).toLinearMap))
    (hrelationFree : relationFree ∈ residual (LinearMap.ker
      (normalizedProjectiveNevanlinnaJetLinftyContinuousControl
        F.amplitude F.quotient zf nf haf hqdf eta hupperf).toLinearMap))
    (hfree : ∀ w ∈ relationFree, ∀ n (shift : InjectiveShiftConfiguration (ι n))
      (coeff : κ n × Fin (degree n + 1) → ℂ),
      actualNevanlinnaExpandedPatternRelationHolds
        (row := row n) F.background F.amplitude F.quotient
          (degree n) (orders n) (exponent n) eta (linftyOne eta)
          (LinearMap.ker
            (normalizedProjectiveNevanlinnaJetLinftyContinuousControl
              F.amplitude F.quotient zf nf haf hqdf eta hupperf).toLinearMap)
          w shift coeff →
        ∀ col, coeff col = 0) :
    let frozen := normalizedProjectiveNevanlinnaJetLinftyContinuousControl
      F.amplitude F.quotient zf nf haf hqdf eta hupperf
    let S := LinearMap.ker frozen.toLinearMap
    let positiveChart : Set S := Metric.ball 0 1
    let actualRelationFree : Set positiveChart := {w | ∀ n
      (shift : InjectiveShiftConfiguration (ι n))
      (coeff : κ n × Fin (degree n + 1) → ℂ),
      F.weightedBoundaryCarrierExpandedPatternRelationHolds
        (row := row n) eta (linftyOne eta + w.1.1)
          (degree n) (orders n) (exponent n) shift coeff →
        ∀ col, coeff col = 0}
    Dense actualRelationFree ∧ actualRelationFree ∈ residual positiveChart ∧
      ∀ w : positiveChart,
        LinftyStrictlyPositive eta (linftyOne eta + w.1.1) ∧
          ∫ t, (linftyOne eta + w.1.1) t ∂eta = 1 := by
  dsimp only
  let frozen := normalizedProjectiveNevanlinnaJetLinftyContinuousControl
    F.amplitude F.quotient zf nf haf hqdf eta hupperf
  let S := LinearMap.ker frozen.toLinearMap
  let positiveChart : Set S := Metric.ball 0 1
  let positiveAbstract : Set positiveChart := Subtype.val ⁻¹' relationFree
  let actualRelationFree : Set positiveChart := {w | ∀ n
    (shift : InjectiveShiftConfiguration (ι n))
    (coeff : κ n × Fin (degree n + 1) → ℂ),
    F.weightedBoundaryCarrierExpandedPatternRelationHolds
      (row := row n) eta (linftyOne eta + w.1.1)
        (degree n) (orders n) (exponent n) shift coeff →
      ∀ col, coeff col = 0}
  have hpositive := normalizedProjectiveNevanlinna_positiveChart_dense_residual
    F.amplitude F.quotient zf nf haf hqdf eta hupperf relationFree hrelationFree
  have hsubset : positiveAbstract ⊆ actualRelationFree := by
    intro w hw n shift coeff hrelation
    have hprob := hpositive.2.2 w
    exact F.weightedBoundaryCarrierExpandedPatternRelation_coefficients_eq_zero
      eta (linftyOne eta) S w.1 hprob.1 hprob.2
      (degree n) (orders n) (exponent n) shift hupperMap
      (hfree w.1 hw n shift) coeff hrelation
  exact ⟨hpositive.1.mono hsubset,
    Filter.mem_of_superset hpositive.2.1 hsubset, hpositive.2.2⟩

end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry
