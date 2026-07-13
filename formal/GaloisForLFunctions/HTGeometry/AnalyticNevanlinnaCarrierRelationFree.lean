import GaloisForLFunctions.HTGeometry.AnalyticNevanlinnaCarrierBridge
import GaloisForLFunctions.HTGeometry.PolynomialCoefficientDifferentialFreeness
import GaloisForLFunctions.HTGeometry.DigammaHypertranscendental

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

/-- A generously rectangular evaluation-row type for a canonical finite differential pattern.
The extra `shiftCount + 2` rows make the transversality codimension inequality automatic. -/
abbrev CarrierPatternRow (p : FiniteDifferentialPattern Unit) :=
  Fin (Fintype.card (PatternShape p) + p.coefficientDegree + p.shiftCount + 2)

abbrev CarrierPatternMonomial (p : FiniteDifferentialPattern Unit) :=
  Fin p.monomialCount

abbrev CarrierPatternShift (p : FiniteDifferentialPattern Unit) :=
  Fin p.shiftCount

theorem carrierPattern_rows_strictly_dominate_columns
    (p : FiniteDifferentialPattern Unit) :
    Fintype.card
        (CarrierPatternMonomial p × Fin (p.coefficientDegree + 1)) +
        p.coefficientDegree < Fintype.card (CarrierPatternRow p) := by
  simp [CarrierPatternRow, CarrierPatternMonomial, PatternShape]
  omega

theorem carrierPattern_shift_dimension_below_codimension
    (p : FiniteDifferentialPattern Unit) :
    Module.finrank ℝ (CarrierPatternShift p → ℂ) <
      2 * (Fintype.card (CarrierPatternRow p) -
        Fintype.card
          (CarrierPatternMonomial p × Fin (p.coefficientDegree + 1)) -
        p.coefficientDegree + 1) := by
  rw [Module.finrank_pi_fintype]
  simp [CarrierPatternRow, CarrierPatternShift, CarrierPatternMonomial, PatternShape]
  omega

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
    {ιf α : Type*} [Fintype ιf] [Countable α]
    (zf : ιf → ℂ) (nf : ιf → ℕ)
    (haf : ∀ i, F.amplitude (zf i) ≠ 0)
    (hqdf : ∀ i, deriv F.quotient (zf i) ≠ 0)
    (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta]
    (hupperf : ∀ i, 0 < (F.quotient (zf i)).im)
    (row κ ι : α → Type)
    [∀ n, Fintype (row n)]
    [∀ n, Fintype (κ n)] [∀ n, DecidableEq (κ n)]
    [∀ n, Fintype (ι n)]
    (degree : α → ℕ) (orders : ∀ n, ι n → ℕ)
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

/-- **Analytic Nevanlinna carrier capstone.**  The compact incidence/projection/stratification
geometry, the uniform finite probe, and the analytic carrier bridge combine to give a dense
residual family in the positive mass-one chart whose actual weighted-carrier transforms satisfy
coefficient rigidity for every encoded differential pattern and every distinct shift tuple. -/
theorem countablePatterns_positiveActualCarrier_relationFree_dense_residual
    (projectiveGeometry : ClassicalComplexProjectiveIncidenceGeometry)
    (parametricAvoidance : ClassicalStratifiedParametricAvoidance)
    (row κ ι : ℕ → Type)
    [∀ n, Fintype (row n)] [∀ n, DecidableEq (row n)]
    [∀ n, Fintype (κ n)] [∀ n, DecidableEq (κ n)]
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    {ιf : Type} [Fintype ιf] [DecidableEq ιf]
    (hCmin : HasMinimalExponentialType F.c)
    (hnoCommon : ∀ z, ¬ (F.c z = 0 ∧ F.d z = 0))
    {p : ℂ} (hCp : F.c p = 0) {c : ℂ} (hCc : F.c c ≠ 0)
    (hupperMap : ∀ z, 0 < z.im → 0 < (F.quotient z).im)
    (zf : ιf → ℂ)
    (hqf_inj : Function.Injective (fun i => F.quotient (zf i)))
    (hupperf : ∀ i, 0 < (F.quotient (zf i)).im)
    (nf : ιf → ℕ) (haf : ∀ i, F.amplitude (zf i) ≠ 0)
    (hqdf : ∀ i, deriv F.quotient (zf i) ≠ 0)
    (degree : ℕ → ℕ) (orders : ∀ n, ι n → ℕ)
    (exponent : ∀ n,
      κ n → (Fin (Fintype.card (Σ i, Fin (orders n i))) →₀ ℕ))
    (hexponent : ∀ n, Function.Injective (exponent n))
    (hrows : ∀ n,
      Fintype.card (κ n × Fin (degree n + 1)) + degree n < Fintype.card (row n))
    (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta] (heta : eta.support.Infinite)
    (hdim : ∀ n, Module.finrank ℝ (ι n → ℂ) <
      2 * (Fintype.card (row n) -
        Fintype.card (κ n × Fin (degree n + 1)) - degree n + 1)) :
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
  let relationFree : Set S := {w | ∀ n
    (shift : InjectiveShiftConfiguration (ι n))
    (coeff : κ n × Fin (degree n + 1) → ℂ),
    actualNevanlinnaExpandedPatternRelationHolds
      (row := row n) F.background F.amplitude F.quotient
        (degree n) (orders n) (exponent n) eta (linftyOne eta) S w shift coeff →
      ∀ col, coeff col = 0}
  have hupperMap' : ∀ z, 0 < z.im →
      0 < (projectiveNevanlinnaQuotient F.c F.d z).im := by
    simpa [quotient, projectiveNevanlinnaQuotient] using hupperMap
  have hqf_inj' : Function.Injective
      (fun i => projectiveNevanlinnaQuotient F.c F.d (zf i)) := by
    simpa [quotient, projectiveNevanlinnaQuotient] using hqf_inj
  have hupperf' : ∀ i,
      0 < (projectiveNevanlinnaQuotient F.c F.d (zf i)).im := by
    simpa [quotient, projectiveNevanlinnaQuotient] using hupperf
  have haf' : ∀ i, projectiveNevanlinnaAmplitude F.c (zf i) ≠ 0 := by
    simpa [amplitude, projectiveNevanlinnaAmplitude] using haf
  have hqdf' : ∀ i,
      deriv (projectiveNevanlinnaQuotient F.c F.d) (zf i) ≠ 0 := by
    simpa [quotient, projectiveNevanlinnaQuotient] using hqdf
  have habstract : Dense relationFree ∧ relationFree ∈ residual S := by
    simpa [relationFree, frozen, S, amplitude, quotient,
      projectiveNevanlinnaAmplitude, projectiveNevanlinnaQuotient] using
      (countablePatterns_actualNevanlinna_relationFree_dense_residual
        projectiveGeometry parametricAvoidance row κ ι hCmin F.differentiable_d
        hnoCommon hCp hCc hupperMap' F.background F.contDiffOn_iteratedDeriv_background
        zf hqf_inj' hupperf'
        nf haf' hqdf' degree orders exponent hexponent hrows eta heta
        (linftyOne eta) hdim)
  exact F.normalizedPositiveChart_actualCarrier_relationFree_dense_residual
    zf nf haf hqdf eta hupperf row κ ι degree orders exponent hupperMap
    relationFree habstract.2 (by
      intro w hw n shift coeff
      exact hw n shift coeff)

/-- **All finite shapes, abstract carrier form.**  The canonical type of finite differential
patterns is countable.  Intersecting the one-pattern global rank theorems therefore gives one
dense residual tangent locus with coefficient rigidity for every finite differential-pattern
shape at once. -/
theorem allFinitePatterns_abstractCarrier_relationFree_dense_residual
    (projectiveGeometry : ClassicalComplexProjectiveIncidenceGeometry)
    (parametricAvoidance : ClassicalStratifiedParametricAvoidance)
    {ιf : Type} [Fintype ιf] [DecidableEq ιf]
    (hCmin : HasMinimalExponentialType F.c)
    (hnoCommon : ∀ z, ¬ (F.c z = 0 ∧ F.d z = 0))
    {p0 : ℂ} (hCp : F.c p0 = 0) {c0 : ℂ} (hCc : F.c c0 ≠ 0)
    (hupperMap : ∀ z, 0 < z.im → 0 < (F.quotient z).im)
    (zf : ιf → ℂ)
    (hqf_inj : Function.Injective (fun i => F.quotient (zf i)))
    (hupperf : ∀ i, 0 < (F.quotient (zf i)).im)
    (nf : ιf → ℕ) (haf : ∀ i, F.amplitude (zf i) ≠ 0)
    (hqdf : ∀ i, deriv F.quotient (zf i) ≠ 0)
    (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta] (heta : eta.support.Infinite) :
    let frozen := normalizedProjectiveNevanlinnaJetLinftyContinuousControl
      F.amplitude F.quotient zf nf haf hqdf eta hupperf
    let S := LinearMap.ker frozen.toLinearMap
    let relationFree : Set S := {w | ∀ p : FiniteDifferentialPattern Unit
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      actualNevanlinnaExpandedPatternRelationHolds
        (row := CarrierPatternRow p) F.background F.amplitude F.quotient
          p.coefficientDegree p.orders p.jetExponent eta (linftyOne eta)
          S w shift coeff →
        ∀ col, coeff col = 0}
    Dense relationFree ∧ relationFree ∈ residual S := by
  dsimp only
  let frozen := normalizedProjectiveNevanlinnaJetLinftyContinuousControl
    F.amplitude F.quotient zf nf haf hqdf eta hupperf
  let S := LinearMap.ker frozen.toLinearMap
  let goodPattern : FiniteDifferentialPattern Unit → Set S := fun p =>
    {w | ∀ shift : InjectiveShiftConfiguration (CarrierPatternShift p),
      actualNevanlinnaExpandedFullRankWitness
        (row := CarrierPatternRow p) (κ := CarrierPatternMonomial p)
        (ι := CarrierPatternShift p)
        F.background F.amplitude F.quotient p.coefficientDegree p.orders
          p.jetExponent eta (linftyOne eta) S w shift}
  let relationFree : Set S := {w | ∀ p : FiniteDifferentialPattern Unit
    (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
    (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
    actualNevanlinnaExpandedPatternRelationHolds
      (row := CarrierPatternRow p) F.background F.amplitude F.quotient
        p.coefficientDegree p.orders p.jetExponent eta (linftyOne eta)
        S w shift coeff →
      ∀ col, coeff col = 0}
  have hupperMap' : ∀ z, 0 < z.im →
      0 < (projectiveNevanlinnaQuotient F.c F.d z).im := by
    simpa [quotient, projectiveNevanlinnaQuotient] using hupperMap
  have hqf_inj' : Function.Injective
      (fun i => projectiveNevanlinnaQuotient F.c F.d (zf i)) := by
    simpa [quotient, projectiveNevanlinnaQuotient] using hqf_inj
  have hupperf' : ∀ i,
      0 < (projectiveNevanlinnaQuotient F.c F.d (zf i)).im := by
    simpa [quotient, projectiveNevanlinnaQuotient] using hupperf
  have haf' : ∀ i, projectiveNevanlinnaAmplitude F.c (zf i) ≠ 0 := by
    simpa [amplitude, projectiveNevanlinnaAmplitude] using haf
  have hqdf' : ∀ i,
      deriv (projectiveNevanlinnaQuotient F.c F.d) (zf i) ≠ 0 := by
    simpa [quotient, projectiveNevanlinnaQuotient] using hqdf
  have hgoodPattern : ∀ p : FiniteDifferentialPattern Unit,
      Dense (goodPattern p) ∧ goodPattern p ∈ residual S := by
    intro p
    simpa [goodPattern, frozen, S, amplitude, quotient,
      projectiveNevanlinnaAmplitude, projectiveNevanlinnaQuotient] using
      (global_injectiveShifts_actualNevanlinna_fullRankWitness_dense_residual
        (row := CarrierPatternRow p) (κ := CarrierPatternMonomial p)
        (ι := CarrierPatternShift p)
        projectiveGeometry parametricAvoidance hCmin F.differentiable_d
        hnoCommon hCp hCc hupperMap' F.background
        F.contDiffOn_iteratedDeriv_background zf hqf_inj' hupperf' nf haf' hqdf'
        p.coefficientDegree p.orders p.jetExponent p.jetExponent_injective
        (carrierPattern_rows_strictly_dominate_columns p)
        eta heta (linftyOne eta)
        (carrierPattern_shift_dimension_below_codimension p))
  have hfullResidual : (⋂ p, goodPattern p) ∈ residual S :=
    countable_iInter_mem.mpr fun p => (hgoodPattern p).2
  have hsubset : (⋂ p, goodPattern p) ⊆ relationFree := by
    intro w hw p shift coeff hrelation
    exact actualNevanlinnaExpandedPatternRelation_coefficients_eq_zero_of_fullRankWitness
      F.background F.amplitude F.quotient p.coefficientDegree p.orders
      p.jetExponent eta (linftyOne eta) S w shift
      (Set.mem_iInter.mp hw p shift) coeff hrelation
  exact ⟨(dense_of_mem_residual hfullResidual).mono hsubset,
    Filter.mem_of_superset hfullResidual hsubset⟩

end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry
