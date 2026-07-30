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
open Polynomial
open scoped ENNReal OnePoint Topology

noncomputable section

namespace ClassicalAnalyticNevanlinnaCarrierFamily

variable {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)

/-- A generously rectangular evaluation-row type for a canonical finite differential pattern.
The extra `shiftCount + 2` rows make the transversality codimension inequality automatic. -/
abbrev CarrierPatternRow {Γ : Type*} (p : FiniteDifferentialPattern Γ) :=
  Fin (Fintype.card (PatternShape p) + p.coefficientDegree + p.shiftCount + 2)

abbrev CarrierPatternMonomial {Γ : Type*} (p : FiniteDifferentialPattern Γ) :=
  Fin p.monomialCount

abbrev CarrierPatternShift {Γ : Type*} (p : FiniteDifferentialPattern Γ) :=
  Fin p.shiftCount

/-- Enumerate the dependent within-shift jet variables in the finite coordinate type used by the
expanded evaluation matrix. -/
noncomputable def carrierPatternExponent {Γ : Type*} (p : FiniteDifferentialPattern Γ) :
    CarrierPatternMonomial p →
      (Fin (Fintype.card (Σ i : CarrierPatternShift p, Fin (p.orders i))) →₀ ℕ) :=
  fun b => Finsupp.equivCongrLeft
    (Fintype.equivFin (Σ i : CarrierPatternShift p, Fin (p.orders i)))
    (p.jetExponent b)

theorem carrierPatternExponent_injective {Γ : Type*} (p : FiniteDifferentialPattern Γ) :
    Function.Injective (carrierPatternExponent p) :=
  (Finsupp.equivCongrLeft
    (Fintype.equivFin (Σ i : CarrierPatternShift p, Fin (p.orders i)))).injective.comp
      p.jetExponent_injective

theorem carrierPattern_rows_strictly_dominate_columns {Γ : Type*}
    (p : FiniteDifferentialPattern Γ) :
    Fintype.card
        (CarrierPatternMonomial p × Fin (p.coefficientDegree + 1)) +
        p.coefficientDegree < Fintype.card (CarrierPatternRow p) := by
  simp [CarrierPatternRow, CarrierPatternMonomial, PatternShape]
  omega

theorem carrierPattern_shift_dimension_below_codimension {Γ : Type*}
    (p : FiniteDifferentialPattern Γ) :
    Module.finrank ℝ (CarrierPatternShift p → ℂ) <
      2 * (Fintype.card (CarrierPatternRow p) -
        Fintype.card
          (CarrierPatternMonomial p × Fin (p.coefficientDegree + 1)) -
        p.coefficientDegree + 1) := by
  rw [Module.finrank_pi_fintype]
  simp [CarrierPatternRow, CarrierPatternShift, CarrierPatternMonomial, PatternShape]
  omega

/-- The dependent jet coordinates of a one-shift packet are canonically the ordinary finite jet
coordinates. -/
def singleShiftJetEquiv (n : ℕ) : (Σ _ : Fin 1, Fin n) ≃ Fin n where
  toFun := fun s => s.2
  invFun := fun j => ⟨0, j⟩
  left_inv := by
    rintro ⟨i, j⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  right_inv := fun _ => rfl

/-- Move an ordinary finite-jet polynomial into the dependent coordinates of a one-shift
packet. -/
noncomputable def renameToSingleShiftJets {R : Type*} [CommSemiring R] (n : ℕ)
    (Q : MvPolynomial (Fin n) R) : MvPolynomial (Σ _ : Fin 1, Fin n) R :=
  MvPolynomial.rename (singleShiftJetEquiv n).symm Q

theorem renameToSingleShiftJets_injective {R : Type*} [CommSemiring R] (n : ℕ) :
    Function.Injective (renameToSingleShiftJets (R := R) n) := by
  exact MvPolynomial.rename_injective _ (singleShiftJetEquiv n).symm.injective

/-- Reshaping the point variable into polynomial coefficients commutes with specialization and
arbitrary jet evaluation. -/
theorem eval_specialize_reshapeJet (n : ℕ) (z : ℂ) (v : Fin (n + 1) → ℂ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) :
    MvPolynomial.eval v (specializePolynomialCoefficients z (reshapeJet n P)) =
      MvPolynomial.eval (Fin.cons z v) P := by
  rw [specializePolynomialCoefficients, MvPolynomial.eval_map]
  have hhom : ((MvPolynomial.eval₂Hom (Polynomial.evalRingHom z) v).comp (reshapeJet n)) =
      (MvPolynomial.eval (Fin.cons z v) : _ →+* ℂ) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [reshapeJet]
    · intro i
      induction i using Fin.cases with
      | zero => simp [reshapeJet]
      | succ j => simp [reshapeJet, Fin.cons_succ]
  exact RingHom.congr_fun hhom P

/-- A polynomial-coefficient relation evaluated on the actual derivatives of the Cauchy
transform of one weighted Nevanlinna carrier. -/
def weightedBoundaryCarrierExpandedPatternRelationHolds
    {row κ ι : Type} [Fintype κ] [Fintype ι]
    (eta : Measure (OnePoint ℝ))
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
      (normalizedProjectiveCauchyJetLinftyContinuousControl
        (fun i => F.quotient (zf i)) nf eta hupperf).toLinearMap))
    (hrelationFree : relationFree ∈ residual (LinearMap.ker
      (normalizedProjectiveCauchyJetLinftyContinuousControl
        (fun i => F.quotient (zf i)) nf eta hupperf).toLinearMap))
    (hfree : ∀ w ∈ relationFree, ∀ n (shift : InjectiveShiftConfiguration (ι n))
      (coeff : κ n × Fin (degree n + 1) → ℂ),
      actualNevanlinnaExpandedPatternRelationHolds
        (row := row n) F.background F.amplitude F.quotient
          (degree n) (orders n) (exponent n) eta (linftyOne eta)
          (LinearMap.ker
            (normalizedProjectiveCauchyJetLinftyContinuousControl
              (fun i => F.quotient (zf i)) nf eta hupperf).toLinearMap)
          w shift coeff →
        ∀ col, coeff col = 0) :
    let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
      (fun i => F.quotient (zf i)) nf eta hupperf
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
  let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
    (fun i => F.quotient (zf i)) nf eta hupperf
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
  have hpositive := normalizedProjectiveCauchy_positiveChart_dense_residual
    (fun i => F.quotient (zf i)) nf eta hupperf relationFree hrelationFree
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
    (nf : ιf → ℕ)
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
    let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
      (fun i => F.quotient (zf i)) nf eta hupperf
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
  let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
    (fun i => F.quotient (zf i)) nf eta hupperf
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
  have habstract : Dense relationFree ∧ relationFree ∈ residual S := by
    have hsource :=
      countablePatterns_actualNevanlinna_relationFree_dense_residual
        row κ ι hCmin F.differentiable_d
        hnoCommon hCp hCc hupperMap' F.background F.contDiffOn_iteratedDeriv_background
        zf hqf_inj' hupperf'
        nf degree orders exponent hexponent hrows eta heta
        (linftyOne eta) hdim
    change Dense relationFree ∧ relationFree ∈ residual S at hsource
    exact hsource
  exact F.normalizedPositiveChart_actualCarrier_relationFree_dense_residual
    zf nf eta hupperf row κ ι degree orders exponent hupperMap
    relationFree habstract.2 (by
      intro w hw n shift coeff
      exact hw n shift coeff)

/-- **All finite shapes, abstract full-rank form.**  One residual frozen-tangent locus carries a
finite admissible row-packet certificate of full coefficient rank for every canonical pattern and
every tuple of distinct complex shifts. -/
theorem allFinitePatterns_abstractCarrier_fullRankWitness_dense_residual
    {Γ : Type} [Countable Γ]
    {ιf : Type} [Fintype ιf] [DecidableEq ιf]
    (hCmin : HasMinimalExponentialType F.c)
    (hnoCommon : ∀ z, ¬ (F.c z = 0 ∧ F.d z = 0))
    {p0 : ℂ} (hCp : F.c p0 = 0) {c0 : ℂ} (hCc : F.c c0 ≠ 0)
    (hupperMap : ∀ z, 0 < z.im → 0 < (F.quotient z).im)
    (zf : ιf → ℂ)
    (hqf_inj : Function.Injective (fun i => F.quotient (zf i)))
    (hupperf : ∀ i, 0 < (F.quotient (zf i)).im)
    (nf : ιf → ℕ)
    (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta] (heta : eta.support.Infinite) :
    let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
      (fun i => F.quotient (zf i)) nf eta hupperf
    let S := LinearMap.ker frozen.toLinearMap
    let fullRank : Set S := {w | ∀ (p : FiniteDifferentialPattern Γ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
      actualNevanlinnaExpandedFullRankWitness
        (row := CarrierPatternRow p) (κ := CarrierPatternMonomial p)
        (ι := CarrierPatternShift p)
        F.background F.amplitude F.quotient p.coefficientDegree p.orders
          (carrierPatternExponent p) eta (linftyOne eta) S w shift}
    Dense fullRank ∧ fullRank ∈ residual S := by
  dsimp only
  let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
    (fun i => F.quotient (zf i)) nf eta hupperf
  let S := LinearMap.ker frozen.toLinearMap
  have hSclosed : IsClosed (S : Set (Lp ℝ (⊤ : ENNReal) eta)) := frozen.isClosed_ker
  letI : CompleteSpace S := hSclosed.completeSpace_coe
  letI : BaireSpace S := by
    set_option synthInstance.maxHeartbeats 100000 in
      infer_instance
  let goodPattern : FiniteDifferentialPattern Γ → Set S := fun p =>
    {w | ∀ shift : InjectiveShiftConfiguration (CarrierPatternShift p),
      actualNevanlinnaExpandedFullRankWitness
        (row := CarrierPatternRow p) (κ := CarrierPatternMonomial p)
        (ι := CarrierPatternShift p)
        F.background F.amplitude F.quotient p.coefficientDegree p.orders
          (carrierPatternExponent p) eta (linftyOne eta) S w shift}
  have hupperMap' : ∀ z, 0 < z.im →
      0 < (projectiveNevanlinnaQuotient F.c F.d z).im := by
    simpa [quotient, projectiveNevanlinnaQuotient] using hupperMap
  have hqf_inj' : Function.Injective
      (fun i => projectiveNevanlinnaQuotient F.c F.d (zf i)) := by
    simpa [quotient, projectiveNevanlinnaQuotient] using hqf_inj
  have hupperf' : ∀ i,
      0 < (projectiveNevanlinnaQuotient F.c F.d (zf i)).im := by
    simpa [quotient, projectiveNevanlinnaQuotient] using hupperf
  have hgoodPattern : ∀ p : FiniteDifferentialPattern Γ,
      Dense (goodPattern p) ∧ goodPattern p ∈ residual S := by
    intro p
    have hsource :=
      global_injectiveShifts_actualNevanlinna_fullRankWitness_dense_residual
        (row := CarrierPatternRow p) (κ := CarrierPatternMonomial p)
        (ι := CarrierPatternShift p)
        hCmin F.differentiable_d
        hnoCommon hCp hCc hupperMap' F.background
        F.contDiffOn_iteratedDeriv_background zf hqf_inj' hupperf' nf
        p.coefficientDegree p.orders (carrierPatternExponent p)
        (carrierPatternExponent_injective p)
        (carrierPattern_rows_strictly_dominate_columns p)
        eta heta (linftyOne eta)
        (carrierPattern_shift_dimension_below_codimension p)
    change Dense (goodPattern p) ∧ goodPattern p ∈ residual S at hsource
    exact hsource
  have hresidual : (⋂ p, goodPattern p) ∈ residual S :=
    countable_iInter_mem.mpr fun p => (hgoodPattern p).2
  have heq : (⋂ p, goodPattern p) = {w | ∀
      (p : FiniteDifferentialPattern Γ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
      actualNevanlinnaExpandedFullRankWitness
        (row := CarrierPatternRow p) (κ := CarrierPatternMonomial p)
        (ι := CarrierPatternShift p)
        F.background F.amplitude F.quotient p.coefficientDegree p.orders
          (carrierPatternExponent p) eta (linftyOne eta) S w shift} := by
    ext w
    simp only [Set.mem_iInter, goodPattern, Set.mem_setOf_eq]
  rw [heq] at hresidual
  exact ⟨dense_of_mem_residual hresidual, hresidual⟩

/-- **All finite shapes in the positive normalized chart, full-rank form.**  Restricting the
simultaneous abstract witness phase to the unit ball preserves density and residuality and makes
every tangent vector a strictly positive mass-one density. -/
theorem allFinitePatterns_positiveAbstractCarrier_fullRankWitness_dense_residual
    {Γ : Type} [Countable Γ]
    {ιf : Type} [Fintype ιf] [DecidableEq ιf]
    (hCmin : HasMinimalExponentialType F.c)
    (hnoCommon : ∀ z, ¬ (F.c z = 0 ∧ F.d z = 0))
    {p0 : ℂ} (hCp : F.c p0 = 0) {c0 : ℂ} (hCc : F.c c0 ≠ 0)
    (hupperMap : ∀ z, 0 < z.im → 0 < (F.quotient z).im)
    (zf : ιf → ℂ)
    (hqf_inj : Function.Injective (fun i => F.quotient (zf i)))
    (hupperf : ∀ i, 0 < (F.quotient (zf i)).im)
    (nf : ιf → ℕ)
    (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta] (heta : eta.support.Infinite) :
    let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
      (fun i => F.quotient (zf i)) nf eta hupperf
    let S := LinearMap.ker frozen.toLinearMap
    let positiveChart : Set S := Metric.ball 0 1
    let fullRank : Set positiveChart := {w | ∀
      (p : FiniteDifferentialPattern Γ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
      actualNevanlinnaExpandedFullRankWitness
        (row := CarrierPatternRow p) (κ := CarrierPatternMonomial p)
        (ι := CarrierPatternShift p)
        F.background F.amplitude F.quotient p.coefficientDegree p.orders
          (carrierPatternExponent p) eta (linftyOne eta) S w.1 shift}
    Dense fullRank ∧ fullRank ∈ residual positiveChart ∧
      ∀ w : positiveChart,
        LinftyStrictlyPositive eta (linftyOne eta + w.1.1) ∧
          ∫ t, (linftyOne eta + w.1.1) t ∂eta = 1 := by
  dsimp only
  let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
    (fun i => F.quotient (zf i)) nf eta hupperf
  let S := LinearMap.ker frozen.toLinearMap
  let abstractFullRank : Set S := {w | ∀
    (p : FiniteDifferentialPattern Γ)
    (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
    actualNevanlinnaExpandedFullRankWitness
      (row := CarrierPatternRow p) (κ := CarrierPatternMonomial p)
      (ι := CarrierPatternShift p)
      F.background F.amplitude F.quotient p.coefficientDegree p.orders
        (carrierPatternExponent p) eta (linftyOne eta) S w shift}
  have habstract : Dense abstractFullRank ∧ abstractFullRank ∈ residual S := by
    simpa [abstractFullRank, frozen, S] using
      (F.allFinitePatterns_abstractCarrier_fullRankWitness_dense_residual
        hCmin hnoCommon hCp hCc hupperMap
        zf hqf_inj hupperf nf eta heta)
  simpa [abstractFullRank, frozen, S] using
    (normalizedProjectiveCauchy_positiveChart_dense_residual
      (fun i => F.quotient (zf i)) nf eta hupperf abstractFullRank habstract.2)

/-- **All finite shapes, abstract carrier form.**  The canonical type of finite differential
patterns is countable.  Intersecting the one-pattern global rank theorems therefore gives one
dense residual tangent locus with coefficient rigidity for every finite differential-pattern
shape at once. -/
theorem allFinitePatterns_abstractCarrier_relationFree_dense_residual
    {Γ : Type} [Countable Γ]
    {ιf : Type} [Fintype ιf] [DecidableEq ιf]
    (hCmin : HasMinimalExponentialType F.c)
    (hnoCommon : ∀ z, ¬ (F.c z = 0 ∧ F.d z = 0))
    {p0 : ℂ} (hCp : F.c p0 = 0) {c0 : ℂ} (hCc : F.c c0 ≠ 0)
    (hupperMap : ∀ z, 0 < z.im → 0 < (F.quotient z).im)
    (zf : ιf → ℂ)
    (hqf_inj : Function.Injective (fun i => F.quotient (zf i)))
    (hupperf : ∀ i, 0 < (F.quotient (zf i)).im)
    (nf : ιf → ℕ)
    (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta] (heta : eta.support.Infinite) :
    let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
      (fun i => F.quotient (zf i)) nf eta hupperf
    let S := LinearMap.ker frozen.toLinearMap
    let relationFree : Set S := {w | ∀ (p : FiniteDifferentialPattern Γ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      actualNevanlinnaExpandedPatternRelationHolds
        (row := CarrierPatternRow p) F.background F.amplitude F.quotient
          p.coefficientDegree p.orders (carrierPatternExponent p) eta (linftyOne eta)
          S w shift coeff →
        ∀ col, coeff col = 0}
    Dense relationFree ∧ relationFree ∈ residual S := by
  dsimp only
  let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
    (fun i => F.quotient (zf i)) nf eta hupperf
  let S := LinearMap.ker frozen.toLinearMap
  let goodPattern' : Set S := {w | ∀ (p : FiniteDifferentialPattern Γ)
    (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
    actualNevanlinnaExpandedFullRankWitness
      (row := CarrierPatternRow p) (κ := CarrierPatternMonomial p)
      (ι := CarrierPatternShift p)
      F.background F.amplitude F.quotient p.coefficientDegree p.orders
        (carrierPatternExponent p) eta (linftyOne eta) S w shift}
  let relationFree : Set S := {w | ∀ (p : FiniteDifferentialPattern Γ)
    (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
    (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
    actualNevanlinnaExpandedPatternRelationHolds
      (row := CarrierPatternRow p) F.background F.amplitude F.quotient
        p.coefficientDegree p.orders (carrierPatternExponent p) eta (linftyOne eta)
        S w shift coeff →
      ∀ col, coeff col = 0}
  have hfull := F.allFinitePatterns_abstractCarrier_fullRankWitness_dense_residual
    (Γ := Γ) hCmin hnoCommon hCp hCc hupperMap zf hqf_inj hupperf nf eta heta
  dsimp only at hfull
  obtain ⟨hdense, hres⟩ := hfull
  have hsubset : goodPattern' ⊆ relationFree := by
    intro w hw p shift coeff hrelation
    exact actualNevanlinnaExpandedPatternRelation_coefficients_eq_zero_of_fullRankWitness
      F.background F.amplitude F.quotient p.coefficientDegree p.orders
      (carrierPatternExponent p) eta (linftyOne eta) S w shift
      (hw p shift) coeff hrelation
  exact ⟨hdense.mono hsubset, Filter.mem_of_superset hres hsubset⟩

/-- **All finite shapes, actual positive-carrier form.**  In the normalized positive chart, a
dense residual family of actual weighted Nevanlinna carrier transforms admits no nonzero relation
of any canonical finite differential-pattern shape. -/
theorem allFinitePatterns_positiveActualCarrier_relationFree_dense_residual
    {Γ : Type} [Countable Γ]
    {ιf : Type} [Fintype ιf] [DecidableEq ιf]
    (hCmin : HasMinimalExponentialType F.c)
    (hnoCommon : ∀ z, ¬ (F.c z = 0 ∧ F.d z = 0))
    {p0 : ℂ} (hCp : F.c p0 = 0) {c0 : ℂ} (hCc : F.c c0 ≠ 0)
    (hupperMap : ∀ z, 0 < z.im → 0 < (F.quotient z).im)
    (zf : ιf → ℂ)
    (hqf_inj : Function.Injective (fun i => F.quotient (zf i)))
    (hupperf : ∀ i, 0 < (F.quotient (zf i)).im)
    (nf : ιf → ℕ)
    (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta] (heta : eta.support.Infinite) :
    let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
      (fun i => F.quotient (zf i)) nf eta hupperf
    let S := LinearMap.ker frozen.toLinearMap
    let positiveChart : Set S := Metric.ball 0 1
    let actualRelationFree : Set positiveChart := {w | ∀
      (p : FiniteDifferentialPattern Γ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      F.weightedBoundaryCarrierExpandedPatternRelationHolds
        (row := CarrierPatternRow p) eta (linftyOne eta + w.1.1)
          p.coefficientDegree p.orders (carrierPatternExponent p) shift coeff →
        ∀ col, coeff col = 0}
    Dense actualRelationFree ∧ actualRelationFree ∈ residual positiveChart ∧
      ∀ w : positiveChart,
        LinftyStrictlyPositive eta (linftyOne eta + w.1.1) ∧
          ∫ t, (linftyOne eta + w.1.1) t ∂eta = 1 := by
  dsimp only
  let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
    (fun i => F.quotient (zf i)) nf eta hupperf
  let S := LinearMap.ker frozen.toLinearMap
  let relationFree : Set S := {w | ∀ (p : FiniteDifferentialPattern Γ)
    (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
    (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
    actualNevanlinnaExpandedPatternRelationHolds
      (row := CarrierPatternRow p) F.background F.amplitude F.quotient
        p.coefficientDegree p.orders (carrierPatternExponent p) eta (linftyOne eta)
        S w shift coeff →
      ∀ col, coeff col = 0}
  have habstract : Dense relationFree ∧ relationFree ∈ residual S := by
    simpa [relationFree, frozen, S] using
      (F.allFinitePatterns_abstractCarrier_relationFree_dense_residual
        hCmin hnoCommon hCp hCc hupperMap
        zf hqf_inj hupperf nf eta heta)
  exact F.normalizedPositiveChart_actualCarrier_relationFree_dense_residual
    zf nf eta hupperf
    (fun p : FiniteDifferentialPattern Γ => CarrierPatternRow p)
    (fun p : FiniteDifferentialPattern Γ => CarrierPatternMonomial p)
    (fun p : FiniteDifferentialPattern Γ => CarrierPatternShift p)
    (fun p => p.coefficientDegree) (fun p => p.orders)
    (fun p => carrierPatternExponent p) hupperMap relationFree habstract.2 (by
      intro w hw p shift coeff
      exact hw p shift coeff)

/-- Avoiding every canonical finite actual-carrier pattern forces the weighted carrier's Cauchy
transform to satisfy no algebraic differential equation on the upper half-plane.  The relation is
only ever evaluated at packet nodes, which lie off the real axis, so the half-plane statement is
what the pattern argument actually gives; global hypertranscendence is the corollary below. -/
theorem not_differentiallyAlgebraicOn_weightedBoundaryCarrierCauchy_of_allFinitePatterns_relationFree
    (eta : Measure (OnePoint ℝ)) [IsFiniteMeasure eta]
    (density : Lp ℝ (⊤ : ENNReal) eta)
    (hfree : ∀ (p : FiniteDifferentialPattern Unit)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      F.weightedBoundaryCarrierExpandedPatternRelationHolds
        (row := CarrierPatternRow p) eta density p.coefficientDegree p.orders
          (carrierPatternExponent p) shift coeff →
        ∀ col, coeff col = 0) :
    ¬ ∃ (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ), P ≠ 0 ∧
        ∀ z : ℂ, 0 < z.im →
          MvPolynomial.eval
            (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ)
              (fun w => ∫ x, ((x : ℂ) - w)⁻¹
                ∂weightedBoundaryCarrier F.base.toBoundaryFamily eta density) z)) P = 0 := by
  intro hDA
  obtain ⟨n, P, hPne, hPzero⟩ := hDA
  let orders : Fin 1 → ℕ := fun _ => n + 1
  let shiftCode : Fin 1 → Unit := fun _ => ()
  have hshiftCode : Function.Injective shiftCode := fun _ _ _ => Subsingleton.elim _ _
  let Q0 : MvPolynomial (Fin (n + 1)) ℂ[X] := reshapeJet n P
  let Q : MvPolynomial (Σ i : Fin 1, Fin (orders i)) ℂ[X] :=
    renameToSingleShiftJets (n + 1) Q0
  let p : FiniteDifferentialPattern Unit :=
    finitePatternOfPolynomial shiftCode hshiftCode orders Q
  let shift0 : InjectiveShiftConfiguration (CarrierPatternShift p) :=
    ⟨fun _ => 0, fun i j _ => p.shiftCode_injective (Subsingleton.elim _ _)⟩
  let patternCoeff : PatternRow p → ℂ :=
    polynomialPatternCoefficientVector shiftCode hshiftCode orders Q
  let coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ :=
    fun col => patternCoeff (Fintype.equivFin (PatternShape p) col)
  let carrierTransform : ℂ → ℂ := fun z =>
    ∫ x, ((x : ℂ) - z)⁻¹
      ∂weightedBoundaryCarrier F.base.toBoundaryFamily eta density
  have hrelation : F.weightedBoundaryCarrierExpandedPatternRelationHolds
      (row := CarrierPatternRow p) eta density p.coefficientDegree p.orders
        (carrierPatternExponent p) shift0 coeff := by
    intro packet hupper r
    let z : ℂ := packet.1 r
    let sigma := Σ i : CarrierPatternShift p, Fin (p.orders i)
    let y : CarrierPatternRow p × Fin (Fintype.card sigma) → ℂ :=
      F.weightedBoundaryCarrierExpandedPacketValue eta density p.orders packet shift0
    let x : sigma → ℂ := fun s =>
      iteratedDeriv s.2 carrierTransform (z + shift0.1 s.1)
    have hy : ∀ s : sigma,
        y (r, Fintype.equivFin sigma s) = x s := by
      intro s
      simp [y, x, z, carrierTransform,
        weightedBoundaryCarrierExpandedPacketValue]
      rw [(Fintype.equivFin sigma).symm_apply_apply s]
    have hprod : ∀ a : CarrierPatternMonomial p,
        (carrierPatternExponent p a).prod
            (fun k e => y (r, k) ^ e) =
          (p.jetExponent a).prod (fun s e => x s ^ e) := by
      intro a
      rw [carrierPatternExponent, Finsupp.equivCongrLeft_apply,
        Finsupp.prod_equivMapDomain]
      apply Finsupp.prod_congr
      intro s hs
      rw [hy s]
    have hsum :
        (∑ col, coeff col *
          expandedDifferentialEvaluationMatrix p.coefficientDegree
            (Fintype.card sigma) packet.1 (carrierPatternExponent p) y r col) =
          ∑ b : PatternRow p,
            patternCoeff b * z ^ patternDegree p b *
              (patternExponent p b).prod (fun s e => x s ^ e) := by
      apply Fintype.sum_equiv (Fintype.equivFin (PatternShape p))
      intro col
      rw [expandedDifferentialEvaluationMatrix_apply, hprod]
      simp [coeff, patternCoeff, patternDegree, patternExponent, z]
      ring
    rw [hsum]
    have hexpand := polynomialPatternCoefficientExpansion
      shiftCode hshiftCode orders Q z x
    rw [hexpand]
    have hrename :
        MvPolynomial.eval x (specializePolynomialCoefficients z Q) =
          MvPolynomial.eval
            (fun j => x ((singleShiftJetEquiv (n + 1)).symm j))
            (specializePolynomialCoefficients z Q0) := by
      simp only [Q, renameToSingleShiftJets, specializePolynomialCoefficients,
        MvPolynomial.eval_map]
      convert
        (MvPolynomial.eval₂_rename (Polynomial.evalRingHom z)
          (singleShiftJetEquiv (n + 1)).symm x Q0) using 1 <;> rfl
    have hx : (fun j => x ((singleShiftJetEquiv (n + 1)).symm j)) =
        fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) carrierTransform z := by
      funext j
      simp [x, p, orders, finitePatternOfPolynomial, shift0, singleShiftJetEquiv]
    calc
      MvPolynomial.eval x (specializePolynomialCoefficients z Q) =
          MvPolynomial.eval
            (fun j => x ((singleShiftJetEquiv (n + 1)).symm j))
            (specializePolynomialCoefficients z Q0) := hrename
      _ = MvPolynomial.eval
          (Fin.cons z (fun j : Fin (n + 1) =>
            iteratedDeriv (j : ℕ) carrierTransform z)) P := by
        rw [hx]
        exact eval_specialize_reshapeJet n z _ P
      _ = 0 := hPzero z (by
        have h0 := hupper (r, (0 : Fin 1))
        simpa [combinedProjectiveRowShiftPacket, shift0, z] using h0)
  have hcoeffZero := hfree p shift0 coeff hrelation
  have hpatternZero : ∀ b : PatternRow p, patternCoeff b = 0 := by
    intro b
    let col : PatternShape p := (Fintype.equivFin (PatternShape p)).symm b
    have hz := hcoeffZero col
    simpa [coeff, col] using hz
  have hQ : Q = 0 :=
    polynomial_eq_zero_of_patternCoefficientVector_eq_zero
      shiftCode hshiftCode orders Q (by
        intro b
        exact hpatternZero b)
  have hQ0 : Q0 = 0 := renameToSingleShiftJets_injective (n + 1) (by
    simpa [Q, orders, renameToSingleShiftJets, MvPolynomial.rename_zero] using hQ)
  have hP : P = 0 := reshapeJet_injective n (by simpa [Q0] using hQ0)
  exact hPne hP

/-- Avoiding every canonical finite actual-carrier pattern forces literal hypertranscendence of
the weighted carrier's Cauchy transform.  A global differential relation is in particular a
relation on the upper half-plane. -/
theorem hypertranscendental_weightedBoundaryCarrierCauchy_of_allFinitePatterns_relationFree
    (eta : Measure (OnePoint ℝ)) [IsFiniteMeasure eta]
    (density : Lp ℝ (⊤ : ENNReal) eta)
    (hfree : ∀ (p : FiniteDifferentialPattern Unit)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      F.weightedBoundaryCarrierExpandedPatternRelationHolds
        (row := CarrierPatternRow p) eta density p.coefficientDegree p.orders
          (carrierPatternExponent p) shift coeff →
        ∀ col, coeff col = 0) :
    Hypertranscendental
      (fun z => ∫ x, ((x : ℂ) - z)⁻¹
        ∂weightedBoundaryCarrier F.base.toBoundaryFamily eta density) := by
  intro hDA
  obtain ⟨n, P, hPne, hPzero⟩ := hDA
  exact F.not_differentiallyAlgebraicOn_weightedBoundaryCarrierCauchy_of_allFinitePatterns_relationFree
    eta density hfree ⟨n, P, hPne, fun z _ => hPzero z⟩

/-- **Residual hypertranscendental Nevanlinna-image law.**  Under the explicit classical
incidence/projection/stratified-avoidance inputs, the positive mass-one chart contains a dense
residual family whose actual weighted-carrier Cauchy transforms are hypertranscendental. -/
theorem positiveActualCarrier_hypertranscendental_dense_residual
    {ιf : Type} [Fintype ιf] [DecidableEq ιf]
    (hCmin : HasMinimalExponentialType F.c)
    (hnoCommon : ∀ z, ¬ (F.c z = 0 ∧ F.d z = 0))
    {p0 : ℂ} (hCp : F.c p0 = 0) {c0 : ℂ} (hCc : F.c c0 ≠ 0)
    (hupperMap : ∀ z, 0 < z.im → 0 < (F.quotient z).im)
    (zf : ιf → ℂ)
    (hqf_inj : Function.Injective (fun i => F.quotient (zf i)))
    (hupperf : ∀ i, 0 < (F.quotient (zf i)).im)
    (nf : ιf → ℕ)
    (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta] (heta : eta.support.Infinite) :
    let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
      (fun i => F.quotient (zf i)) nf eta hupperf
    let S := LinearMap.ker frozen.toLinearMap
    let positiveChart : Set S := Metric.ball 0 1
    let hypertranscendentalCarrier : Set positiveChart := {w |
      Hypertranscendental
        (fun z => ∫ x, ((x : ℂ) - z)⁻¹
          ∂weightedBoundaryCarrier F.base.toBoundaryFamily eta
            (linftyOne eta + w.1.1))}
    Dense hypertranscendentalCarrier ∧
      hypertranscendentalCarrier ∈ residual positiveChart ∧
      ∀ w : positiveChart,
        LinftyStrictlyPositive eta (linftyOne eta + w.1.1) ∧
          ∫ t, (linftyOne eta + w.1.1) t ∂eta = 1 := by
  dsimp only
  let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
    (fun i => F.quotient (zf i)) nf eta hupperf
  let S := LinearMap.ker frozen.toLinearMap
  let positiveChart : Set S := Metric.ball 0 1
  let actualRelationFree : Set positiveChart := {w | ∀
    (p : FiniteDifferentialPattern Unit)
    (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
    (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
    F.weightedBoundaryCarrierExpandedPatternRelationHolds
      (row := CarrierPatternRow p) eta (linftyOne eta + w.1.1)
        p.coefficientDegree p.orders (carrierPatternExponent p) shift coeff →
      ∀ col, coeff col = 0}
  let hypertranscendentalCarrier : Set positiveChart := {w |
    Hypertranscendental
      (fun z => ∫ x, ((x : ℂ) - z)⁻¹
        ∂weightedBoundaryCarrier F.base.toBoundaryFamily eta
          (linftyOne eta + w.1.1))}
  have hpatterns : Dense actualRelationFree ∧
      actualRelationFree ∈ residual positiveChart ∧
      ∀ w : positiveChart,
        LinftyStrictlyPositive eta (linftyOne eta + w.1.1) ∧
          ∫ t, (linftyOne eta + w.1.1) t ∂eta = 1 := by
    simpa [actualRelationFree, frozen, S, positiveChart] using
      (F.allFinitePatterns_positiveActualCarrier_relationFree_dense_residual
        hCmin hnoCommon hCp hCc hupperMap
        zf hqf_inj hupperf nf eta heta)
  have hsubset : actualRelationFree ⊆ hypertranscendentalCarrier := by
    intro w hw
    exact F.hypertranscendental_weightedBoundaryCarrierCauchy_of_allFinitePatterns_relationFree
      eta (linftyOne eta + w.1.1) hw
  exact ⟨hpatterns.1.mono hsubset,
    Filter.mem_of_superset hpatterns.2.1 hsubset, hpatterns.2.2⟩

/-- **Singular-continuous residual HT carrier capstone.**  If the projective parameter law is
singular continuous and its label pullback has the classical null-set property, then every point
of the positive chart is an atomless singular probability solution of the same Hamburger moment
problem, while a dense residual subfamily has hypertranscendental Cauchy transform. -/
theorem positiveSingularContinuousCarrier_hypertranscendental_dense_residual
    {ιf : Type} [Fintype ιf] [DecidableEq ιf]
    (hCmin : HasMinimalExponentialType F.c)
    (hnoCommon : ∀ z, ¬ (F.c z = 0 ∧ F.d z = 0))
    {p0 : ℂ} (hCp : F.c p0 = 0) {c0 : ℂ} (hCc : F.c c0 ≠ 0)
    (hupperMap : ∀ z, 0 < z.im → 0 < (F.quotient z).im)
    (zf : ιf → ℂ)
    (hqf_inj : Function.Injective (fun i => F.quotient (zf i)))
    (hupperf : ∀ i, 0 < (F.quotient (zf i)).im)
    (nf : ιf → ℕ)
    (eta : ProbabilityMeasure (OnePoint ℝ))
    (hetaInfinite : (eta : Measure (OnePoint ℝ)).support.Infinite)
    (hetaSC : eta ∈ projectiveSingularContinuousProbabilityLaws)
    (hnull : ∀ E : Set (OnePoint ℝ), MeasurableSet E →
      (projectiveLebesgueProbability : Measure (OnePoint ℝ)) E = 0 →
      (volume : Measure ℝ)
        (F.base.toBoundaryFamily.matrix.projectiveLabel ⁻¹' E) = 0) :
    let mu : Measure (OnePoint ℝ) := eta
    let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
      (fun i => F.quotient (zf i)) nf mu hupperf
    let S := LinearMap.ker frozen.toLinearMap
    let positiveChart : Set S := Metric.ball 0 1
    let hypertranscendentalCarrier : Set positiveChart := {w |
      Hypertranscendental
        (fun z => ∫ x, ((x : ℂ) - z)⁻¹
          ∂weightedBoundaryCarrier F.base.toBoundaryFamily mu
            (linftyOne mu + w.1.1))}
    Dense hypertranscendentalCarrier ∧
      hypertranscendentalCarrier ∈ residual positiveChart ∧
      ∀ w : positiveChart,
        let density := linftyOne mu + w.1.1
        let carrier := weightedBoundaryCarrier F.base.toBoundaryFamily mu density
        LinftyStrictlyPositive mu density ∧
          ∫ t, density t ∂mu = 1 ∧
          IsProbabilityMeasure carrier ∧ NullSingletonClass carrier ∧
          carrier ⟂ₘ (volume : Measure ℝ) ∧ HasHamburgerMoments s carrier := by
  dsimp only
  let mu : Measure (OnePoint ℝ) := eta
  let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
    (fun i => F.quotient (zf i)) nf mu hupperf
  let S := LinearMap.ker frozen.toLinearMap
  let positiveChart : Set S := Metric.ball 0 1
  let hypertranscendentalCarrier : Set positiveChart := {w |
    Hypertranscendental
      (fun z => ∫ x, ((x : ℂ) - z)⁻¹
        ∂weightedBoundaryCarrier F.base.toBoundaryFamily mu
          (linftyOne mu + w.1.1))}
  letI : IsProbabilityMeasure mu := eta.prop
  have hht : Dense hypertranscendentalCarrier ∧
      hypertranscendentalCarrier ∈ residual positiveChart ∧
      ∀ w : positiveChart,
        LinftyStrictlyPositive mu (linftyOne mu + w.1.1) ∧
          ∫ t, (linftyOne mu + w.1.1) t ∂mu = 1 := by
    simpa [hypertranscendentalCarrier, positiveChart, frozen, S, mu] using
      (F.positiveActualCarrier_hypertranscendental_dense_residual
        hCmin hnoCommon hCp hCc hupperMap
        zf hqf_inj hupperf nf mu hetaInfinite)
  refine ⟨hht.1, hht.2.1, ?_⟩
  intro w
  let density := linftyOne mu + w.1.1
  let carrier := weightedBoundaryCarrier F.base.toBoundaryFamily mu density
  have hstruct := weightedBoundaryCarrier_singularContinuous_probability
    F.base.toBoundaryFamily eta hetaSC hnull density (hht.2.2 w).1 (hht.2.2 w).2
  exact ⟨(hht.2.2 w).1, (hht.2.2 w).2,
    hstruct.1, hstruct.2.1, hstruct.2.2.1, hstruct.2.2.2⟩

end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry
