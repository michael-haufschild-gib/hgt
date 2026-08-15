import GaloisForLFunctions.HTGeometry.GaugeExpandedJetFamily
import GaloisForLFunctions.HTGeometry.GaugeRowPacketAtlas
import GaloisForLFunctions.HTGeometry.NevanlinnaNoncriticalProjectiveCompactPatch
import GaloisForLFunctions.HTGeometry.AnalyticNevanlinnaCarrierRelationFree
import GaloisForLFunctions.HTGeometry.SingularContinuousFullTranslationFamilyFreenessUniversalityLaw

/-!
# Full complex translation freeness on a prescribed divisor

A gauged source `W·exp(g)` has exactly the divisor of `W`, whatever the entire exponent `g`.  This
module runs the compact-patch codimension argument for such sources: over a compact patch of
collision-free complex shifts, finitely many admissible row packets suffice, and for each of them
the full-rank locus of gauges is open and dense.  Baire over a compact exhaustion of the shift
configuration space, and then over the countable set of finite differential patterns, produces one
dense residual set of gauges with a full-rank witness for every finite tuple of distinct complex
shifts at once.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Topology

noncomputable section

variable {row κ ι : Type} [Fintype row] [DecidableEq row] [Fintype κ] [DecidableEq κ]
  [Fintype ι] [DecidableEq ι]

/-- The largest jet order of a finite pattern. -/
def ordersBound (orders : ι → ℕ) : ℕ := Finset.univ.sup orders

omit [DecidableEq ι] in
theorem le_ordersBound (orders : ι → ℕ) (i : ι) : orders i ≤ ordersBound orders :=
  Finset.le_sup (Finset.mem_univ i)

/-- A row packet is admissible for a shift when its whole node family is collision-free, nonzero,
and off the divisor. -/
def gaugeGoodPacket (W : ℂ → ℂ) (packet : InjectiveProjectiveRowPacket row)
    (shift : InjectiveShiftConfiguration ι) : Prop :=
  shift.1 ∈ gaugeGoodCombinedRowPacketAmbientSet W packet

/-- The literal expanded evaluation packet of a gauged source. -/
def gaugeExpandedPacketValue (W : ℂ → ℂ) (orders : ι → ℕ)
    (packet : InjectiveProjectiveRowPacket row) (g : EntireGauge)
    (shift : InjectiveShiftConfiguration ι) :
    row × Fin (Fintype.card (Σ i, Fin (orders i))) → ℂ :=
  reshapeCombinedJetsFinCLM row ι orders
    (fun s => iteratedDeriv s.2.1 (fun w => W w * Complex.exp ((g : C(ℂ, ℂ)) w))
      (combinedProjectiveRowShiftPacket packet shift s.1))

omit [DecidableEq row] [DecidableEq ι] in
theorem gaugeExpandedActualJetFamily_unit (W : ℂ → ℂ) (orders : ι → ℕ)
    (packet : InjectiveProjectiveRowPacket row) (g : EntireGauge)
    (shift : InjectiveShiftConfiguration ι) :
    gaugeExpandedActualJetFamily W (ordersBound orders) orders (le_ordersBound orders)
        (fun _ : Unit => combinedProjectiveRowShiftPacket packet shift) (g, ())
      = gaugeExpandedPacketValue W orders packet g shift := rfl

/-- One admissible packet witnesses full coefficient rank. -/
def gaugeExpandedFullRankWitness (W : ℂ → ℂ) (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (g : EntireGauge) (shift : InjectiveShiftConfiguration ι) : Prop :=
  ∃ packet : InjectiveProjectiveRowPacket row,
    gaugeGoodPacket W packet shift ∧
      Function.Injective
        (expandedDifferentialEvaluationMatrix degree
          (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
          (gaugeExpandedPacketValue W orders packet g shift)).mulVec

/-- A finite polynomial-coefficient relation on the jets of a gauged source. -/
def gaugeExpandedPatternRelationHolds (W : ℂ → ℂ) (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (g : EntireGauge) (shift : InjectiveShiftConfiguration ι)
    (coeff : κ × Fin (degree + 1) → ℂ) : Prop :=
  ∀ packet : InjectiveProjectiveRowPacket row, gaugeGoodPacket W packet shift →
    ∀ r, ∑ col, coeff col *
      expandedDifferentialEvaluationMatrix degree
        (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
        (gaugeExpandedPacketValue W orders packet g shift) r col = 0

omit [DecidableEq row] [DecidableEq κ] [DecidableEq ι] in
theorem gaugeExpandedPatternRelation_coefficients_eq_zero_of_fullRankWitness
    (W : ℂ → ℂ) (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (g : EntireGauge) (shift : InjectiveShiftConfiguration ι)
    (hwitness : gaugeExpandedFullRankWitness (row := row) (κ := κ) W degree orders exponent g shift)
    (coeff : κ × Fin (degree + 1) → ℂ)
    (hrelation : gaugeExpandedPatternRelationHolds (row := row) W degree orders exponent g shift
      coeff) :
    ∀ col, coeff col = 0 := by
  obtain ⟨packet, hgood, hinjective⟩ := hwitness
  have hmul : (expandedDifferentialEvaluationMatrix degree
      (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
      (gaugeExpandedPacketValue W orders packet g shift)).mulVec coeff = 0 := by
    funext r
    simpa [Matrix.mulVec, dotProduct, mul_comm] using hrelation packet hgood r
  have hcoeff : coeff = 0 := hinjective (by simpa using hmul)
  intro col
  exact congrFun hcoeff col

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Set Topology

noncomputable section

variable {row κ ι : Type} [Fintype row] [DecidableEq row] [Fintype κ] [DecidableEq κ]
  [Fintype ι] [DecidableEq ι]

/-- **Compact-patch complete atlas for a gauged source.**  A compact collision-free shift patch has
an open dense set of gauges each of which has an admissible row packet witnessing full
coefficient-uniform rank at every shift of the patch. -/
theorem compact_injectiveShiftPatch_has_dense_completeAtlas_gauge
    (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree < Fintype.card row)
    {W : ℂ → ℂ} (hWd : Differentiable ℂ W) (h0 : ∃ w, W w ≠ 0)
    (Kshift : Set (InjectiveShiftConfiguration ι)) (hKshift : IsCompact Kshift)
    (hdim : Module.finrank ℝ (ι → ℂ) <
      2 * (Fintype.card row - Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    ∃ G : Set EntireGauge, IsOpen G ∧ Dense G ∧
      ∀ g ∈ G, ∀ shift ∈ Kshift,
        gaugeExpandedFullRankWitness (row := row) (κ := κ) W degree orders exponent g shift := by
  classical
  have hWa : AnalyticOnNhd ℂ W Set.univ := hWd.differentiableOn.analyticOnNhd isOpen_univ
  obtain ⟨n, packets, pieces, hcover, hpiecesCompact, hpiecesChart⟩ :=
    compact_injectiveShiftPatch_finite_gaugeGoodCombinedRowPacket_refinement
      (row := row) (ι := ι) hWa hWd.continuous h0 hKshift
  set m := ordersBound orders with hmdef
  set hm := le_ordersBound orders with hhm
  set nodes : Fin n → (ι → ℂ) → row × ι → ℂ := fun j h x => (packets j).1 x.1 + h x.2 with hnodes
  set ambientPiece : Fin n → Set (ι → ℂ) := fun j => Subtype.val '' pieces j with hambient
  set family : Fin n → (EntireGauge × (ι → ℂ)) →
      row × Fin (Fintype.card (Σ i, Fin (orders i))) → ℂ := fun j =>
    gaugeExpandedActualJetFamily W m orders hm (nodes j) with hfamily
  set good : Fin n → Set EntireGauge := fun j =>
    compactConfigurationAvoidance (family j)
      (expandedDifferentialEvaluationRankDefect degree
        (Fintype.card (Σ i, Fin (orders i))) (packets j).1 exponent)
      (ambientPiece j) with hgooddef
  have hnodesSmooth : ∀ j, ContDiff ℝ ⊤ (nodes j) := by
    intro j
    rw [contDiff_pi]
    intro x
    exact contDiff_const.add (contDiff_apply ℝ ℂ x.2)
  have hfamilyCont : ∀ j, Continuous (family j) := fun j =>
    continuous_gaugeExpandedActualJetFamily hWd m orders hm (hnodesSmooth j).continuous
  have hKj : ∀ j, IsCompact (ambientPiece j) := fun j =>
    (hpiecesCompact j).image continuous_subtype_val
  have hKjUj : ∀ j, ambientPiece j ⊆ gaugeGoodCombinedRowPacketAmbientSet (ι := ι) W (packets j) := by
    rintro j _ ⟨shiftCfg, hpiece, rfl⟩
    exact hpiecesChart j hpiece
  have hgood : ∀ j, Dense (good j) ∧ IsOpen (good j) := by
    intro j
    constructor
    · have := compact_gaugeExpandedActualEvaluation_avoidance_dense
        (row := row) (κ := κ) (ι := ι) (H := ι → ℂ)
        degree orders m hm (packets j).1 (packets j).2 exponent hexponent hrows hWd
        (nodes j) (hnodesSmooth j)
        (gaugeGoodCombinedRowPacketAmbientSet (ι := ι) W (packets j)) (ambientPiece j)
        (gaugeGoodCombinedRowPacketAmbientSet_isOpen (ι := ι) hWd.continuous (packets j))
        (hKjUj j)
        (fun h hh => injective_of_mem_gaugeGoodCombinedRowPacketAmbientSet hh)
        (fun h hh x => ne_zero_of_mem_gaugeGoodCombinedRowPacketAmbientSet hh x)
        (fun h hh x => source_ne_zero_of_mem_gaugeGoodCombinedRowPacketAmbientSet hh x)
        hdim
      exact this
    · exact compactConfigurationAvoidance_isOpen (family j) (hfamilyCont j) _
        (expandedDifferentialEvaluationRankDefect_isClosed degree
          (Fintype.card (Σ i, Fin (orders i))) (packets j).1 exponent)
        (ambientPiece j) (hKj j)
  refine ⟨⋂ j, good j, isOpen_iInter_of_finite fun j => (hgood j).2,
    dense_iInter_of_finite_isOpen good (fun j => (hgood j).2) (fun j => (hgood j).1), ?_⟩
  intro g hg shift hshift
  obtain ⟨j, hjpiece⟩ := Set.mem_iUnion.mp (hcover hshift)
  refine ⟨packets j, hpiecesChart j hjpiece, ?_⟩
  have hjgood := Set.mem_iInter.mp hg j
  have havoid := hjgood shift.1 ⟨shift, hjpiece, rfl⟩
  have hinjective : Function.Injective
      (expandedDifferentialEvaluationMatrix degree
        (Fintype.card (Σ i, Fin (orders i))) (packets j).1 exponent
        (family j (g, shift.1))).mulVec := by
    simpa only [mem_expandedDifferentialEvaluationRankDefect_iff, not_not] using havoid
  exact hinjective

/-- **All-shift full-rank law for one finite differential pattern.** -/
theorem global_injectiveShifts_gaugeExpandedFullRankWitness_dense_residual
    (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree < Fintype.card row)
    {W : ℂ → ℂ} (hWd : Differentiable ℂ W) (h0 : ∃ w, W w ≠ 0)
    (hdim : Module.finrank ℝ (ι → ℂ) <
      2 * (Fintype.card row - Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    let good : Set EntireGauge := {g |
      ∀ shift : InjectiveShiftConfiguration ι,
        gaugeExpandedFullRankWitness (row := row) (κ := κ) W degree orders exponent g shift}
    Dense good ∧ good ∈ residual EntireGauge := by
  dsimp only
  apply globalWitness_dense_residual_of_sigmaCompact
    (fun g (shift : InjectiveShiftConfiguration ι) =>
      gaugeExpandedFullRankWitness (row := row) (κ := κ) W degree orders exponent g shift)
  intro Kshift hKshift
  exact compact_injectiveShiftPatch_has_dense_completeAtlas_gauge degree orders exponent
    hexponent hrows hWd h0 Kshift hKshift hdim

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Set Topology
open ClassicalAnalyticNevanlinnaCarrierFamily

noncomputable section

/-! ### All finite patterns at once -/

theorem allFinitePatterns_gaugeExpandedFullRankWitness_dense_residual
    {Γ : Type} [Countable Γ] {W : ℂ → ℂ} (hWd : Differentiable ℂ W) (h0 : ∃ w, W w ≠ 0) :
    let fullRank : Set EntireGauge := {g |
      ∀ (p : FiniteDifferentialPattern Γ)
        (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
        gaugeExpandedFullRankWitness (row := CarrierPatternRow p)
          (κ := CarrierPatternMonomial p) W p.coefficientDegree p.orders
          (carrierPatternExponent p) g shift}
    Dense fullRank ∧ fullRank ∈ residual EntireGauge := by
  dsimp only
  let goodPattern : FiniteDifferentialPattern Γ → Set EntireGauge := fun p =>
    {g | ∀ shift : InjectiveShiftConfiguration (CarrierPatternShift p),
      gaugeExpandedFullRankWitness (row := CarrierPatternRow p)
        (κ := CarrierPatternMonomial p) W p.coefficientDegree p.orders
        (carrierPatternExponent p) g shift}
  have hgoodPattern : ∀ p : FiniteDifferentialPattern Γ,
      Dense (goodPattern p) ∧ goodPattern p ∈ residual EntireGauge := by
    intro p
    have hsource := global_injectiveShifts_gaugeExpandedFullRankWitness_dense_residual
      (row := CarrierPatternRow p) (κ := CarrierPatternMonomial p) (ι := CarrierPatternShift p)
      p.coefficientDegree p.orders (carrierPatternExponent p)
      (carrierPatternExponent_injective p)
      (carrierPattern_rows_strictly_dominate_columns p) hWd h0
      (carrierPattern_shift_dimension_below_codimension p)
    exact hsource
  have hresidual : (⋂ p, goodPattern p) ∈ residual EntireGauge :=
    countable_iInter_mem.mpr fun p => (hgoodPattern p).2
  have heq : (⋂ p, goodPattern p) = {g |
      ∀ (p : FiniteDifferentialPattern Γ)
        (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
        gaugeExpandedFullRankWitness (row := CarrierPatternRow p)
          (κ := CarrierPatternMonomial p) W p.coefficientDegree p.orders
          (carrierPatternExponent p) g shift} := by
    ext g
    simp only [Set.mem_iInter, goodPattern, Set.mem_setOf_eq]
  rw [heq] at hresidual
  exact ⟨dense_of_mem_residual hresidual, hresidual⟩

theorem allFinitePatterns_gaugeExpandedRelationFree_dense_residual
    {Γ : Type} [Countable Γ] {W : ℂ → ℂ} (hWd : Differentiable ℂ W) (h0 : ∃ w, W w ≠ 0) :
    let relationFree : Set EntireGauge := {g |
      ∀ (p : FiniteDifferentialPattern Γ)
        (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
        (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
        gaugeExpandedPatternRelationHolds (row := CarrierPatternRow p)
          W p.coefficientDegree p.orders (carrierPatternExponent p) g shift coeff →
        ∀ col, coeff col = 0}
    Dense relationFree ∧ relationFree ∈ residual EntireGauge := by
  dsimp only
  let fullRank : Set EntireGauge := {g |
    ∀ (p : FiniteDifferentialPattern Γ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
      gaugeExpandedFullRankWitness (row := CarrierPatternRow p)
        (κ := CarrierPatternMonomial p) W p.coefficientDegree p.orders
        (carrierPatternExponent p) g shift}
  let relationFree : Set EntireGauge := {g |
    ∀ (p : FiniteDifferentialPattern Γ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      gaugeExpandedPatternRelationHolds (row := CarrierPatternRow p)
        W p.coefficientDegree p.orders (carrierPatternExponent p) g shift coeff →
      ∀ col, coeff col = 0}
  have hfull : Dense fullRank ∧ fullRank ∈ residual EntireGauge := by
    simpa only [fullRank] using
      (allFinitePatterns_gaugeExpandedFullRankWitness_dense_residual (Γ := Γ) hWd h0)
  have hsubset : fullRank ⊆ relationFree := by
    intro g hg p shift coeff hrelation
    exact gaugeExpandedPatternRelation_coefficients_eq_zero_of_fullRankWitness
      W p.coefficientDegree p.orders (carrierPatternExponent p) g shift (hg p shift) coeff
      hrelation
  exact ⟨hfull.1.mono hsubset, Filter.mem_of_superset hfull.2 hsubset⟩

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Set Topology
open ClassicalAnalyticNevanlinnaCarrierFamily

noncomputable section

/-! ### Descent to differential-algebraic independence -/

theorem gaugeExpandedPacketValue_eq_familyJetVec
    {mm nn : ℕ} {row : Type} [Fintype row] [DecidableEq row]
    {W : ℂ → ℂ} (packet : InjectiveProjectiveRowPacket row) (g : EntireGauge)
    (shift : InjectiveShiftConfiguration (Fin mm))
    (r : row) (t : Σ _ : Fin mm, Fin (nn + 1)) :
    gaugeExpandedPacketValue W (fun _ : Fin mm => nn + 1) packet g shift
        (r, Fintype.equivFin (Σ _ : Fin mm, Fin (nn + 1)) t)
      = familyJetVec (n := nn)
          (fun i w => W (w + shift.1 i) * Complex.exp ((g : C(ℂ, ℂ)) (w + shift.1 i)))
          (packet.1 r) (Sum.inr (t.1, t.2)) := by
  show iteratedDeriv _ _ _ = _
  rw [(Fintype.equivFin (Σ _ : Fin mm, Fin (nn + 1))).symm_apply_apply t]
  have hrhs : familyJetVec (n := nn)
      (fun i w => W (w + shift.1 i) * Complex.exp ((g : C(ℂ, ℂ)) (w + shift.1 i)))
      (packet.1 r) (Sum.inr (t.1, t.2))
      = iteratedDeriv (t.2 : ℕ)
        (fun w => (fun u => W u * Complex.exp ((g : C(ℂ, ℂ)) u)) (w + shift.1 t.1))
        (packet.1 r) := rfl
  rw [hrhs, iteratedDeriv_comp_add_right]
  rfl

/-- **No finite family of distinct complex translates of a relation-free gauged source satisfies an
algebraic differential relation over the rational functions.** -/
theorem not_familyDifferentiallyAlgebraicOn_gaugeCarrier_of_relationFree
    (mm : ℕ) {W : ℂ → ℂ} (g : EntireGauge)
    (hfree : ∀ (p : FiniteDifferentialPattern ℕ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      gaugeExpandedPatternRelationHolds (row := CarrierPatternRow p)
        W p.coefficientDegree p.orders (carrierPatternExponent p) g shift coeff →
      ∀ col, coeff col = 0)
    (shift : InjectiveShiftConfiguration (Fin mm)) :
    ¬ FamilyDifferentiallyAlgebraicOn
      (fun i z => W (z + shift.1 i) * Complex.exp ((g : C(ℂ, ℂ)) (z + shift.1 i))) Set.univ := by
  intro hDA
  obtain ⟨nn, P, hPne, hPzero⟩ := hDA
  let shiftCode : Fin mm → ℕ := naturalFamilyShiftCode mm
  have hshiftCode : Function.Injective shiftCode := naturalFamilyShiftCode_injective mm
  let Q : MvPolynomial (Σ _ : Fin mm, Fin (nn + 1)) (Polynomial ℂ) :=
    renameToFamilyShiftJets mm nn (familyReshapeJet mm nn P)
  let p : FiniteDifferentialPattern ℕ := codedFamilyPatternOfRelation shiftCode hshiftCode P
  let shiftP : InjectiveShiftConfiguration (CarrierPatternShift p) := ⟨shift.1, shift.2⟩
  let patternCoeff : PatternRow p → ℂ :=
    polynomialPatternCoefficientVector shiftCode hshiftCode (familyOrders mm nn) Q
  let coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ :=
    fun col => patternCoeff (Fintype.equivFin (PatternShape p) col)
  have hrelation : gaugeExpandedPatternRelationHolds (row := CarrierPatternRow p)
      W p.coefficientDegree p.orders (carrierPatternExponent p) g shiftP coeff := by
    intro packet _ r
    let z : ℂ := packet.1 r
    let sigma := Σ i : CarrierPatternShift p, Fin (p.orders i)
    let y : CarrierPatternRow p × Fin (Fintype.card sigma) → ℂ :=
      gaugeExpandedPacketValue W p.orders packet g shiftP
    let x : sigma → ℂ := fun t =>
      familyJetVec (n := nn)
        (fun i w => W (w + shift.1 i) * Complex.exp ((g : C(ℂ, ℂ)) (w + shift.1 i)))
        z (Sum.inr (t.1, t.2))
    have hy : ∀ t : sigma, y (r, Fintype.equivFin sigma t) = x t := by
      intro t
      simpa [y, x, p, Q, shiftP, shiftCode, codedFamilyPatternOfRelation, familyOrders] using!
        (gaugeExpandedPacketValue_eq_familyJetVec packet g shift r
          (⟨t.1, t.2⟩ : Σ _ : Fin mm, Fin (nn + 1)))
    have hprod : ∀ a : CarrierPatternMonomial p,
        (carrierPatternExponent p a).prod (fun k e => y (r, k) ^ e)
          = (p.jetExponent a).prod (fun t e => x t ^ e) := by
      intro a
      rw [carrierPatternExponent, Finsupp.equivCongrLeft_apply, Finsupp.prod_equivMapDomain]
      apply Finsupp.prod_congr
      intro t _
      rw [hy t]
    have hsum : (∑ col, coeff col *
          expandedDifferentialEvaluationMatrix p.coefficientDegree
            (Fintype.card sigma) packet.1 (carrierPatternExponent p) y r col)
        = ∑ b : PatternRow p, patternCoeff b * z ^ patternDegree p b *
            (patternExponent p b).prod (fun t e => x t ^ e) := by
      apply Fintype.sum_equiv (Fintype.equivFin (PatternShape p))
      intro col
      rw [expandedDifferentialEvaluationMatrix_apply, hprod]
      simp [coeff, patternCoeff, patternDegree, patternExponent, z]
      ring
    rw [hsum]
    calc
      (∑ b : PatternRow p, patternCoeff b * z ^ patternDegree p b *
          (patternExponent p b).prod (fun t e => x t ^ e))
          = MvPolynomial.eval (Sum.elim (fun _ => z) fun q => x ⟨q.1, q.2⟩) P := by
        simpa [patternCoeff, p, Q] using!
          (codedFamilyPatternExpansion_eq_eval shiftCode hshiftCode P z x)
      _ = 0 := hPzero z (Set.mem_univ z)
  have hcoeffZero := hfree p shiftP coeff hrelation
  have hpatternZero : ∀ b : PatternRow p, patternCoeff b = 0 := by
    intro b
    have hz := hcoeffZero ((Fintype.equivFin (PatternShape p)).symm b)
    simpa [coeff] using hz
  have hP : P = 0 :=
    familyJetRelation_eq_zero_of_codedPatternCoefficients_zero shiftCode hshiftCode P
      (fun b => hpatternZero b)
  exact hPne hP

/-! ### The capstone -/

/-- **Full complex translation freeness on a prescribed divisor.**  For every nonzero entire `W`, a
dense residual set of entire gauges makes every finite family of distinct complex translates of
`W·exp(g)` differentially algebraically independent over the rational functions, while every such
source has exactly the divisor of `W`. -/
theorem fixedDivisor_fullTranslationFreeness_denseResidual
    {W : ℂ → ℂ} (hWd : Differentiable ℂ W) (h0 : ∃ w, W w ≠ 0) :
    let universalPhase : Set EntireGauge := {g |
      ∀ (p : FiniteDifferentialPattern ℕ)
        (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
        (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
        gaugeExpandedPatternRelationHolds (row := CarrierPatternRow p)
          W p.coefficientDegree p.orders (carrierPatternExponent p) g shift coeff →
        ∀ col, coeff col = 0}
    Dense universalPhase ∧ universalPhase ∈ residual EntireGauge ∧
      (∀ (g : EntireGauge) (z : ℂ),
        W z * Complex.exp ((g : C(ℂ, ℂ)) z) = 0 ↔ W z = 0) ∧
      (∀ g : EntireGauge, Differentiable ℂ
        (fun z => W z * Complex.exp ((g : C(ℂ, ℂ)) z))) ∧
      ∀ g ∈ universalPhase, ∀ (mm : ℕ) (shift : InjectiveShiftConfiguration (Fin mm)),
        ¬ FamilyDifferentiallyAlgebraicOn
          (fun i z => W (z + shift.1 i) * Complex.exp ((g : C(ℂ, ℂ)) (z + shift.1 i)))
          Set.univ := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (allFinitePatterns_gaugeExpandedRelationFree_dense_residual (Γ := ℕ) hWd h0).1
  · exact (allFinitePatterns_gaugeExpandedRelationFree_dense_residual (Γ := ℕ) hWd h0).2
  · intro g z
    constructor
    · intro hzero
      rcases mul_eq_zero.mp hzero with h | h
      · exact h
      · exact absurd h (Complex.exp_ne_zero _)
    · intro hzero
      rw [hzero, zero_mul]
  · intro g
    exact hWd.mul g.2.cexp
  · intro g hg mm shift
    exact not_familyDifferentiallyAlgebraicOn_gaugeCarrier_of_relationFree mm g hg shift

end

end GaloisForLFunctions.HTGeometry
