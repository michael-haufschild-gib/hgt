import GaloisForLFunctions.HTGeometry.MovingDivisorEvenJetSubmersion
import GaloisForLFunctions.HTGeometry.MovingEvenCanonicalFullTranslationFreeness

/-!
# Full-translation freeness for the even carrier of a moving divisor

The Baire intersection over every finite differential pattern and every injective shift
configuration leaves a dense residual set of bounded parameters whose symmetric carrier has a
differentially algebraically independent full complex translation family.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Topology Filter
open ClassicalAnalyticNevanlinnaCarrierFamily
open scoped ComplexConjugate

noncomputable section

namespace MovingDivisor

def evenActualJetFamily (Dv : MovingDivisor)
    {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype ι]
    (nodes : H → ι → ℂ) (n : ι → ℕ)
    (p : BoundedRealSequence × H) :
    (Σ i, Fin (n i)) → ℂ :=
  evenJetExtraction n
    (Dv.actualJetFamily
      (movingEvenCanonicalDoubledNodes nodes)
      (evenUpperNodeOrders n) p)

theorem evenActualJetFamily_apply (Dv : MovingDivisor)
    {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype ι]
    (nodes : H → ι → ℂ) (n : ι → ℕ)
    (p : BoundedRealSequence × H)
    (hupper : ∀ i, 0 < (nodes p.2 i).im)
    (s : Σ i, Fin (n i)) :
    Dv.evenActualJetFamily nodes n p s =
      iteratedDeriv s.2.1
        (Dv.evenCarrierB p.1) (nodes p.2 s.1) := by
  rw [Dv.iteratedDeriv_evenCarrierB _ _ (hupper s.1)]
  rfl

theorem continuousOn_evenActualJetFamily (Dv : MovingDivisor)
    {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype ι]
    (nodes : H → ι → ℂ) (hnodes : Continuous nodes)
    (n : ι → ℕ) (U : Set H)
    (hupper : ∀ h ∈ U, ∀ i, 0 < (nodes h i).im) :
    ContinuousOn
      (Dv.evenActualJetFamily nodes n)
      (Set.univ ×ˢ U) := by
  exact (evenJetExtraction n).continuous.comp_continuousOn
    (Dv.continuousOn_actualJetFamily
      (movingEvenCanonicalDoubledNodes nodes)
      (continuous_movingEvenCanonicalDoubledNodes nodes hnodes)
      (evenUpperNodeOrders n) U
      (fun h hh => evenUpperNodePair_upper (nodes h) (hupper h hh)))

def evenExpandedActualJetFamily (Dv : MovingDivisor)
    {H row ι : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype row] [Fintype ι]
    (orders : ι → ℕ) (nodes : H → row × ι → ℂ)
    (p : BoundedRealSequence × H) :
    row × Fin (Fintype.card (Σ i, Fin (orders i))) → ℂ :=
  reshapeCombinedJetsFinCLM row ι orders
    (Dv.evenActualJetFamily nodes
      (fun x : row × ι => orders x.2) p)

theorem continuousOn_evenExpandedActualJetFamily (Dv : MovingDivisor)
    {H row ι : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype row] [Fintype ι]
    (orders : ι → ℕ) (nodes : H → row × ι → ℂ)
    (hnodes : Continuous nodes) (U : Set H)
    (hupper : ∀ h ∈ U, ∀ x, 0 < (nodes h x).im) :
    ContinuousOn
      (Dv.evenExpandedActualJetFamily orders nodes)
      (Set.univ ×ˢ U) :=
  (reshapeCombinedJetsFinCLM row ι orders).continuous.comp_continuousOn
    (Dv.continuousOn_evenActualJetFamily
      nodes hnodes (fun x : row × ι => orders x.2) U hupper)

def evenFiniteJointJetFamily (Dv : MovingDivisor)
    {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype ι]
    (nodes : H → ι → ℂ) (n : ι → ℕ)
    (θ : BoundedRealSequence)
    (p : (Fin (movingCanonicalLocationProbeCard
      (evenUpperNodeOrders n)) → ℝ) × H) :
    (Σ i, Fin (n i)) → ℂ :=
  evenJetExtraction n
    (Dv.finiteJointJetFamily
      (movingEvenCanonicalDoubledNodes nodes)
      (evenUpperNodeOrders n) θ p)

theorem contDiffOn_evenFiniteJointJetFamily (Dv : MovingDivisor)
    {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype ι]
    (nodes : H → ι → ℂ) (hnodes : ContDiff ℝ ⊤ nodes)
    (n : ι → ℕ) (θ : BoundedRealSequence)
    (U : Set H) (hupper : ∀ h ∈ U, ∀ i, 0 < (nodes h i).im) :
    ContDiffOn ℝ ⊤
      (Dv.evenFiniteJointJetFamily nodes n θ)
      (Set.univ ×ˢ U) := by
  exact (evenJetExtraction n).contDiff.comp_contDiffOn
    (Dv.contDiffOn_finiteJointJetFamily
      (movingEvenCanonicalDoubledNodes nodes)
      (contDiff_movingEvenCanonicalDoubledNodes nodes hnodes)
      (evenUpperNodeOrders n) θ U
      (fun h hh => evenUpperNodePair_upper (nodes h) (hupper h hh)))

def evenExpandedJetFamily (Dv : MovingDivisor)
    {H row ι : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype row] [Fintype ι]
    (orders : ι → ℕ) (nodes : H → row × ι → ℂ)
    (θ : BoundedRealSequence)
    (p :
      (Fin (movingCanonicalLocationProbeCard
        (evenUpperNodeOrders
          (fun x : row × ι => orders x.2))) → ℝ) × H) :
    row × Fin (Fintype.card (Σ i, Fin (orders i))) → ℂ :=
  reshapeCombinedJetsFinCLM row ι orders
    (Dv.evenFiniteJointJetFamily nodes
      (fun x : row × ι => orders x.2) θ p)

theorem contDiffOn_evenExpandedJetFamily (Dv : MovingDivisor)
    {H row ι : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype row] [Fintype ι]
    (orders : ι → ℕ) (nodes : H → row × ι → ℂ)
    (hnodes : ContDiff ℝ ⊤ nodes)
    (θ : BoundedRealSequence) (U : Set H)
    (hupper : ∀ h ∈ U, ∀ x, 0 < (nodes h x).im) :
    ContDiffOn ℝ ⊤
      (Dv.evenExpandedJetFamily orders nodes θ)
      (Set.univ ×ˢ U) := by
  exact (reshapeCombinedJetsFinCLM row ι orders).contDiff.comp_contDiffOn
    (Dv.contDiffOn_evenFiniteJointJetFamily
      nodes hnodes (fun x : row × ι => orders x.2) θ U hupper)

theorem fderiv_evenExpandedJetFamily_probe_surjective (Dv : MovingDivisor)
    {H row ι : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype row] [Fintype ι]
    [DecidableEq row] [DecidableEq ι]
    (orders : ι → ℕ) (nodes : H → row × ι → ℂ)
    (θ : BoundedRealSequence)
    (p : Fin (movingCanonicalLocationProbeCard
      (evenUpperNodeOrders
        (fun x : row × ι => orders x.2))) → ℝ)
    (h : H) (hsep : EvenNodeSeparated (nodes h))
    (hupper : ∀ x, 0 < (nodes h x).im) :
    Function.Surjective
      (fderiv ℝ
        (fun v => Dv.evenExpandedJetFamily
          orders nodes θ (v, h)) p) := by
  let nodeOrders : row × ι → ℕ := fun x => orders x.2
  have hcanonical :=
    Dv.finiteActualJetFamily_hasFDerivAt
      (evenUpperNodePair (nodes h))
      (evenUpperNodePair_upper (nodes h) hupper)
      (evenUpperNodeOrders nodeOrders) θ p
  have hactual : HasFDerivAt
      (Dv.evenFiniteActualJetFamily
        (nodes h) nodeOrders θ)
      ((evenJetExtraction nodeOrders).comp
        (Dv.finiteParameterJetCLM
          (evenUpperNodePair (nodes h))
          (evenUpperNodeOrders nodeOrders)
          (movingCanonicalFiniteChart
            (movingCanonicalLocationProbeCard
              (evenUpperNodeOrders nodeOrders)) θ p)))
      p :=
    (evenJetExtraction nodeOrders).hasFDerivAt.comp p hcanonical
  have hreshape : HasNormedFDerivAt
      (reshapeCombinedJetsFinCLM row ι orders)
      (reshapeCombinedJetsFinCLM row ι orders)
      (Dv.evenFiniteActualJetFamily
        (nodes h) nodeOrders θ p) :=
    (reshapeCombinedJetsFinCLM row ι orders).hasFDerivAt
  have hcomp := hreshape.comp p hactual
  have hfun :
      (fun v => Dv.evenExpandedJetFamily
        orders nodes θ (v, h)) =
        (reshapeCombinedJetsFinCLM row ι orders) ∘
          Dv.evenFiniteActualJetFamily
            (nodes h) nodeOrders θ := by
    funext v
    rfl
  have hderiv :
      fderiv ℝ
        (fun v => Dv.evenExpandedJetFamily
          orders nodes θ (v, h)) p =
        (reshapeCombinedJetsFinCLM row ι orders).comp
          (fderiv ℝ
            (Dv.evenFiniteActualJetFamily
              (nodes h) nodeOrders θ) p) := by
    rw [hfun]
    rw [hactual.fderiv]
    exact hcomp.fderiv
  rw [hderiv]
  exact (reshapeCombinedJetsFinCLM_surjective row ι orders).comp
    (Dv.fderiv_evenFiniteActualJetFamily_surjective
      (nodes h) hsep hupper nodeOrders θ p)

theorem compact_evenExpandedEvaluation_avoidance_dense (Dv : MovingDivisor)
    {H row κ ι : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (degree : ℕ) (orders : ι → ℕ)
    (z : row → ℂ) (hz : Function.Injective z)
    (exponent :
      κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree <
      Fintype.card row)
    (nodes : H → row × ι → ℂ) (hnodes : ContDiff ℝ ⊤ nodes)
    (U K : Set H) (hU : IsOpen U) (hKU : K ⊆ U)
    (hsep : ∀ h ∈ U, EvenNodeSeparated (nodes h))
    (hupper : ∀ h ∈ U, ∀ x, 0 < (nodes h x).im)
    (θ : BoundedRealSequence)
    (hdim : Module.finrank ℝ H <
      2 * (Fintype.card row -
        Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    Dense
      (compactConfigurationAvoidance
        (Dv.evenExpandedJetFamily orders nodes θ)
        (expandedDifferentialEvaluationRankDefect degree
          (Fintype.card (Σ i, Fin (orders i))) z exponent)
        K) := by
  apply expandedEvaluation_compactPatchAvoidance_dense
    degree (Fintype.card (Σ i, Fin (orders i)))
      z hz exponent hexponent hrows
      (Dv.evenExpandedJetFamily orders nodes θ)
      U K hU hKU
  · exact Dv.contDiffOn_evenExpandedJetFamily
      orders nodes hnodes θ U hupper
  · intro p h hh
    exact Dv.fderiv_evenExpandedJetFamily_probe_surjective
      orders nodes θ p h (hsep h hh) (hupper h hh)
  · exact hdim

theorem compact_evenExpandedActualEvaluation_avoidance_dense (Dv : MovingDivisor)
    {H row κ ι : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (degree : ℕ) (orders : ι → ℕ)
    (z : row → ℂ) (hz : Function.Injective z)
    (exponent :
      κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree <
      Fintype.card row)
    (nodes : H → row × ι → ℂ) (hnodes : ContDiff ℝ ⊤ nodes)
    (U K : Set H) (hU : IsOpen U) (hKU : K ⊆ U)
    (hsep : ∀ h ∈ U, EvenNodeSeparated (nodes h))
    (hupper : ∀ h ∈ U, ∀ x, 0 < (nodes h x).im)
    (hdim : Module.finrank ℝ H <
      2 * (Fintype.card row -
        Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    Dense
      (compactConfigurationAvoidance
        (Dv.evenExpandedActualJetFamily orders nodes)
        (expandedDifferentialEvaluationRankDefect degree
          (Fintype.card (Σ i, Fin (orders i))) z exponent)
        K) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro θ
  rw [mem_closure_iff]
  intro V hVopen hθV
  let D := movingCanonicalLocationProbeCard
    (evenUpperNodeOrders (fun x : row × ι => orders x.2))
  let chart : (Fin D → ℝ) → BoundedRealSequence :=
    movingCanonicalFiniteChart D θ
  have hchart : Continuous chart := by
    exact (contDiff_movingCanonicalFiniteChart D θ).continuous
  have hchartZero : chart 0 = θ := by
    exact finiteChartB_zero D θ
  have hpreOpen : IsOpen (chart ⁻¹' V) :=
    hVopen.preimage hchart
  have hpreNonempty : (chart ⁻¹' V).Nonempty := by
    exact ⟨0, by simpa [hchartZero] using hθV⟩
  have hdenseFinite :=
    Dv.compact_evenExpandedEvaluation_avoidance_dense
      degree orders z hz exponent hexponent hrows nodes hnodes
      U K hU hKU hsep hupper θ hdim
  obtain ⟨p, hpgood, hpV⟩ :=
    hdenseFinite.exists_mem_open hpreOpen hpreNonempty
  refine ⟨chart p, hpV, ?_⟩
  intro h hh
  exact hpgood h hh

def evenExpandedPacketValue (Dv : MovingDivisor)
    {row ι : Type} [Fintype row] [DecidableEq row]
    [Fintype ι] [DecidableEq ι]
    (orders : ι → ℕ) (packet : InjectiveProjectiveRowPacket row)
    (θ : BoundedRealSequence) (shift : InjectiveShiftConfiguration ι) :
    row × Fin (Fintype.card (Σ i, Fin (orders i))) → ℂ :=
  reshapeCombinedJetsFinCLM row ι orders
    (Dv.evenActualJetFamily
      (fun _ : Unit =>
        combinedProjectiveRowShiftPacket packet shift)
      (fun x : row × ι => orders x.2) (θ, ()))

theorem evenExpandedPacketValue_apply (Dv : MovingDivisor)
    {row ι : Type} [Fintype row] [DecidableEq row]
    [Fintype ι] [DecidableEq ι]
    (orders : ι → ℕ) (packet : InjectiveProjectiveRowPacket row)
    (θ : BoundedRealSequence) (shift : InjectiveShiftConfiguration ι)
    (hupper : ∀ x,
      0 < (combinedProjectiveRowShiftPacket packet shift x).im)
    (r : row) (j : Fin (Fintype.card (Σ i, Fin (orders i)))) :
    Dv.evenExpandedPacketValue orders packet θ shift (r, j) =
      reshapeCombinedJetsFinCLM row ι orders
        (fun s => iteratedDeriv s.2.1
          (Dv.evenCarrierB θ)
          (combinedProjectiveRowShiftPacket packet shift s.1))
        (r, j) := by
  unfold MovingDivisor.evenExpandedPacketValue
  apply congrArg
    (fun v : ((Σ x : row × ι, Fin (orders x.2)) → ℂ) =>
      reshapeCombinedJetsFinCLM row ι orders v (r, j))
  funext s
  exact Dv.evenActualJetFamily_apply
    (fun _ : Unit => combinedProjectiveRowShiftPacket packet shift)
    (fun x : row × ι => orders x.2) (θ, ())
    hupper
    s

def evenExpandedFullRankWitness (Dv : MovingDivisor)
    {row κ ι : Type}
    [Fintype row] [DecidableEq row]
    [Fintype κ] [Fintype ι] [DecidableEq ι]
    (degree : ℕ) (orders : ι → ℕ)
    (exponent :
      κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (θ : BoundedRealSequence)
    (shift : InjectiveShiftConfiguration ι) : Prop :=
  ∃ packet : InjectiveProjectiveRowPacket row,
    Function.Injective (combinedProjectiveRowShiftPacket packet shift) ∧
      (∀ x, 0 < (combinedProjectiveRowShiftPacket packet shift x).im) ∧
      (∀ x, 0 < (combinedProjectiveRowShiftPacket packet shift x).re) ∧
      Function.Injective
        (expandedDifferentialEvaluationMatrix degree
          (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
          (Dv.evenExpandedPacketValue
            orders packet θ shift)).mulVec

def evenExpandedPatternRelationHolds (Dv : MovingDivisor)
    {row κ ι : Type}
    [Fintype row] [DecidableEq row]
    [Fintype κ] [Fintype ι] [DecidableEq ι]
    (degree : ℕ) (orders : ι → ℕ)
    (exponent :
      κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (θ : BoundedRealSequence)
    (shift : InjectiveShiftConfiguration ι)
    (coeff : κ × Fin (degree + 1) → ℂ) : Prop :=
  ∀ packet : InjectiveProjectiveRowPacket row,
    Function.Injective (combinedProjectiveRowShiftPacket packet shift) →
    (∀ x, 0 < (combinedProjectiveRowShiftPacket packet shift x).im) →
    (∀ x, 0 < (combinedProjectiveRowShiftPacket packet shift x).re) →
    ∀ r, ∑ col, coeff col *
      expandedDifferentialEvaluationMatrix degree
        (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
        (Dv.evenExpandedPacketValue
          orders packet θ shift) r col = 0

theorem evenExpandedPatternRelation_coefficients_eq_zero_of_fullRankWitness (Dv : MovingDivisor)
    {row κ ι : Type}
    [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (degree : ℕ) (orders : ι → ℕ)
    (exponent :
      κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (θ : BoundedRealSequence)
    (shift : InjectiveShiftConfiguration ι)
    (hwitness : Dv.evenExpandedFullRankWitness
      (row := row) (κ := κ) degree orders exponent θ shift)
    (coeff : κ × Fin (degree + 1) → ℂ)
    (hrelation : Dv.evenExpandedPatternRelationHolds
      (row := row) degree orders exponent θ shift coeff) :
    ∀ col, coeff col = 0 := by
  obtain ⟨packet, hinjNodes, hupper, hreal, hinjective⟩ := hwitness
  let A := expandedDifferentialEvaluationMatrix degree
    (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
    (Dv.evenExpandedPacketValue orders packet θ shift)
  have hmul : A.mulVec coeff = 0 := by
    funext r
    simpa [A, Matrix.mulVec, dotProduct, mul_comm] using
      hrelation packet hinjNodes hupper hreal r
  have hcoeff : coeff = 0 := hinjective (by simpa [A] using hmul)
  intro col
  exact congrFun hcoeff col

theorem compact_injectiveShiftPatch_has_dense_completeAtlas_even (Dv : MovingDivisor)
    {row κ ι : Type}
    [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (degree : ℕ) (orders : ι → ℕ)
    (exponent :
      κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree <
      Fintype.card row)
    (Kshift : Set (InjectiveShiftConfiguration ι))
    (hKshift : IsCompact Kshift)
    (hdim : Module.finrank ℝ (ι → ℂ) <
      2 * (Fintype.card row -
        Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    ∃ n : ℕ, ∃ packets : Fin n → InjectiveProjectiveRowPacket row,
      ∃ pieces : Fin n → Set (InjectiveShiftConfiguration ι),
        Kshift ⊆ ⋃ j, pieces j ∧
        (∀ j, IsCompact (pieces j)) ∧
        (∀ j, pieces j ⊆
          evenCanonicalUpperGoodCombinedRowPacketSet (packets j)) ∧
        let ambientPiece := fun j =>
          ambientImageOfInjectiveShiftPiece (pieces j)
        let family := fun j =>
          Dv.evenExpandedActualJetFamily orders
            (fun h x => (packets j).1 x.1 + h x.2)
        let good := fun j => compactConfigurationAvoidance (family j)
          (expandedDifferentialEvaluationRankDefect degree
            (Fintype.card (Σ i, Fin (orders i)))
            (packets j).1 exponent)
          (ambientPiece j)
        Dense (⋂ j, good j) ∧ IsOpen (⋂ j, good j) ∧
          ∀ θ ∈ ⋂ j, good j, ∀ shift ∈ Kshift,
            Dv.evenExpandedFullRankWitness
              (row := row) (κ := κ)
              degree orders exponent θ shift := by
  classical
  obtain ⟨n, packets, pieces, hcover, hpiecesCompact, hpiecesChart⟩ :=
    compact_injectiveShiftPatch_finite_evenCanonicalUpperGoodCombinedRowPacket_refinement
      (row := row) hKshift
  let ambientPiece : Fin n → Set (ι → ℂ) := fun j =>
    ambientImageOfInjectiveShiftPiece (pieces j)
  let nodes : Fin n → (ι → ℂ) → (row × ι → ℂ) := fun j h x =>
    (packets j).1 x.1 + h x.2
  let family := fun j =>
    Dv.evenExpandedActualJetFamily orders (nodes j)
  let good := fun j => compactConfigurationAvoidance (family j)
    (expandedDifferentialEvaluationRankDefect degree
      (Fintype.card (Σ i, Fin (orders i))) (packets j).1 exponent)
    (ambientPiece j)
  have hgood : ∀ j, Dense (good j) ∧ IsOpen (good j) := by
    intro j
    let Uj : Set (ι → ℂ) :=
      evenCanonicalUpperGoodCombinedRowPacketAmbientSet (packets j)
    have hUj : IsOpen Uj :=
      evenCanonicalUpperGoodCombinedRowPacketAmbientSet_isOpen
        (packets j)
    have hKj : IsCompact (ambientPiece j) :=
      (hpiecesCompact j).image continuous_subtype_val
    have hKjUj : ambientPiece j ⊆ Uj := by
      rintro shift ⟨shiftCfg, hpiece, rfl⟩
      exact hpiecesChart j hpiece
    have hnodes : ContDiff ℝ ⊤ (nodes j) := by
      rw [contDiff_pi]
      intro x
      exact contDiff_const.add (contDiff_apply ℝ ℂ x.2)
    have hdenseRaw :=
      Dv.compact_evenExpandedActualEvaluation_avoidance_dense
        degree orders (packets j).1 (packets j).2
        exponent hexponent hrows
        (nodes j) hnodes Uj (ambientPiece j)
        hUj hKjUj
        (fun h hh =>
          positiveRealUpperNodes_evenSeparated
            (nodes j h) hh.1.1 hh.2)
        (fun h hh x => hh.1.2 x)
        hdim
    have hdense : Dense (good j) := by
      simpa only [good, family] using hdenseRaw
    have hfamilyOn : ContinuousOn (family j) (Set.univ ×ˢ Uj) := by
      exact Dv.continuousOn_evenExpandedActualJetFamily
        orders (nodes j) hnodes.continuous Uj
          (fun h hh x => hh.1.2 x)
    have hopenRaw :=
      compactConfigurationAvoidance_isOpen_of_continuousOn_open
        (family j)
        (expandedDifferentialEvaluationRankDefect degree
          (Fintype.card (Σ i, Fin (orders i)))
          (packets j).1 exponent)
        (expandedDifferentialEvaluationRankDefect_isClosed degree
          (Fintype.card (Σ i, Fin (orders i)))
          (packets j).1 exponent)
        Uj hUj hfamilyOn (ambientPiece j) hKj hKjUj
    have hopen : IsOpen (good j) := by
      simpa only [good] using hopenRaw
    exact ⟨hdense, hopen⟩
  refine ⟨n, packets, pieces, hcover, hpiecesCompact, hpiecesChart,
    ?_, ?_, ?_⟩
  · exact dense_iInter_of_finite_isOpen good
      (fun j => (hgood j).2) (fun j => (hgood j).1)
  · exact isOpen_iInter_of_finite (fun j => (hgood j).2)
  · intro θ hθ shift hshift
    obtain ⟨j, hjpiece⟩ := Set.mem_iUnion.mp (hcover hshift)
    have hjchart := hpiecesChart j hjpiece
    refine ⟨packets j, hjchart.1.1, hjchart.1.2, hjchart.2, ?_⟩
    have hjgood := Set.mem_iInter.mp hθ j
    have hambient : shift.1 ∈ ambientPiece j :=
      ⟨shift, hjpiece, rfl⟩
    have havoid := hjgood shift.1 hambient
    have hinjective : Function.Injective
        (expandedDifferentialEvaluationMatrix degree
          (Fintype.card (Σ i, Fin (orders i)))
          (packets j).1 exponent
          (family j (θ, shift.1))).mulVec := by
      simpa only [mem_expandedDifferentialEvaluationRankDefect_iff,
        not_not] using havoid
    change Function.Injective
      (expandedDifferentialEvaluationMatrix degree
        (Fintype.card (Σ i, Fin (orders i)))
        (packets j).1 exponent
        (family j (θ, shift.1))).mulVec
    exact hinjective

theorem global_injectiveShifts_evenExpandedFullRankWitness_dense_residual (Dv : MovingDivisor)
    {row κ ι : Type}
    [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (degree : ℕ) (orders : ι → ℕ)
    (exponent :
      κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree <
      Fintype.card row)
    (hdim : Module.finrank ℝ (ι → ℂ) <
      2 * (Fintype.card row -
        Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    let good : Set BoundedRealSequence := {θ |
      ∀ shift : InjectiveShiftConfiguration ι,
        Dv.evenExpandedFullRankWitness
          (row := row) (κ := κ)
          degree orders exponent θ shift}
    Dense good ∧ good ∈ residual BoundedRealSequence := by
  dsimp only
  letI : BaireSpace BoundedRealSequence := by infer_instance
  apply globalWitness_dense_residual_of_sigmaCompact
    (fun θ (shift : InjectiveShiftConfiguration ι) =>
      Dv.evenExpandedFullRankWitness
        (row := row) (κ := κ)
        degree orders exponent θ shift)
  intro Kshift hKshift
  obtain ⟨n, packets, pieces, hcover, hpiecesCompact, hpiecesChart,
      hDense, hOpen, hWitness⟩ :=
    Dv.compact_injectiveShiftPatch_has_dense_completeAtlas_even
      degree orders exponent hexponent hrows Kshift hKshift hdim
  exact ⟨_, hOpen, hDense, hWitness⟩

theorem allFinitePatterns_evenExpandedFullRankWitness_dense_residual (Dv : MovingDivisor)
    {Γ : Type} [Countable Γ] :
    let fullRank : Set BoundedRealSequence := {θ |
      ∀ (p : FiniteDifferentialPattern Γ)
        (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
        Dv.evenExpandedFullRankWitness
          (row := CarrierPatternRow p)
          (κ := CarrierPatternMonomial p)
          p.coefficientDegree p.orders
          (carrierPatternExponent p) θ shift}
    Dense fullRank ∧ fullRank ∈ residual BoundedRealSequence := by
  dsimp only
  letI : BaireSpace BoundedRealSequence := by infer_instance
  let goodPattern :
      FiniteDifferentialPattern Γ → Set BoundedRealSequence := fun p =>
    {θ | ∀ shift : InjectiveShiftConfiguration (CarrierPatternShift p),
      Dv.evenExpandedFullRankWitness
        (row := CarrierPatternRow p)
        (κ := CarrierPatternMonomial p)
        p.coefficientDegree p.orders
        (carrierPatternExponent p) θ shift}
  have hgoodPattern : ∀ p : FiniteDifferentialPattern Γ,
      Dense (goodPattern p) ∧
        goodPattern p ∈ residual BoundedRealSequence := by
    intro p
    have hsource :=
      Dv.global_injectiveShifts_evenExpandedFullRankWitness_dense_residual
        (row := CarrierPatternRow p)
        (κ := CarrierPatternMonomial p)
        (ι := CarrierPatternShift p)
        p.coefficientDegree p.orders
        (carrierPatternExponent p)
        (carrierPatternExponent_injective p)
        (carrierPattern_rows_strictly_dominate_columns p)
        (carrierPattern_shift_dimension_below_codimension p)
    change Dense (goodPattern p) ∧
      goodPattern p ∈ residual BoundedRealSequence at hsource
    exact hsource
  have hresidual : (⋂ p, goodPattern p) ∈
      residual BoundedRealSequence :=
    countable_iInter_mem.mpr fun p => (hgoodPattern p).2
  have heq : (⋂ p, goodPattern p) =
      {θ | ∀ (p : FiniteDifferentialPattern Γ)
        (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
        Dv.evenExpandedFullRankWitness
          (row := CarrierPatternRow p)
          (κ := CarrierPatternMonomial p)
          p.coefficientDegree p.orders
          (carrierPatternExponent p) θ shift} := by
    ext θ
    simp only [Set.mem_iInter, goodPattern, Set.mem_setOf_eq]
  rw [heq] at hresidual
  exact ⟨dense_of_mem_residual hresidual, hresidual⟩

theorem allFinitePatterns_evenExpandedRelationFree_dense_residual (Dv : MovingDivisor)
    {Γ : Type} [Countable Γ] :
    let relationFree : Set BoundedRealSequence := {θ |
      ∀ (p : FiniteDifferentialPattern Γ)
        (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
        (coeff :
          CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
        Dv.evenExpandedPatternRelationHolds
          (row := CarrierPatternRow p)
          p.coefficientDegree p.orders
          (carrierPatternExponent p) θ shift coeff →
        ∀ col, coeff col = 0}
    Dense relationFree ∧
      relationFree ∈ residual BoundedRealSequence := by
  dsimp only
  let fullRank : Set BoundedRealSequence := {θ |
    ∀ (p : FiniteDifferentialPattern Γ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
      Dv.evenExpandedFullRankWitness
        (row := CarrierPatternRow p)
        (κ := CarrierPatternMonomial p)
        p.coefficientDegree p.orders
        (carrierPatternExponent p) θ shift}
  let relationFree : Set BoundedRealSequence := {θ |
    ∀ (p : FiniteDifferentialPattern Γ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff :
        CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      Dv.evenExpandedPatternRelationHolds
        (row := CarrierPatternRow p)
        p.coefficientDegree p.orders
        (carrierPatternExponent p) θ shift coeff →
      ∀ col, coeff col = 0}
  have hfull : Dense fullRank ∧
      fullRank ∈ residual BoundedRealSequence := by
    simpa only [fullRank] using
      (Dv.allFinitePatterns_evenExpandedFullRankWitness_dense_residual
        (Γ := Γ))
  have hsubset : fullRank ⊆ relationFree := by
    intro θ hθ p shift coeff hrelation
    exact
      Dv.evenExpandedPatternRelation_coefficients_eq_zero_of_fullRankWitness
        p.coefficientDegree p.orders
        (carrierPatternExponent p) θ shift
        (hθ p shift) coeff hrelation
  exact ⟨hfull.1.mono hsubset,
    Filter.mem_of_superset hfull.2 hsubset⟩

theorem evenExpandedPacketValue_eq_familyJetVec (Dv : MovingDivisor)
    {m n : ℕ} {row : Type} [Fintype row] [DecidableEq row]
    (packet : InjectiveProjectiveRowPacket row)
    (θ : BoundedRealSequence)
    (shift : InjectiveShiftConfiguration (Fin m))
    (hupper : ∀ x : row × Fin m,
      0 < (combinedProjectiveRowShiftPacket packet shift x).im)
    (r : row)
    (t : Σ _ : Fin m, Fin (n + 1)) :
    Dv.evenExpandedPacketValue
        (fun _ : Fin m => n + 1) packet θ shift
        (r, Fintype.equivFin (Σ _ : Fin m, Fin (n + 1)) t) =
      familyJetVec (n := n)
        (fun i w => Dv.evenCarrierB θ (w + shift.1 i))
        (packet.1 r) (Sum.inr (t.1, t.2)) := by
  rw [Dv.evenExpandedPacketValue_apply
    (fun _ : Fin m => n + 1) packet θ shift hupper]
  show iteratedDeriv _ _ _ = _
  rw [(Fintype.equivFin
    (Σ _ : Fin m, Fin (n + 1))).symm_apply_apply t]
  show _ = iteratedDeriv (t.2 : ℕ)
    (fun w => Dv.evenCarrierB θ (w + shift.1 t.1))
    (packet.1 r)
  rw [iteratedDeriv_comp_add_right]
  rfl

theorem not_familyDifferentiallyAlgebraicOn_evenCarrierB_of_relationFree (Dv : MovingDivisor)
    (m : ℕ) (θ : BoundedRealSequence)
    (hfree : ∀ (p : FiniteDifferentialPattern ℕ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff :
        CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      Dv.evenExpandedPatternRelationHolds
        (row := CarrierPatternRow p)
        p.coefficientDegree p.orders
        (carrierPatternExponent p) θ shift coeff →
      ∀ col, coeff col = 0)
    (shift : InjectiveShiftConfiguration (Fin m)) :
    ¬ FamilyDifferentiallyAlgebraicOn
      (fun i z => Dv.evenCarrierB θ (z + shift.1 i))
      (commonUpperTranslationDomain shift) := by
  intro hDA
  obtain ⟨n, P, hPne, hPzero⟩ := hDA
  let shiftCode : Fin m → ℕ := naturalFamilyShiftCode m
  have hshiftCode : Function.Injective shiftCode :=
    naturalFamilyShiftCode_injective m
  let Q : MvPolynomial
      (Σ _ : Fin m, Fin (n + 1)) (Polynomial ℂ) :=
    renameToFamilyShiftJets m n (familyReshapeJet m n P)
  let p : FiniteDifferentialPattern ℕ :=
    codedFamilyPatternOfRelation shiftCode hshiftCode P
  let shiftP : InjectiveShiftConfiguration (CarrierPatternShift p) :=
    ⟨shift.1, shift.2⟩
  let patternCoeff : PatternRow p → ℂ :=
    polynomialPatternCoefficientVector
      shiftCode hshiftCode (familyOrders m n) Q
  let coeff :
      CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ :=
    fun col => patternCoeff
      (Fintype.equivFin (PatternShape p) col)
  have hrelation : Dv.evenExpandedPatternRelationHolds
      (row := CarrierPatternRow p)
      p.coefficientDegree p.orders
      (carrierPatternExponent p) θ shiftP coeff := by
    intro packet hinj hupper hreal r
    let z : ℂ := packet.1 r
    let sigma := Σ i : CarrierPatternShift p, Fin (p.orders i)
    let y : CarrierPatternRow p × Fin (Fintype.card sigma) → ℂ :=
      Dv.evenExpandedPacketValue p.orders packet θ shiftP
    let x : sigma → ℂ := fun t =>
      familyJetVec (n := n)
        (fun i w => Dv.evenCarrierB θ (w + shift.1 i))
        z (Sum.inr (t.1, t.2))
    have hy : ∀ t : sigma,
        y (r, Fintype.equivFin sigma t) = x t := by
      intro t
      simpa [y, x, p, Q, shiftP, shiftCode,
        codedFamilyPatternOfRelation, familyOrders] using!
        (Dv.evenExpandedPacketValue_eq_familyJetVec
          packet θ shift hupper r
          (⟨t.1, t.2⟩ : Σ _ : Fin m, Fin (n + 1)))
    have hprod : ∀ a : CarrierPatternMonomial p,
        (carrierPatternExponent p a).prod
            (fun k e => y (r, k) ^ e) =
          (p.jetExponent a).prod (fun t e => x t ^ e) := by
      intro a
      rw [carrierPatternExponent, Finsupp.equivCongrLeft_apply,
        Finsupp.prod_equivMapDomain]
      apply Finsupp.prod_congr
      intro t ht
      rw [hy t]
    have hsum :
        (∑ col, coeff col *
          expandedDifferentialEvaluationMatrix p.coefficientDegree
            (Fintype.card sigma) packet.1
            (carrierPatternExponent p) y r col) =
          ∑ b : PatternRow p,
            patternCoeff b * z ^ patternDegree p b *
              (patternExponent p b).prod
                (fun t e => x t ^ e) := by
      apply Fintype.sum_equiv
        (Fintype.equivFin (PatternShape p))
      intro col
      rw [expandedDifferentialEvaluationMatrix_apply, hprod]
      simp [coeff, patternCoeff, patternDegree,
        patternExponent, z]
      ring
    rw [hsum]
    have hdomain :
        z ∈ commonUpperTranslationDomain shift := by
      intro i
      have hi := hupper (r, i)
      simpa [commonUpperTranslationDomain,
        combinedProjectiveRowShiftPacket,
        z, shiftP, p, codedFamilyPatternOfRelation] using hi
    calc
      (∑ b : PatternRow p,
          patternCoeff b * z ^ patternDegree p b *
            (patternExponent p b).prod
              (fun t e => x t ^ e)) =
          MvPolynomial.eval
            (Sum.elim (fun _ => z)
              fun q => x ⟨q.1, q.2⟩) P := by
        simpa [patternCoeff, p, Q] using!
          (codedFamilyPatternExpansion_eq_eval
            shiftCode hshiftCode P z x)
      _ = 0 := hPzero z hdomain
  have hcoeffZero := hfree p shiftP coeff hrelation
  have hpatternZero : ∀ b : PatternRow p,
      patternCoeff b = 0 := by
    intro b
    let col : PatternShape p :=
      (Fintype.equivFin (PatternShape p)).symm b
    have hz := hcoeffZero col
    simpa [coeff, col] using hz
  have hP : P = 0 :=
    familyJetRelation_eq_zero_of_codedPatternCoefficients_zero
      shiftCode hshiftCode P (by
        intro b
        exact hpatternZero b)
  exact hPne hP

theorem movingDivisor_fullTranslationFreeness_denseResidual (Dv : MovingDivisor) :
    let universalPhase : Set BoundedRealSequence := {θ |
      ∀ (p : FiniteDifferentialPattern ℕ)
        (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
        (coeff :
          CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
        Dv.evenExpandedPatternRelationHolds
          (row := CarrierPatternRow p)
          p.coefficientDegree p.orders
          (carrierPatternExponent p) θ shift coeff →
        ∀ col, coeff col = 0}
    Dense universalPhase ∧
      universalPhase ∈ residual BoundedRealSequence ∧
      ∀ θ ∈ universalPhase, ∀ (m : ℕ)
        (shift : InjectiveShiftConfiguration (Fin m)),
        ¬ FamilyDifferentiallyAlgebraicOn
          (fun i z =>
            Dv.evenCarrierB θ (z + shift.1 i))
          (commonUpperTranslationDomain shift) := by
  dsimp only
  let universalPhase : Set BoundedRealSequence := {θ |
    ∀ (p : FiniteDifferentialPattern ℕ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff :
        CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      Dv.evenExpandedPatternRelationHolds
        (row := CarrierPatternRow p)
        p.coefficientDegree p.orders
        (carrierPatternExponent p) θ shift coeff →
      ∀ col, coeff col = 0}
  have hphase : Dense universalPhase ∧
      universalPhase ∈ residual BoundedRealSequence := by
    simpa only [universalPhase] using
      (Dv.allFinitePatterns_evenExpandedRelationFree_dense_residual
        (Γ := ℕ))
  refine ⟨hphase.1, hphase.2, ?_⟩
  intro θ hθ m shift
  exact
    Dv.not_familyDifferentiallyAlgebraicOn_evenCarrierB_of_relationFree
      m θ hθ shift

end MovingDivisor

end

end GaloisForLFunctions.HTGeometry
