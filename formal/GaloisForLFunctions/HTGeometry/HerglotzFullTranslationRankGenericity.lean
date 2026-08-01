import GaloisForLFunctions.HTGeometry.CompactCauchyRowPacketAtlas
import GaloisForLFunctions.HTGeometry.AnalyticNevanlinnaCarrierRelationFree
import GaloisForLFunctions.HTGeometry.HerglotzJetMapJointContinuity
import GaloisForLFunctions.HTGeometry.InjectiveShiftConfigurationTopology
import GaloisForLFunctions.HTGeometry.NevanlinnaNoncriticalProjectiveCompactPatch

/-!
# Full-translation rank genericity for arbitrary-measure Herglotz charts

This module globalizes compact translated-row transversality.  A finite compact atlas handles one
compact patch of collision-free complex shifts.  Joint parameter/node continuity makes every
patch condition open, and the nonlinear compact-patch theorem makes it dense.  Sigma-compactness
then gives one dense residual set with a literal full-rank witness for every finite tuple of
distinct complex shifts.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set Topology
open ClassicalAnalyticNevanlinnaCarrierFamily
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 2000000

/-- Normalized Cauchy moments of one bounded Herglotz parameter on a translated row packet. -/
def herglotzExpandedPacketValue
    {row ι : Type} [Fintype row] [DecidableEq row] [Fintype ι] [DecidableEq ι]
    (μ : Measure ℝ) (w : ℝ → ℝ) (orders : ι → ℕ)
    (packet : InjectiveProjectiveRowPacket row)
    (u : Lp ℝ ⊤ μ) (shift : InjectiveShiftConfiguration ι) :
    row × Fin (Fintype.card (Σ i, Fin (orders i))) → ℂ :=
  reshapeCombinedJetsFinCLM row ι orders
    (herglotzJetMap μ w (combinedProjectiveRowShiftPacket packet shift)
      (fun x : row × ι => orders x.2) u)

/-- One admissible translated row packet witnesses full coefficient rank for normalized Herglotz
Cauchy moments. -/
def herglotzExpandedFullRankWitness
    {row κ ι : Type}
    [Fintype row] [DecidableEq row]
    [Fintype κ] [Fintype ι] [DecidableEq ι]
    (μ : Measure ℝ) (w : ℝ → ℝ)
    (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (u : Lp ℝ ⊤ μ) (shift : InjectiveShiftConfiguration ι) : Prop :=
  ∃ packet : InjectiveProjectiveRowPacket row,
    Function.Injective (combinedProjectiveRowShiftPacket packet shift) ∧
      (∀ x, 0 < (combinedProjectiveRowShiftPacket packet shift x).im) ∧
      Function.Injective
        (expandedDifferentialEvaluationMatrix degree
          (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
          (herglotzExpandedPacketValue μ w orders packet u shift)).mulVec

/-- A finite polynomial-coefficient relation on normalized Herglotz Cauchy moments. -/
def herglotzExpandedPatternRelationHolds
    {row κ ι : Type}
    [Fintype row] [DecidableEq row]
    [Fintype κ] [Fintype ι] [DecidableEq ι]
    (μ : Measure ℝ) (w : ℝ → ℝ)
    (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (u : Lp ℝ ⊤ μ) (shift : InjectiveShiftConfiguration ι)
    (coeff : κ × Fin (degree + 1) → ℂ) : Prop :=
  ∀ packet : InjectiveProjectiveRowPacket row,
    Function.Injective (combinedProjectiveRowShiftPacket packet shift) →
    (∀ x, 0 < (combinedProjectiveRowShiftPacket packet shift x).im) →
    ∀ r, ∑ col, coeff col *
      expandedDifferentialEvaluationMatrix degree
        (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
        (herglotzExpandedPacketValue μ w orders packet u shift) r col = 0

/-- A literal full-rank normalized-moment packet kills every coefficient of the same relation. -/
theorem herglotzExpandedPatternRelation_coefficients_eq_zero_of_fullRankWitness
    {row κ ι : Type}
    [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (μ : Measure ℝ) (w : ℝ → ℝ)
    (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (u : Lp ℝ ⊤ μ) (shift : InjectiveShiftConfiguration ι)
    (hwitness : herglotzExpandedFullRankWitness
      (row := row) (κ := κ) μ w degree orders exponent u shift)
    (coeff : κ × Fin (degree + 1) → ℂ)
    (hrelation : herglotzExpandedPatternRelationHolds
      (row := row) μ w degree orders exponent u shift coeff) :
    ∀ col, coeff col = 0 := by
  obtain ⟨packet, hinjNodes, hupper, hinjective⟩ := hwitness
  let A := expandedDifferentialEvaluationMatrix degree
    (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
    (herglotzExpandedPacketValue μ w orders packet u shift)
  have hmul : A.mulVec coeff = 0 := by
    funext r
    simpa [A, Matrix.mulVec, dotProduct, mul_comm] using
      hrelation packet hinjNodes hupper r
  have hcoeff : coeff = 0 := hinjective (by simpa [A] using hmul)
  intro col
  exact congrFun hcoeff col

/-- **Compact-shift complete-atlas Herglotz rank law.**  A compact collision-free shift patch has
one finite compact row atlas whose simultaneous normalized-moment full-rank phase is open dense and
witnesses every shift in the original patch. -/
theorem compact_injectiveShiftPatch_has_dense_completeAtlas_herglotz
    {row κ ι : Type}
    [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (μ : Measure ℝ) (hμ : μ.support.Infinite)
    (w : ℝ → ℝ) (hw : Integrable w μ) (hwpos : ∀ t, 0 < w t)
    (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree < Fintype.card row)
    (Kshift : Set (InjectiveShiftConfiguration ι)) (hKshift : IsCompact Kshift)
    (hdim : Module.finrank ℝ (ι → ℂ) <
      2 * (Fintype.card row - Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    ∃ n : ℕ, ∃ packets : Fin n → InjectiveProjectiveRowPacket row,
      ∃ pieces : Fin n → Set (InjectiveShiftConfiguration ι),
        Kshift ⊆ ⋃ j, pieces j ∧
        (∀ j, IsCompact (pieces j)) ∧
        (∀ j, pieces j ⊆ cauchyUpperGoodCombinedRowPacketSet (packets j)) ∧
        let ambientPiece := fun j => ambientImageOfInjectiveShiftPiece (pieces j)
        let family := fun j (p : Lp ℝ ⊤ μ × (ι → ℂ)) =>
          reshapeCombinedJetsFinCLM row ι orders
            (herglotzJetMap μ w
              (fun x : row × ι => (packets j).1 x.1 + p.2 x.2)
              (fun x : row × ι => orders x.2) p.1)
        let good := fun j => compactConfigurationAvoidance (family j)
          (expandedDifferentialEvaluationRankDefect
            degree (Fintype.card (Σ i, Fin (orders i))) (packets j).1 exponent)
          (ambientPiece j)
        Dense (⋂ j, good j) ∧ IsOpen (⋂ j, good j) ∧
          ∀ u ∈ ⋂ j, good j, ∀ shift ∈ Kshift,
            herglotzExpandedFullRankWitness
              (row := row) (κ := κ) μ w degree orders exponent u shift := by
  classical
  obtain ⟨n, packets, pieces, hcover, hpiecesCompact, hpiecesChart⟩ :=
    compact_injectiveShiftPatch_finite_cauchyUpperGoodCombinedRowPacket_refinement
      (row := row) hKshift
  let ambientPiece : Fin n → Set (ι → ℂ) := fun j =>
    ambientImageOfInjectiveShiftPiece (pieces j)
  let nodes : Fin n → (ι → ℂ) → (row × ι → ℂ) := fun j h x =>
    (packets j).1 x.1 + h x.2
  let family := fun j (p : Lp ℝ ⊤ μ × (ι → ℂ)) =>
    reshapeCombinedJetsFinCLM row ι orders
      (herglotzJetMap μ w (nodes j p.2)
        (fun x : row × ι => orders x.2) p.1)
  let good := fun j => compactConfigurationAvoidance (family j)
    (expandedDifferentialEvaluationRankDefect
      degree (Fintype.card (Σ i, Fin (orders i))) (packets j).1 exponent)
    (ambientPiece j)
  have hgood : ∀ j, Dense (good j) ∧ IsOpen (good j) := by
    intro j
    let Uj : Set (ι → ℂ) :=
      cauchyUpperGoodCombinedRowPacketAmbientSet (packets j)
    have hUj : IsOpen Uj :=
      cauchyUpperGoodCombinedRowPacketAmbientSet_isOpen (packets j)
    have hKj : IsCompact (ambientPiece j) :=
      (hpiecesCompact j).image continuous_subtype_val
    have hKjUj : ambientPiece j ⊆ Uj := by
      rintro shift ⟨shiftCfg, hpiece, rfl⟩
      exact hpiecesChart j hpiece
    have hnodes : ContDiff ℝ ⊤ (nodes j) := by
      rw [contDiff_pi]
      intro x
      exact contDiff_const.add (contDiff_apply ℝ ℂ x.2)
    have hdenseRaw := compact_herglotzExpandedEvaluation_avoidance_dense
      μ hμ w hw hwpos degree orders (packets j).1 (packets j).2
      exponent hexponent hrows (nodes j) hnodes Uj (ambientPiece j)
      hUj hKj hKjUj (fun h hh x => hh.2 x)
        (fun h hh => (hKjUj hh).1) hdim
    have hdense : Dense (good j) := by
      simpa only [good, family] using hdenseRaw
    have hfamilyOn : ContinuousOn (family j) (Set.univ ×ˢ Uj) := by
      have hargs : Continuous
          (fun p : Lp ℝ ⊤ μ × (ι → ℂ) => (p.1, nodes j p.2)) :=
        continuous_fst.prodMk (hnodes.continuous.comp continuous_snd)
      have hsource : ContinuousOn
          (fun p : Lp ℝ ⊤ μ × (row × ι → ℂ) =>
            reshapeCombinedJetsFinCLM row ι orders
              (herglotzJetMap μ w p.2 (fun x : row × ι => orders x.2) p.1))
          (Set.univ ×ˢ nevanlinnaUpperPacketSet (fun z : ℂ => z)) :=
        continuousOn_reshapedHerglotzJetMap_pair μ w hw
          (fun t => (hwpos t).le) orders
      exact hsource.comp hargs.continuousOn (fun p hp => by
        refine ⟨Set.mem_univ _, ?_⟩
        intro x
        exact hp.2.2 x)
    have hopenRaw := compactConfigurationAvoidance_isOpen_of_continuousOn_open
        (family j)
        (expandedDifferentialEvaluationRankDefect
          degree (Fintype.card (Σ i, Fin (orders i))) (packets j).1 exponent)
        (expandedDifferentialEvaluationRankDefect_isClosed
          degree (Fintype.card (Σ i, Fin (orders i))) (packets j).1 exponent)
        Uj hUj hfamilyOn (ambientPiece j) hKj hKjUj
    have hopen : IsOpen (good j) := by
      simpa only [good] using hopenRaw
    exact ⟨hdense, hopen⟩
  refine ⟨n, packets, pieces, hcover, hpiecesCompact, hpiecesChart, ?_, ?_, ?_⟩
  · exact dense_iInter_of_finite_isOpen good
      (fun j => (hgood j).2) (fun j => (hgood j).1)
  · exact isOpen_iInter_of_finite (fun j => (hgood j).2)
  · intro u hu shift hshift
    obtain ⟨j, hjpiece⟩ := Set.mem_iUnion.mp (hcover hshift)
    have hjchart := hpiecesChart j hjpiece
    refine ⟨packets j, hjchart.1, hjchart.2, ?_⟩
    have hjgood := Set.mem_iInter.mp hu j
    have hambient : shift.1 ∈ ambientPiece j := ⟨shift, hjpiece, rfl⟩
    have havoid := hjgood shift.1 hambient
    have hinjective : Function.Injective
        (expandedDifferentialEvaluationMatrix degree
          (Fintype.card (Σ i, Fin (orders i))) (packets j).1 exponent
          (family j (u, shift.1))).mulVec := by
      simpa only [mem_expandedDifferentialEvaluationRankDefect_iff, not_not] using havoid
    change Function.Injective
      (expandedDifferentialEvaluationMatrix degree
        (Fintype.card (Σ i, Fin (orders i))) (packets j).1 exponent
        (family j (u, shift.1))).mulVec
    exact hinjective

/-- **All-shift rank law for one finite pattern.**  A dense residual set of bounded Herglotz
parameters has a full normalized-moment row witness for every tuple of distinct complex shifts. -/
theorem global_injectiveShifts_herglotzExpandedFullRankWitness_dense_residual
    {row κ ι : Type}
    [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (μ : Measure ℝ) (hμ : μ.support.Infinite)
    (w : ℝ → ℝ) (hw : Integrable w μ) (hwpos : ∀ t, 0 < w t)
    (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree < Fintype.card row)
    (hdim : Module.finrank ℝ (ι → ℂ) <
      2 * (Fintype.card row - Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    let good : Set (Lp ℝ ⊤ μ) := {u | ∀ shift : InjectiveShiftConfiguration ι,
      herglotzExpandedFullRankWitness
        (row := row) (κ := κ) μ w degree orders exponent u shift}
    Dense good ∧ good ∈ residual (Lp ℝ ⊤ μ) := by
  dsimp only
  letI : BaireSpace (Lp ℝ ⊤ μ) := by infer_instance
  apply globalWitness_dense_residual_of_sigmaCompact
    (fun u (shift : InjectiveShiftConfiguration ι) =>
      herglotzExpandedFullRankWitness
        (row := row) (κ := κ) μ w degree orders exponent u shift)
  intro Kshift hKshift
  obtain ⟨n, packets, pieces, hcover, hpiecesCompact, hpiecesChart,
      hDense, hOpen, hWitness⟩ :=
    compact_injectiveShiftPatch_has_dense_completeAtlas_herglotz
      μ hμ w hw hwpos degree orders exponent hexponent hrows Kshift hKshift hdim
  exact ⟨_, hOpen, hDense, hWitness⟩

/-- **All-pattern all-shift normalized-moment rank law.**  One dense residual subset of the
arbitrary-measure Herglotz chart has a literal full-rank packet for every canonical finite
differential pattern over a countable palette and every tuple of distinct complex shifts. -/
theorem allFinitePatterns_herglotzExpandedFullRankWitness_dense_residual
    {Γ : Type} [Countable Γ]
    (μ : Measure ℝ) (hμ : μ.support.Infinite)
    (w : ℝ → ℝ) (hw : Integrable w μ) (hwpos : ∀ t, 0 < w t) :
    let fullRank : Set (Lp ℝ ⊤ μ) := {u | ∀ (p : FiniteDifferentialPattern Γ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
      herglotzExpandedFullRankWitness
        (row := CarrierPatternRow p) (κ := CarrierPatternMonomial p)
        μ w p.coefficientDegree p.orders (carrierPatternExponent p) u shift}
    Dense fullRank ∧ fullRank ∈ residual (Lp ℝ ⊤ μ) := by
  dsimp only
  letI : BaireSpace (Lp ℝ ⊤ μ) := by infer_instance
  let goodPattern : FiniteDifferentialPattern Γ → Set (Lp ℝ ⊤ μ) := fun p =>
    {u | ∀ shift : InjectiveShiftConfiguration (CarrierPatternShift p),
      herglotzExpandedFullRankWitness
        (row := CarrierPatternRow p) (κ := CarrierPatternMonomial p)
        μ w p.coefficientDegree p.orders (carrierPatternExponent p) u shift}
  have hgoodPattern : ∀ p : FiniteDifferentialPattern Γ,
      Dense (goodPattern p) ∧ goodPattern p ∈ residual (Lp ℝ ⊤ μ) := by
    intro p
    have hsource :=
      global_injectiveShifts_herglotzExpandedFullRankWitness_dense_residual
        (row := CarrierPatternRow p) (κ := CarrierPatternMonomial p)
        (ι := CarrierPatternShift p)
        μ hμ w hw hwpos p.coefficientDegree p.orders (carrierPatternExponent p)
        (carrierPatternExponent_injective p)
        (carrierPattern_rows_strictly_dominate_columns p)
        (carrierPattern_shift_dimension_below_codimension p)
    change Dense (goodPattern p) ∧
      goodPattern p ∈ residual (Lp ℝ ⊤ μ) at hsource
    exact hsource
  have hresidual : (⋂ p, goodPattern p) ∈ residual (Lp ℝ ⊤ μ) :=
    countable_iInter_mem.mpr fun p => (hgoodPattern p).2
  have heq : (⋂ p, goodPattern p) = {u | ∀
      (p : FiniteDifferentialPattern Γ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
      herglotzExpandedFullRankWitness
        (row := CarrierPatternRow p) (κ := CarrierPatternMonomial p)
        μ w p.coefficientDegree p.orders (carrierPatternExponent p) u shift} := by
    ext u
    simp only [Set.mem_iInter, goodPattern, Set.mem_setOf_eq]
  rw [heq] at hresidual
  exact ⟨dense_of_mem_residual hresidual, hresidual⟩

/-- **All-pattern coefficient rigidity for arbitrary-measure Herglotz moments.**  One dense
residual set simultaneously kills every finite polynomial-coefficient relation on every distinct
complex shift tuple. -/
theorem allFinitePatterns_herglotzExpandedRelationFree_dense_residual
    {Γ : Type} [Countable Γ]
    (μ : Measure ℝ) (hμ : μ.support.Infinite)
    (w : ℝ → ℝ) (hw : Integrable w μ) (hwpos : ∀ t, 0 < w t) :
    let relationFree : Set (Lp ℝ ⊤ μ) := {u | ∀ (p : FiniteDifferentialPattern Γ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      herglotzExpandedPatternRelationHolds
        (row := CarrierPatternRow p) μ w p.coefficientDegree p.orders
          (carrierPatternExponent p) u shift coeff →
        ∀ col, coeff col = 0}
    Dense relationFree ∧ relationFree ∈ residual (Lp ℝ ⊤ μ) := by
  dsimp only
  let fullRank : Set (Lp ℝ ⊤ μ) := {u | ∀ (p : FiniteDifferentialPattern Γ)
    (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
    herglotzExpandedFullRankWitness
      (row := CarrierPatternRow p) (κ := CarrierPatternMonomial p)
      μ w p.coefficientDegree p.orders (carrierPatternExponent p) u shift}
  let relationFree : Set (Lp ℝ ⊤ μ) := {u | ∀ (p : FiniteDifferentialPattern Γ)
    (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
    (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
    herglotzExpandedPatternRelationHolds
      (row := CarrierPatternRow p) μ w p.coefficientDegree p.orders
        (carrierPatternExponent p) u shift coeff →
      ∀ col, coeff col = 0}
  have hfull : Dense fullRank ∧ fullRank ∈ residual (Lp ℝ ⊤ μ) := by
    simpa only [fullRank] using
      (allFinitePatterns_herglotzExpandedFullRankWitness_dense_residual
        (Γ := Γ) μ hμ w hw hwpos)
  have hsubset : fullRank ⊆ relationFree := by
    intro u hu p shift coeff hrelation
    exact herglotzExpandedPatternRelation_coefficients_eq_zero_of_fullRankWitness
      μ w p.coefficientDegree p.orders (carrierPatternExponent p) u shift
      (hu p shift) coeff hrelation
  exact ⟨hfull.1.mono hsubset, Filter.mem_of_superset hfull.2 hsubset⟩

end

end GaloisForLFunctions.HTGeometry
