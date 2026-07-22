import GaloisForLFunctions.HTGeometry.CompactNoncriticalProjectiveRowPacketAtlas
import GaloisForLFunctions.HTGeometry.InjectiveShiftConfigurationTopology
import GaloisForLFunctions.HTGeometry.NevanlinnaTranslatedExpandedEvaluationCompactPatch

/-!
# Actual compact-patch density on complete projective row atlases

This module joins the complete `row × shift` projective atlas to the actual smooth Nevanlinna
evaluation family.  Its local regularity locus is the complement of the denominator divisor;
no global smooth extension of the meromorphic quotient is assumed.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory Set Topology
open scoped ENNReal OnePoint

noncomputable section

/-- The affine projective coordinate of a Nevanlinna matrix row. -/
def projectiveNevanlinnaQuotient (C D : ℂ → ℂ) (z : ℂ) : ℂ :=
  -D z / C z

/-- The coefficient of the simple projective resolvent in the determinant-one chart. -/
def projectiveNevanlinnaAmplitude (C : ℂ → ℂ) (z : ℂ) : ℂ :=
  -1 / C z ^ 2

/-- The denominator-regular locus of the affine projective chart. -/
def projectiveRegularLocus (C : ℂ → ℂ) : Set ℂ :=
  {z | C z ≠ 0}

theorem projectiveRegularLocus_isOpen
    {C : ℂ → ℂ} (hC : Differentiable ℂ C) :
    IsOpen (projectiveRegularLocus C) :=
  hC.continuous.isOpen_preimage {z : ℂ | z ≠ 0} isOpen_ne

/-- The quotient and amplitude are smooth on the literal denominator-regular locus. -/
theorem contDiffOn_projectiveNevanlinna_coordinates
    {C D : ℂ → ℂ} (hC : Differentiable ℂ C) (hD : Differentiable ℂ D) :
    ContDiffOn ℂ ⊤ (projectiveNevanlinnaAmplitude C) (projectiveRegularLocus C) ∧
      ContDiffOn ℂ ⊤ (projectiveNevanlinnaQuotient C D) (projectiveRegularLocus C) := by
  have hCs : ContDiff ℂ ⊤ C := hC.contDiff
  have hDs : ContDiff ℂ ⊤ D := hD.contDiff
  constructor
  · exact (contDiff_const (c := (-1 : ℂ))).contDiffOn.div
      (hCs.pow 2).contDiffOn (fun z hz => pow_ne_zero 2 hz)
  · exact hDs.neg.contDiffOn.div hCs.contDiffOn (fun z hz => hz)

/-- Strict positivity on a compact family with finitely many coordinates has one positive uniform
lower bound. -/
theorem compact_finite_strictPositive_uniformLowerBound
    {H ρ : Type*} [TopologicalSpace H] [Fintype ρ]
    (K : Set H) (hK : IsCompact K) (f : H → ρ → ℝ)
    (hf : ∀ r, ContinuousOn (fun h => f h r) K)
    (hpos : ∀ h ∈ K, ∀ r, 0 < f h r) :
    ∃ η : ℝ, 0 < η ∧ ∀ h ∈ K, ∀ r, η ≤ f h r := by
  classical
  by_cases hKne : K.Nonempty
  · letI : TopologicalSpace ρ := ⊥
    letI : DiscreteTopology ρ := ⟨rfl⟩
    let g : H × ρ → ℝ := fun p => f p.1 p.2
    have hg : ContinuousOn g (K ×ˢ (Set.univ : Set ρ)) := by
      rw [continuousOn_prod_of_discrete_right]
      intro r
      simpa using hf r
    have hprodCompact : IsCompact (K ×ˢ (Set.univ : Set ρ)) :=
      hK.prod (Set.toFinite (Set.univ : Set ρ)).isCompact
    by_cases hρ : Nonempty ρ
    · obtain ⟨h0, hh0⟩ := hKne
      obtain ⟨r0⟩ := hρ
      have hprodNe : (K ×ˢ (Set.univ : Set ρ)).Nonempty :=
        ⟨(h0, r0), hh0, Set.mem_univ r0⟩
      obtain ⟨p, hp, hpmin⟩ := hprodCompact.exists_isMinOn hprodNe hg
      refine ⟨g p, hpos p.1 hp.1 p.2, ?_⟩
      intro h hh r
      exact hpmin (a := (h, r)) ⟨hh, Set.mem_univ r⟩
    · refine ⟨1, zero_lt_one, ?_⟩
      letI : IsEmpty ρ := not_nonempty_iff.mp hρ
      intro h hh r
      exact isEmptyElim r
  · refine ⟨1, zero_lt_one, ?_⟩
    intro h hh
    exact (hKne ⟨h, hh⟩).elim

/-- Uniform avoidance on a compact patch is open when the family is continuous on one ambient
open collar of that patch.  This is the local meromorphic version of the global tube lemma. -/
theorem compactConfigurationAvoidance_isOpen_of_continuousOn_open
    {X H Y : Type*} [TopologicalSpace X] [TopologicalSpace H] [TopologicalSpace Y]
    (F : X × H → Y) (bad : Set Y) (hbad : IsClosed bad)
    (U : Set H) (hU : IsOpen U)
    (hF : ContinuousOn F (Set.univ ×ˢ U))
    (K : Set H) (hK : IsCompact K) (hKU : K ⊆ U) :
    IsOpen (compactConfigurationAvoidance F bad K) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  let W : Set (X × H) := (Set.univ ×ˢ U) ∩ F ⁻¹' badᶜ
  have hWopen : IsOpen W :=
    hF.isOpen_inter_preimage (isOpen_univ.prod hU) hbad.isOpen_compl
  have hprod : ({x} : Set X) ×ˢ K ⊆ W := by
    rintro ⟨x', h⟩ ⟨hx', hh⟩
    simp only [mem_singleton_iff] at hx'
    subst x'
    exact ⟨⟨Set.mem_univ x, hKU hh⟩, hx h hh⟩
  obtain ⟨V, Z, hVopen, hZopen, hxV, hKZ, hVZ⟩ :=
    generalized_tube_lemma isCompact_singleton hK hWopen hprod
  refine Filter.mem_of_superset (hVopen.mem_nhds (hxV (mem_singleton x))) ?_
  intro x' hx' h hh
  exact (hVZ ⟨hx', hKZ hh⟩).2

/-- A finite intersection of open dense sets is dense, without invoking a Baire-space instance. -/
theorem dense_iInter_of_finite_isOpen
    {X ρ : Type*} [TopologicalSpace X] [Fintype ρ]
    (f : ρ → Set X) (ho : ∀ r, IsOpen (f r)) (hd : ∀ r, Dense (f r)) :
    Dense (⋂ r, f r) := by
  classical
  have hfin : ∀ s : Finset ρ, Dense (⋂ r ∈ s, f r) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert r s hrs ih =>
        have hopen : IsOpen (⋂ i ∈ s, f i) := by
          apply isOpen_biInter_finset
          intro i hi
          exact ho i
        have hinter := ih.inter_of_isOpen_left (hd r) hopen
        simpa [hrs, inter_comm] using hinter
  simpa using hfin Finset.univ

/-- Compact-local open dense witness sets assemble over a sigma-compact configuration space into
one dense residual global witness set.  The witness may use different finite certificates on
different compact patches. -/
theorem globalWitness_dense_residual_of_sigmaCompact
    {X H : Type*} [TopologicalSpace X] [BaireSpace X]
    [TopologicalSpace H] [SigmaCompactSpace H]
    (Witness : X → H → Prop)
    (hcompact : ∀ K : Set H, IsCompact K →
      ∃ G : Set X, IsOpen G ∧ Dense G ∧
        ∀ x ∈ G, ∀ h ∈ K, Witness x h) :
    Dense {x | ∀ h, Witness x h} ∧ {x | ∀ h, Witness x h} ∈ residual X := by
  obtain ⟨K, hK, hcover⟩ := SigmaCompactSpace.exists_compact_covering (X := H)
  let G : ℕ → Set X := fun n => Classical.choose (hcompact (K n) (hK n))
  have hGopen : ∀ n, IsOpen (G n) := fun n =>
    (Classical.choose_spec (hcompact (K n) (hK n))).1
  have hGdense : ∀ n, Dense (G n) := fun n =>
    (Classical.choose_spec (hcompact (K n) (hK n))).2.1
  have hGwitness : ∀ n x, x ∈ G n → ∀ h ∈ K n, Witness x h := fun n =>
    (Classical.choose_spec (hcompact (K n) (hK n))).2.2
  have hresInter : (⋂ n, G n) ∈ residual X :=
    countable_iInter_mem.mpr fun n => residual_of_dense_open (hGopen n) (hGdense n)
  have hsubset : (⋂ n, G n) ⊆ {x | ∀ h, Witness x h} := by
    intro x hx h
    have hh : h ∈ ⋃ n, K n := by rw [hcover]; exact Set.mem_univ h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hh
    exact hGwitness n x (Set.mem_iInter.mp hx n) h hn
  have hres : {x | ∀ h, Witness x h} ∈ residual X :=
    Filter.mem_of_superset hresInter hsubset
  exact ⟨dense_of_mem_residual hres, hres⟩

/-- Extract the complete Nevanlinna control data from one combined row-packet chart. -/
theorem noncriticalProjectiveUpperGoodCombinedRowPacket_complete_data
    {row ι κ : Type*} [Fintype row]
    [Fintype ι] [DecidableEq (row × ι)] [Fintype κ]
    {C D : ℂ → ℂ} (hC : Differentiable ℂ C) (hD : Differentiable ℂ D)
    (forbidden : κ → ℂ) (packet : InjectiveProjectiveRowPacket row)
    {shift : InjectiveShiftConfiguration ι}
    (hgood : shift ∈ noncriticalProjectiveUpperGoodCombinedRowPacketSet
      (ι := ι) (κ := κ) C D forbidden packet) :
    (∀ x, C (combinedProjectiveRowShiftPacket packet shift x) ≠ 0) ∧
      Function.Injective (fun x => projectiveNevanlinnaQuotient C D
        (combinedProjectiveRowShiftPacket packet shift x)) ∧
      (∀ x k, projectiveNevanlinnaQuotient C D
        (combinedProjectiveRowShiftPacket packet shift x) ≠ forbidden k) ∧
      (∀ x, deriv (projectiveNevanlinnaQuotient C D)
        (combinedProjectiveRowShiftPacket packet shift x) ≠ 0) := by
  have hdata := noncriticalProjectiveSeparationProduct_complete_data
    hC hD forbidden (combinedProjectiveRowShiftPacket packet shift) hgood.1
  simpa [projectiveNevanlinnaQuotient] using hdata

/-- The literal affine node family on the ambient finite-dimensional shift packet space. -/
def ambientCombinedProjectiveNodes
    {row ι : Type*}
    (packet : InjectiveProjectiveRowPacket row) (shift : ι → ℂ) : row × ι → ℂ :=
  fun x => packet.1 x.1 + shift x.2

/-- Forget the built-in injectivity proof on a compact shift piece. -/
def ambientImageOfInjectiveShiftPiece
    {ι : Type*} (piece : Set (InjectiveShiftConfiguration ι)) :
    Set (ι → ℂ) :=
  Subtype.val '' piece

/-- The literal expanded evaluation packet of the actual Nevanlinna carrier at one tangent
parameter and one collision-free shift configuration. -/
def actualNevanlinnaExpandedPacketValue
    {row ι : Type} [Fintype row] [Fintype ι]
    (m0 a q : ℂ → ℂ) (orders : ι → ℕ)
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu]
    (baseDensity : Lp ℝ (⊤ : ENNReal) mu)
    (S : Submodule ℝ (Lp ℝ (⊤ : ENNReal) mu))
    (packet : InjectiveProjectiveRowPacket row)
    (w : S) (shift : InjectiveShiftConfiguration ι) :
    row × Fin (Fintype.card (Σ i, Fin (orders i))) → ℂ :=
  let control := projectiveNevanlinnaJetExpansionSmoothControl
    a q (fun x : row × ι => orders x.2) mu
      (ambientCombinedProjectiveNodes packet shift.1)
  let centered := reshapeCombinedJetsFinCLM row ι orders
    (control (baseDensity + w.1))
  fun p =>
    let s := (Fintype.equivFin (Σ i, Fin (orders i))).symm p.2
    iteratedDeriv s.2 m0 (packet.1 p.1 + shift.1 s.1) + centered p

/-- One complete row packet witnesses full coefficient-uniform expanded-evaluation rank. -/
def actualNevanlinnaExpandedFullRankWitness
    {row κ ι : Type} [Fintype row] [Fintype κ] [Fintype ι]
    (m0 a q : ℂ → ℂ) (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu]
    (baseDensity : Lp ℝ (⊤ : ENNReal) mu)
    (S : Submodule ℝ (Lp ℝ (⊤ : ENNReal) mu))
    (w : S) (shift : InjectiveShiftConfiguration ι) : Prop :=
  ∃ packet : InjectiveProjectiveRowPacket row,
    (∀ x, 0 < (combinedProjectiveRowShiftPacket packet shift x).im) ∧
      Function.Injective
        (expandedDifferentialEvaluationMatrix degree
          (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
          (actualNevanlinnaExpandedPacketValue
            m0 a q orders mu baseDensity S packet w shift)).mulVec

/-- A polynomial-coefficient relation of one finite expanded pattern holds on every admissible
evaluation packet.  This is the finite functional relation surface seen by the row geometry. -/
def actualNevanlinnaExpandedPatternRelationHolds
    {row κ ι : Type} [Fintype row] [Fintype κ] [Fintype ι]
    (m0 a q : ℂ → ℂ) (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu]
    (baseDensity : Lp ℝ (⊤ : ENNReal) mu)
    (S : Submodule ℝ (Lp ℝ (⊤ : ENNReal) mu))
    (w : S) (shift : InjectiveShiftConfiguration ι)
    (coeff : κ × Fin (degree + 1) → ℂ) : Prop :=
  ∀ packet : InjectiveProjectiveRowPacket row,
    (∀ x, 0 < (combinedProjectiveRowShiftPacket packet shift x).im) →
    ∀ r, ∑ col, coeff col *
      expandedDifferentialEvaluationMatrix degree
        (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
        (actualNevanlinnaExpandedPacketValue
          m0 a q orders mu baseDensity S packet w shift) r col = 0

/-- A complete full-rank row witness kills every coefficient of a finite functional relation. -/
theorem actualNevanlinnaExpandedPatternRelation_coefficients_eq_zero_of_fullRankWitness
    {row κ ι : Type} [Fintype row] [Fintype κ] [DecidableEq κ] [Fintype ι]
    (m0 a q : ℂ → ℂ) (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu]
    (baseDensity : Lp ℝ (⊤ : ENNReal) mu)
    (S : Submodule ℝ (Lp ℝ (⊤ : ENNReal) mu))
    (w : S) (shift : InjectiveShiftConfiguration ι)
    (hwitness : actualNevanlinnaExpandedFullRankWitness
      (row := row) (κ := κ) (ι := ι)
      m0 a q degree orders exponent mu baseDensity S w shift)
    (coeff : κ × Fin (degree + 1) → ℂ)
    (hrelation : actualNevanlinnaExpandedPatternRelationHolds
      (row := row) m0 a q degree orders exponent mu baseDensity S w shift coeff) :
    ∀ col, coeff col = 0 := by
  obtain ⟨packet, hupper, hinjective⟩ := hwitness
  let A := expandedDifferentialEvaluationMatrix degree
    (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
    (actualNevanlinnaExpandedPacketValue
      m0 a q orders mu baseDensity S packet w shift)
  have hmul : A.mulVec coeff = 0 := by
    funext r
    simpa [A, Matrix.mulVec, dotProduct, mul_comm] using hrelation packet hupper r
  have hcoeff : coeff = 0 := hinjective (by simpa [A] using hmul)
  intro col
  exact congrFun hcoeff col

/-- Countably simultaneous full-rank witnesses promote monotonically to coefficient rigidity for
every encoded finite relation pattern. -/
theorem countablePatterns_relationFree_dense_residual_of_fullRankWitness
    (row κ ι : ℕ → Type)
    [∀ n, Fintype (row n)]
    [∀ n, Fintype (κ n)] [∀ n, DecidableEq (κ n)]
    [∀ n, Fintype (ι n)]
    (m0 a q : ℂ → ℂ) (degree : ℕ → ℕ) (orders : ∀ n, ι n → ℕ)
    (exponent : ∀ n,
      κ n → (Fin (Fintype.card (Σ i, Fin (orders n i))) →₀ ℕ))
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu]
    (baseDensity : Lp ℝ (⊤ : ENNReal) mu)
    (S : Submodule ℝ (Lp ℝ (⊤ : ENNReal) mu))
    [BaireSpace S]
    (hfull :
      Dense {w : S | ∀ n (shift : InjectiveShiftConfiguration (ι n)),
        actualNevanlinnaExpandedFullRankWitness
          (row := row n) (κ := κ n) (ι := ι n)
          m0 a q (degree n) (orders n) (exponent n) mu baseDensity S w shift} ∧
      {w : S | ∀ n (shift : InjectiveShiftConfiguration (ι n)),
        actualNevanlinnaExpandedFullRankWitness
          (row := row n) (κ := κ n) (ι := ι n)
          m0 a q (degree n) (orders n) (exponent n) mu baseDensity S w shift} ∈ residual S) :
    let relationFree : Set S := {w | ∀ n (shift : InjectiveShiftConfiguration (ι n))
      (coeff : κ n × Fin (degree n + 1) → ℂ),
      actualNevanlinnaExpandedPatternRelationHolds
        (row := row n) m0 a q (degree n) (orders n) (exponent n)
          mu baseDensity S w shift coeff →
        ∀ col, coeff col = 0}
    Dense relationFree ∧ relationFree ∈ residual S := by
  dsimp only
  let full : Set S := {w | ∀ n (shift : InjectiveShiftConfiguration (ι n)),
    actualNevanlinnaExpandedFullRankWitness
      (row := row n) (κ := κ n) (ι := ι n)
      m0 a q (degree n) (orders n) (exponent n) mu baseDensity S w shift}
  let relationFree : Set S := {w | ∀ n (shift : InjectiveShiftConfiguration (ι n))
    (coeff : κ n × Fin (degree n + 1) → ℂ),
    actualNevanlinnaExpandedPatternRelationHolds
      (row := row n) m0 a q (degree n) (orders n) (exponent n)
        mu baseDensity S w shift coeff →
      ∀ col, coeff col = 0}
  have hsubset : full ⊆ relationFree := by
    intro w hw n shift coeff hrelation
    exact actualNevanlinnaExpandedPatternRelation_coefficients_eq_zero_of_fullRankWitness
      m0 a q (degree n) (orders n) (exponent n) mu baseDensity S w shift
      (hw n shift) coeff hrelation
  exact ⟨hfull.1.mono hsubset, Filter.mem_of_superset hfull.2 hsubset⟩

/-- **One complete atlas piece supplies the actual compact-patch density theorem.**  The theorem
derives an ambient open regularity collar and a positive uniform projective height from the compact
piece; it then instantiates the genuine smooth Nevanlinna row family and the uniform finite probe.
The only upper-half-plane hypothesis is the classical Nevanlinna mapping property of `-D/C`. -/
theorem compact_completeProjectiveRowPiece_has_dense_actualNevanlinna_finiteProbe
    {row κ ι ιf : Type}
    [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    [Fintype ιf] [DecidableEq ιf]
    {C D : ℂ → ℂ} (hC : Differentiable ℂ C) (hD : Differentiable ℂ D)
    (hupperMap : ∀ z, 0 < z.im → 0 < (projectiveNevanlinnaQuotient C D z).im)
    (m0 : ℂ → ℂ)
    (hm0 : ∀ k, ContDiffOn ℂ ⊤ (iteratedDeriv k m0) (projectiveRegularLocus C))
    (zf : ιf → ℂ)
    (hqf_inj : Function.Injective (fun i => projectiveNevanlinnaQuotient C D (zf i)))
    (hupperf : ∀ i, 0 < (projectiveNevanlinnaQuotient C D (zf i)).im)
    (nf : ιf → ℕ)
    (degree : ℕ) (orders : ι → ℕ)
    (packet : InjectiveProjectiveRowPacket row)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree < Fintype.card row)
    (mu : Measure (OnePoint ℝ)) [IsProbabilityMeasure mu] (hmu : mu.support.Infinite)
    (baseDensity : Lp ℝ (⊤ : ENNReal) mu)
    (piece : Set (InjectiveShiftConfiguration ι)) (hpiece : IsCompact piece)
    (hpieceChart : piece ⊆ noncriticalProjectiveUpperGoodCombinedRowPacketSet
      (ι := ι) (κ := ιf) C D
      (fun i => projectiveNevanlinnaQuotient C D (zf i)) packet)
    (hdim : Module.finrank ℝ (ι → ℂ) <
      2 * (Fintype.card row - Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    let a := projectiveNevanlinnaAmplitude C
    let q := projectiveNevanlinnaQuotient C D
    let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
      (fun i => q (zf i)) nf mu hupperf
    let S := LinearMap.ker frozen.toLinearMap
    ∃ V : Submodule ℝ S, V.FG ∧
      let nodes := ambientCombinedProjectiveNodes packet
      let control := fun h =>
        projectiveNevanlinnaJetExpansionSmoothControl
          a q (fun x : row × ι => orders x.2) mu (nodes h)
      let background := fun h p =>
        let s := (Fintype.equivFin (Σ i, Fin (orders i))).symm p.2
        iteratedDeriv s.2 m0 (nodes h (p.1, s.1))
      let base := fun h =>
        background h + reshapeCombinedJetsFinCLM row ι orders (control h baseDensity)
      let direction := fun h =>
        (reshapeCombinedJetsFinCLM row ι orders).comp ((control h).domRestrict S)
      Dense (compactConfigurationAvoidance
          (smoothAffineControlFamily base direction)
          (expandedDifferentialEvaluationRankDefect
            degree (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent)
          (ambientImageOfInjectiveShiftPiece piece)) ∧
        IsOpen (compactConfigurationAvoidance
          (smoothAffineControlFamily base direction)
          (expandedDifferentialEvaluationRankDefect
            degree (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent)
          (ambientImageOfInjectiveShiftPiece piece)) := by
  dsimp only
  let a := projectiveNevanlinnaAmplitude C
  let q := projectiveNevanlinnaQuotient C D
  let Omega := projectiveRegularLocus C
  let nodes : (ι → ℂ) → (row × ι → ℂ) :=
    ambientCombinedProjectiveNodes (row := row) (ι := ι) packet
  let K : Set (ι → ℂ) := ambientImageOfInjectiveShiftPiece (ι := ι) piece
  have hOmega : IsOpen Omega := projectiveRegularLocus_isOpen hC
  have hcoords := contDiffOn_projectiveNevanlinna_coordinates hC hD
  have ha : ContDiffOn ℂ ⊤ a Omega := hcoords.1
  have hq : ContDiffOn ℂ ⊤ q Omega := hcoords.2
  have hK : IsCompact K := hpiece.image continuous_subtype_val
  have hchartOpen := noncriticalProjectiveUpperGoodCombinedRowPacketSet_isOpen
    (row := row) (ι := ι) (κ := ιf) hC hD
      (fun i => q (zf i)) packet
  rw [isOpen_induced_iff] at hchartOpen
  obtain ⟨O, hOopen, hOeq⟩ := hchartOpen
  let U0 : Set (ι → ℂ) := O ∩ injectiveShiftConfigurationSet ι
  have hU0 : IsOpen U0 := hOopen.inter (injectiveShiftConfigurationSet_isOpen ι)
  have hchartU0 : ∀ (h : ι → ℂ) (hh : h ∈ U0),
      (⟨h, hh.2⟩ : InjectiveShiftConfiguration ι) ∈
        noncriticalProjectiveUpperGoodCombinedRowPacketSet
          (ι := ι) (κ := ιf) C D (fun i => q (zf i)) packet := by
    intro h hh
    have hpre : (⟨h, hh.2⟩ : InjectiveShiftConfiguration ι) ∈ Subtype.val ⁻¹' O := hh.1
    rw [hOeq] at hpre
    exact hpre
  have hKU0 : K ⊆ U0 := by
    intro h hh
    obtain ⟨shift, hshiftPiece, rfl⟩ := hh
    have hgood := hpieceChart hshiftPiece
    constructor
    · have hpre : shift ∈ Subtype.val ⁻¹' O := by
        rw [hOeq]
        exact hgood
      exact hpre
    · exact shift.2
  have hdataU0 : ∀ h ∈ U0,
      (∀ x, C (nodes h x) ≠ 0) ∧
        Function.Injective (fun x => q (nodes h x)) ∧
        (∀ x i, q (nodes h x) ≠ q (zf i)) ∧
        (∀ x, deriv q (nodes h x) ≠ 0) := by
    intro h hh
    have hdata := noncriticalProjectiveUpperGoodCombinedRowPacket_complete_data
      hC hD (fun i => q (zf i)) packet (hchartU0 h hh)
    simpa [nodes, ambientCombinedProjectiveNodes, q,
      projectiveNevanlinnaQuotient] using hdata
  have hnodesOmegaU0 : ∀ h ∈ U0, ∀ x, nodes h x ∈ Omega := by
    intro h hh x
    exact (hdataU0 h hh).1 x
  have hnodeContinuous : ∀ x, Continuous (fun h : ι → ℂ => nodes h x) := by
    intro x
    exact continuous_const.add (continuous_apply x.2)
  have hheightContinuousU0 : ∀ x, ContinuousOn
      (fun h : ι → ℂ => (q (nodes h x)).im) U0 := by
    intro x
    exact Complex.continuous_im.continuousOn.comp
      (hq.continuousOn.comp (hnodeContinuous x).continuousOn
        (fun h hh => hnodesOmegaU0 h hh x)) (fun _ _ => Set.mem_univ _)
  have hpositiveK : ∀ h ∈ K, ∀ x, 0 < (q (nodes h x)).im := by
    intro h hh x
    have h0 := hKU0 hh
    have hsource := (hchartU0 h h0).2 x
    exact hupperMap (nodes h x) hsource
  obtain ⟨η0, hη0, hη0K⟩ := compact_finite_strictPositive_uniformLowerBound
    K hK (fun h x => (q (nodes h x)).im)
      (fun x => (hheightContinuousU0 x).mono hKU0) hpositiveK
  let η : ℝ := η0 / 2
  have hη : 0 < η := by dsimp [η]; linarith
  let upperSet : row × ι → Set (ι → ℂ) := fun x =>
    U0 ∩ (fun h => (q (nodes h x)).im) ⁻¹' Set.Ioi η
  have hupperSetOpen : ∀ x, IsOpen (upperSet x) := by
    intro x
    exact (hheightContinuousU0 x).isOpen_inter_preimage hU0 isOpen_Ioi
  let U : Set (ι → ℂ) := U0 ∩ ⋂ x, upperSet x
  have hU : IsOpen U := hU0.inter (isOpen_iInter_of_finite hupperSetOpen)
  have hKU : K ⊆ U := by
    intro h hh
    refine ⟨hKU0 hh, Set.mem_iInter.mpr ?_⟩
    intro x
    refine ⟨hKU0 hh, ?_⟩
    change η < (q (nodes h x)).im
    have hle := hη0K h hh x
    dsimp [η]
    linarith
  have hnodes : ContDiff ℝ ⊤ nodes := by
    rw [contDiff_pi]
    intro x
    simpa [nodes, ambientCombinedProjectiveNodes] using
      (contDiff_const.add (contDiff_apply ℝ ℂ x.2))
  let background : (ι → ℂ) →
      (row × Fin (Fintype.card (Σ i, Fin (orders i))) → ℂ) := fun h p =>
    let s := (Fintype.equivFin (Σ i, Fin (orders i))).symm p.2
    iteratedDeriv s.2 m0 (nodes h (p.1, s.1))
  have hnodesOmega : ∀ h ∈ U, ∀ x, nodes h x ∈ Omega := by
    intro h hh x
    exact hnodesOmegaU0 h hh.1 x
  have hbackground : ContDiffOn ℝ ⊤ background U := by
    apply contDiffOn_pi'
    intro p
    let s := (Fintype.equivFin (Σ i, Fin (orders i))).symm p.2
    have hnode : ContDiff ℝ ⊤ (fun h : ι → ℂ => nodes h (p.1, s.1)) := by
      simpa [nodes, ambientCombinedProjectiveNodes] using
        (contDiff_const.add (contDiff_apply ℝ ℂ s.1))
    have hjetReal : ContDiffOn ℝ ⊤ (iteratedDeriv s.2 m0) Omega :=
      contDiffOn_real_of_contDiffOn_complex_of_isOpen hOmega (hm0 s.2)
    simpa [background, s] using hjetReal.comp hnode.contDiffOn
      (fun h hh => hnodesOmega h hh (p.1, s.1))
  have hupper : ∀ h ∈ U, ∀ x, η ≤ (q (nodes h x)).im := by
    intro h hh x
    have hx := Set.mem_iInter.mp hh.2 x
    exact hx.2.le
  have hqt_inj : ∀ h ∈ K, Function.Injective (fun x => q (nodes h x)) := by
    intro h hh
    exact (hdataU0 h (hKU0 hh)).2.1
  have hcross : ∀ h ∈ K, ∀ i x, q (zf i) ≠ q (nodes h x) := by
    intro h hh i x
    exact ((hdataU0 h (hKU0 hh)).2.2.1 x i).symm
  have hat : ∀ h ∈ K, ∀ x, a (nodes h x) ≠ 0 := by
    intro h hh x
    have hCnode := (hdataU0 h (hKU0 hh)).1 x
    exact div_ne_zero (neg_ne_zero.mpr one_ne_zero) (pow_ne_zero 2 hCnode)
  have hqdt : ∀ h ∈ K, ∀ x, deriv q (nodes h x) ≠ 0 := by
    intro h hh x
    exact (hdataU0 h (hKU0 hh)).2.2.2 x
  obtain ⟨V, hVfg, hDense⟩ :=
    compact_translatedNevanlinnaExpandedEvaluation_has_dense_finiteProbe
    a q Omega hOmega ha hq η hη
    zf hqf_inj hupperf nf degree orders packet.1 packet.2
    exponent hexponent hrows mu hmu baseDensity background nodes hnodes U K hU hK hKU
    hbackground
    hnodesOmega hupper hqt_inj hcross hat hqdt hdim
  refine ⟨V, hVfg, hDense, ?_⟩
  let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
    (fun i => q (zf i)) nf mu hupperf
  let S := LinearMap.ker frozen.toLinearMap
  let control := fun h =>
    projectiveNevanlinnaJetExpansionSmoothControl
      a q (fun x : row × ι => orders x.2) mu (nodes h)
  let base := fun h =>
    background h + reshapeCombinedJetsFinCLM row ι orders (control h baseDensity)
  let direction := fun h =>
    (reshapeCombinedJetsFinCLM row ι orders).comp ((control h).domRestrict S)
  have hcontrol : ContDiffOn ℝ ⊤ control U := by
    exact (contDiffOn_projectiveNevanlinnaJetExpansionSmoothControl_within
      a q hOmega ha hq (fun x : row × ι => orders x.2) mu).comp hnodes.contDiffOn
        (fun h hh => ⟨fun x => hη.trans_le (hupper h hh x),
          fun x _ => hnodesOmega h hh x⟩)
  have hbase : ContDiffOn ℝ ⊤ base U := by
    exact hbackground.add
      ((reshapeCombinedJetsFinCLM row ι orders).contDiff.comp_contDiffOn
        (hcontrol.clm_apply contDiffOn_const))
  have hdirection : ContDiffOn ℝ ⊤ direction U := by
    have hS : ContDiffOn ℝ ⊤ (fun h => (control h).domRestrict S) U := by
      have hsubS : ContDiffOn ℝ ⊤ (fun _ : ι → ℂ => S.subtypeL) U := contDiffOn_const
      simpa only [ContinuousLinearMap.domRestrict] using hcontrol.clm_comp hsubS
    have hreindex : ContDiffOn ℝ ⊤
        (fun _ : ι → ℂ => reshapeCombinedJetsFinCLM row ι orders) U := contDiffOn_const
    simpa only [direction] using hreindex.clm_comp hS
  have hopen := compactConfigurationAvoidance_isOpen_of_continuousOn_open
    (smoothAffineControlFamily base direction)
    (expandedDifferentialEvaluationRankDefect
      degree (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent)
    (expandedDifferentialEvaluationRankDefect_isClosed
      degree (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent)
    U hU (contDiffOn_smoothAffineControlFamily hbase hdirection).continuousOn
    K hK hKU
  simpa [frozen, S, control, background, base, direction, K, nodes, a, q] using hopen

/-- **Compact-patch complete-atlas density law.**  A compact collision-free shift patch admits a
finite compact refinement by complete combined row charts.  For one and the same frozen tangent,
the actual Nevanlinna expanded-evaluation rank condition on every member of that finite atlas is
open dense.  Thus every shift in the original compact patch has at least one simultaneous row
packet witnessing full coefficient-uniform rank. -/
theorem compact_injectiveShiftPatch_has_dense_completeAtlas_actualNevanlinna
    {row κ ι ιf : Type}
    [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    [Fintype ιf] [DecidableEq ιf]
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C) (hD : Differentiable ℂ D)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {p : ℂ} (hCp : C p = 0) {c : ℂ} (hCc : C c ≠ 0)
    (hupperMap : ∀ z, 0 < z.im → 0 < (projectiveNevanlinnaQuotient C D z).im)
    (m0 : ℂ → ℂ)
    (hm0 : ∀ k, ContDiffOn ℂ ⊤ (iteratedDeriv k m0) (projectiveRegularLocus C))
    (zf : ιf → ℂ)
    (hqf_inj : Function.Injective (fun i => projectiveNevanlinnaQuotient C D (zf i)))
    (hupperf : ∀ i, 0 < (projectiveNevanlinnaQuotient C D (zf i)).im)
    (nf : ιf → ℕ)
    (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree < Fintype.card row)
    (mu : Measure (OnePoint ℝ)) [IsProbabilityMeasure mu] (hmu : mu.support.Infinite)
    (baseDensity : Lp ℝ (⊤ : ENNReal) mu)
    (Kshift : Set (InjectiveShiftConfiguration ι)) (hKshift : IsCompact Kshift)
    (hdim : Module.finrank ℝ (ι → ℂ) <
      2 * (Fintype.card row - Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    let a := projectiveNevanlinnaAmplitude C
    let q := projectiveNevanlinnaQuotient C D
    let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
      (fun i => q (zf i)) nf mu hupperf
    let S := LinearMap.ker frozen.toLinearMap
    ∃ n : ℕ, ∃ packets : Fin n → InjectiveProjectiveRowPacket row,
      ∃ pieces : Fin n → Set (InjectiveShiftConfiguration ι),
        Kshift ⊆ ⋃ j, pieces j ∧
        (∀ j, IsCompact (pieces j)) ∧
        (∀ j, pieces j ⊆ noncriticalProjectiveUpperGoodCombinedRowPacketSet
          (ι := ι) (κ := ιf) C D (fun i => q (zf i)) (packets j)) ∧
        let nodes := fun j => ambientCombinedProjectiveNodes (packets j)
        let control := fun j h =>
          projectiveNevanlinnaJetExpansionSmoothControl
            a q (fun x : row × ι => orders x.2) mu (nodes j h)
        let background := fun j h
            (p : row × Fin (Fintype.card (Σ i, Fin (orders i)))) =>
          let s := (Fintype.equivFin (Σ i, Fin (orders i))).symm p.2
          iteratedDeriv s.2 m0 (nodes j h (p.1, s.1))
        let base := fun j h =>
          background j h + reshapeCombinedJetsFinCLM row ι orders (control j h baseDensity)
        let direction := fun j h =>
          (reshapeCombinedJetsFinCLM row ι orders).comp ((control j h).domRestrict S)
        let good := fun j => compactConfigurationAvoidance
          (smoothAffineControlFamily (base j) (direction j))
          (expandedDifferentialEvaluationRankDefect
            degree (Fintype.card (Σ i, Fin (orders i))) (packets j).1 exponent)
          (ambientImageOfInjectiveShiftPiece (pieces j))
        Dense (⋂ j, good j) ∧ IsOpen (⋂ j, good j) ∧
          ∀ w ∈ ⋂ j, good j, ∀ shift ∈ Kshift,
            actualNevanlinnaExpandedFullRankWitness
              (row := row) (κ := κ) (ι := ι)
              m0 a q degree orders exponent mu baseDensity S w shift := by
  dsimp only
  let a := projectiveNevanlinnaAmplitude C
  let q := projectiveNevanlinnaQuotient C D
  let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
    (fun i => q (zf i)) nf mu hupperf
  let S := LinearMap.ker frozen.toLinearMap
  letI normedAddCommGroupS : NormedAddCommGroup S := Submodule.normedAddCommGroup S
  letI : NormedSpace ℝ S := Submodule.normedSpace S
  obtain ⟨n, packets, pieces, hcover, hpiecesCompact, hpiecesChart⟩ :=
    compact_injectiveShiftPatch_finite_noncriticalProjectiveUpperGoodCombinedRowPacket_refinement
      (row := row) (ι := ι) (κ := ιf) hCmin hD hnoCommon hCp hCc
      (fun i => q (zf i)) hKshift
  let nodes : Fin n → (ι → ℂ) → (row × ι → ℂ) := fun j =>
    ambientCombinedProjectiveNodes (row := row) (ι := ι) (packets j)
  let control := fun j h =>
    projectiveNevanlinnaJetExpansionSmoothControl
      a q (fun x : row × ι => orders x.2) mu (nodes j h)
  let background := fun j h
      (p : row × Fin (Fintype.card (Σ i, Fin (orders i)))) =>
    let s := (Fintype.equivFin (Σ i, Fin (orders i))).symm p.2
    iteratedDeriv s.2 m0 (nodes j h (p.1, s.1))
  let base := fun j h =>
    background j h + reshapeCombinedJetsFinCLM row ι orders (control j h baseDensity)
  let direction := fun j h =>
    (reshapeCombinedJetsFinCLM row ι orders).comp ((control j h).domRestrict S)
  let good := fun j => compactConfigurationAvoidance
    (smoothAffineControlFamily (base j) (direction j))
    (expandedDifferentialEvaluationRankDefect
      degree (Fintype.card (Σ i, Fin (orders i))) (packets j).1 exponent)
    (ambientImageOfInjectiveShiftPiece (pieces j))
  have hgood : ∀ j, Dense (good j) ∧ IsOpen (good j) := by
    intro j
    obtain ⟨V, hVfg, hj⟩ :=
      compact_completeProjectiveRowPiece_has_dense_actualNevanlinna_finiteProbe
        hCmin.1 hD hupperMap
        m0 hm0
        zf hqf_inj hupperf nf degree orders (packets j)
        exponent hexponent hrows mu hmu baseDensity (pieces j)
        (hpiecesCompact j) (hpiecesChart j) hdim
    simpa [good, nodes, control, background, base, direction, frozen, S, a, q] using hj
  refine ⟨n, packets, pieces, hcover, hpiecesCompact, hpiecesChart, ?_, ?_, ?_⟩
  · exact dense_iInter_of_finite_isOpen good
      (fun j => (hgood j).2) (fun j => (hgood j).1)
  · exact isOpen_iInter_of_finite (fun j => (hgood j).2)
  · intro w hw shift hshift
    obtain ⟨j, hjpiece⟩ := Set.mem_iUnion.mp (hcover hshift)
    refine ⟨packets j, (hpiecesChart j hjpiece).2, ?_⟩
    have hjgood := Set.mem_iInter.mp hw j
    have hambient : shift.1 ∈ ambientImageOfInjectiveShiftPiece (pieces j) :=
      ⟨shift, hjpiece, rfl⟩
    have havoid := hjgood shift.1 hambient
    have hinjective : Function.Injective
        (expandedDifferentialEvaluationMatrix degree
          (Fintype.card (Σ i, Fin (orders i))) (packets j).1 exponent
          (smoothAffineControlFamily (base j) (direction j) (w, shift.1))).mulVec := by
      simpa only [mem_expandedDifferentialEvaluationRankDefect_iff, not_not] using havoid
    have hfamily : smoothAffineControlFamily (base j) (direction j) (w, shift.1) =
        actualNevanlinnaExpandedPacketValue
          m0 a q orders mu baseDensity S (packets j) w shift := by
      funext p
      simp [smoothAffineControlFamily, background, base, direction, control, nodes,
        actualNevanlinnaExpandedPacketValue, ambientCombinedProjectiveNodes,
        ContinuousLinearMap.domRestrict_apply, map_add, add_assoc]
    simpa [hfamily] using hinjective

/-- **Global all-shift rank law for one finite differential-relation pattern.**  The compact atlas
law and sigma-compactness of the collision-free shift configuration space produce one dense
residual subset of the frozen tangent on which every distinct shift tuple has a complete row
packet witnessing full expanded-evaluation rank. -/
theorem global_injectiveShifts_actualNevanlinna_fullRankWitness_dense_residual
    {row κ ι ιf : Type}
    [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    [Fintype ιf] [DecidableEq ιf]
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C) (hD : Differentiable ℂ D)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {p : ℂ} (hCp : C p = 0) {c : ℂ} (hCc : C c ≠ 0)
    (hupperMap : ∀ z, 0 < z.im → 0 < (projectiveNevanlinnaQuotient C D z).im)
    (m0 : ℂ → ℂ)
    (hm0 : ∀ k, ContDiffOn ℂ ⊤ (iteratedDeriv k m0) (projectiveRegularLocus C))
    (zf : ιf → ℂ)
    (hqf_inj : Function.Injective (fun i => projectiveNevanlinnaQuotient C D (zf i)))
    (hupperf : ∀ i, 0 < (projectiveNevanlinnaQuotient C D (zf i)).im)
    (nf : ιf → ℕ)
    (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree < Fintype.card row)
    (mu : Measure (OnePoint ℝ)) [IsProbabilityMeasure mu] (hmu : mu.support.Infinite)
    (baseDensity : Lp ℝ (⊤ : ENNReal) mu)
    (hdim : Module.finrank ℝ (ι → ℂ) <
      2 * (Fintype.card row - Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    let a := projectiveNevanlinnaAmplitude C
    let q := projectiveNevanlinnaQuotient C D
    let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
      (fun i => q (zf i)) nf mu hupperf
    let S := LinearMap.ker frozen.toLinearMap
    let good : Set S := {w | ∀ shift : InjectiveShiftConfiguration ι,
      actualNevanlinnaExpandedFullRankWitness
        (row := row) (κ := κ) (ι := ι)
        m0 a q degree orders exponent mu baseDensity S w shift}
    Dense good ∧ good ∈ residual S := by
  dsimp only
  let a := projectiveNevanlinnaAmplitude C
  let q := projectiveNevanlinnaQuotient C D
  let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
    (fun i => q (zf i)) nf mu hupperf
  let S := LinearMap.ker frozen.toLinearMap
  letI normedAddCommGroupS : NormedAddCommGroup S := Submodule.normedAddCommGroup S
  letI : NormedSpace ℝ S := Submodule.normedSpace S
  have hSclosed : IsClosed (S : Set (Lp ℝ (⊤ : ENNReal) mu)) := frozen.isClosed_ker
  letI : CompleteSpace S := hSclosed.completeSpace_coe
  letI : BaireSpace S := by
    set_option synthInstance.maxHeartbeats 100000 in
      infer_instance
  apply globalWitness_dense_residual_of_sigmaCompact
    (fun w (shift : InjectiveShiftConfiguration ι) =>
      actualNevanlinnaExpandedFullRankWitness
        (row := row) (κ := κ) (ι := ι)
        m0 a q degree orders exponent mu baseDensity S w shift)
  intro Kshift hKshift
  obtain ⟨n, packets, pieces, hcover, hpiecesCompact, hpiecesChart,
      hDense, hOpen, hWitness⟩ :=
    compact_injectiveShiftPatch_has_dense_completeAtlas_actualNevanlinna
      hCmin hD hnoCommon hCp hCc hupperMap
      m0 hm0
      zf hqf_inj hupperf nf degree orders exponent hexponent hrows
      mu hmu baseDensity Kshift hKshift hdim
  exact ⟨_, hOpen, hDense, hWitness⟩

/-- **Countable all-pattern all-shift rank law.**  One dense residual subset of the frozen tangent
simultaneously has complete row-packet witnesses for every pattern in a countable family and every
tuple of distinct complex shifts. -/
theorem countablePatterns_global_injectiveShifts_actualNevanlinna_fullRankWitness_dense_residual
    (row κ ι : ℕ → Type)
    [∀ n, Fintype (row n)] [∀ n, DecidableEq (row n)]
    [∀ n, Fintype (κ n)] [∀ n, DecidableEq (κ n)]
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    {ιf : Type} [Fintype ιf] [DecidableEq ιf]
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C) (hD : Differentiable ℂ D)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {p : ℂ} (hCp : C p = 0) {c : ℂ} (hCc : C c ≠ 0)
    (hupperMap : ∀ z, 0 < z.im → 0 < (projectiveNevanlinnaQuotient C D z).im)
    (m0 : ℂ → ℂ)
    (hm0 : ∀ k, ContDiffOn ℂ ⊤ (iteratedDeriv k m0) (projectiveRegularLocus C))
    (zf : ιf → ℂ)
    (hqf_inj : Function.Injective (fun i => projectiveNevanlinnaQuotient C D (zf i)))
    (hupperf : ∀ i, 0 < (projectiveNevanlinnaQuotient C D (zf i)).im)
    (nf : ιf → ℕ)
    (degree : ℕ → ℕ) (orders : ∀ n, ι n → ℕ)
    (exponent : ∀ n,
      κ n → (Fin (Fintype.card (Σ i, Fin (orders n i))) →₀ ℕ))
    (hexponent : ∀ n, Function.Injective (exponent n))
    (hrows : ∀ n,
      Fintype.card (κ n × Fin (degree n + 1)) + degree n < Fintype.card (row n))
    (mu : Measure (OnePoint ℝ)) [IsProbabilityMeasure mu] (hmu : mu.support.Infinite)
    (baseDensity : Lp ℝ (⊤ : ENNReal) mu)
    (hdim : ∀ n, Module.finrank ℝ (ι n → ℂ) <
      2 * (Fintype.card (row n) -
        Fintype.card (κ n × Fin (degree n + 1)) - degree n + 1)) :
    let a := projectiveNevanlinnaAmplitude C
    let q := projectiveNevanlinnaQuotient C D
    let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
      (fun i => q (zf i)) nf mu hupperf
    let S := LinearMap.ker frozen.toLinearMap
    let good : Set S := {w | ∀ n (shift : InjectiveShiftConfiguration (ι n)),
      actualNevanlinnaExpandedFullRankWitness
        (row := row n) (κ := κ n) (ι := ι n)
        m0 a q (degree n) (orders n) (exponent n) mu baseDensity S w shift}
    Dense good ∧ good ∈ residual S := by
  dsimp only
  let a := projectiveNevanlinnaAmplitude C
  let q := projectiveNevanlinnaQuotient C D
  let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
    (fun i => q (zf i)) nf mu hupperf
  let S := LinearMap.ker frozen.toLinearMap
  letI normedAddCommGroupS : NormedAddCommGroup S := Submodule.normedAddCommGroup S
  letI : NormedSpace ℝ S := Submodule.normedSpace S
  have hSclosed : IsClosed (S : Set (Lp ℝ (⊤ : ENNReal) mu)) := frozen.isClosed_ker
  letI : CompleteSpace S := hSclosed.completeSpace_coe
  letI : BaireSpace S := by
    set_option synthInstance.maxHeartbeats 100000 in
      infer_instance
  let goodPattern : ℕ → Set S := fun n =>
    {w | ∀ shift : InjectiveShiftConfiguration (ι n),
      actualNevanlinnaExpandedFullRankWitness
        (row := row n) (κ := κ n) (ι := ι n)
        m0 a q (degree n) (orders n) (exponent n) mu baseDensity S w shift}
  have hgoodPattern : ∀ n, Dense (goodPattern n) ∧ goodPattern n ∈ residual S := by
    intro n
    simpa [goodPattern, a, q, frozen, S] using
      (global_injectiveShifts_actualNevanlinna_fullRankWitness_dense_residual
        hCmin hD hnoCommon hCp hCc hupperMap
        m0 hm0
        zf hqf_inj hupperf nf (degree n) (orders n) (exponent n)
        (hexponent n) (hrows n) mu hmu baseDensity (hdim n))
  have hres : (⋂ n, goodPattern n) ∈ residual S :=
    countable_iInter_mem.mpr fun n => (hgoodPattern n).2
  have heq : (⋂ n, goodPattern n) =
      {w | ∀ n (shift : InjectiveShiftConfiguration (ι n)),
        actualNevanlinnaExpandedFullRankWitness
          (row := row n) (κ := κ n) (ι := ι n)
          m0 a q (degree n) (orders n) (exponent n) mu baseDensity S w shift} := by
    ext w
    simp only [Set.mem_iInter, goodPattern, Set.mem_setOf_eq]
  rw [heq] at hres
  exact ⟨dense_of_mem_residual hres, hres⟩

/-- **Actual Nevanlinna countable-pattern relation-rigidity capstone.**  Under the exact classical
projective-incidence, stratified-transversality, and Nevanlinna upper-mapping inputs, a dense
residual subset of every frozen tangent satisfies coefficient rigidity for every encoded finite
differential pattern and every tuple of distinct complex shifts. -/
theorem countablePatterns_actualNevanlinna_relationFree_dense_residual
    (row κ ι : ℕ → Type)
    [∀ n, Fintype (row n)] [∀ n, DecidableEq (row n)]
    [∀ n, Fintype (κ n)] [∀ n, DecidableEq (κ n)]
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    {ιf : Type} [Fintype ιf] [DecidableEq ιf]
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C) (hD : Differentiable ℂ D)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {p : ℂ} (hCp : C p = 0) {c : ℂ} (hCc : C c ≠ 0)
    (hupperMap : ∀ z, 0 < z.im → 0 < (projectiveNevanlinnaQuotient C D z).im)
    (m0 : ℂ → ℂ)
    (hm0 : ∀ k, ContDiffOn ℂ ⊤ (iteratedDeriv k m0) (projectiveRegularLocus C))
    (zf : ιf → ℂ)
    (hqf_inj : Function.Injective (fun i => projectiveNevanlinnaQuotient C D (zf i)))
    (hupperf : ∀ i, 0 < (projectiveNevanlinnaQuotient C D (zf i)).im)
    (nf : ιf → ℕ)
    (degree : ℕ → ℕ) (orders : ∀ n, ι n → ℕ)
    (exponent : ∀ n,
      κ n → (Fin (Fintype.card (Σ i, Fin (orders n i))) →₀ ℕ))
    (hexponent : ∀ n, Function.Injective (exponent n))
    (hrows : ∀ n,
      Fintype.card (κ n × Fin (degree n + 1)) + degree n < Fintype.card (row n))
    (mu : Measure (OnePoint ℝ)) [IsProbabilityMeasure mu] (hmu : mu.support.Infinite)
    (baseDensity : Lp ℝ (⊤ : ENNReal) mu)
    (hdim : ∀ n, Module.finrank ℝ (ι n → ℂ) <
      2 * (Fintype.card (row n) -
        Fintype.card (κ n × Fin (degree n + 1)) - degree n + 1)) :
    let a := projectiveNevanlinnaAmplitude C
    let q := projectiveNevanlinnaQuotient C D
    let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
      (fun i => q (zf i)) nf mu hupperf
    let S := LinearMap.ker frozen.toLinearMap
    let relationFree : Set S := {w | ∀ n (shift : InjectiveShiftConfiguration (ι n))
      (coeff : κ n × Fin (degree n + 1) → ℂ),
      actualNevanlinnaExpandedPatternRelationHolds
        (row := row n) m0 a q (degree n) (orders n) (exponent n)
          mu baseDensity S w shift coeff →
        ∀ col, coeff col = 0}
    Dense relationFree ∧ relationFree ∈ residual S := by
  dsimp only
  let a := projectiveNevanlinnaAmplitude C
  let q := projectiveNevanlinnaQuotient C D
  let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
    (fun i => q (zf i)) nf mu hupperf
  let S := LinearMap.ker frozen.toLinearMap
  letI normedAddCommGroupS : NormedAddCommGroup S := Submodule.normedAddCommGroup S
  letI : NormedSpace ℝ S := Submodule.normedSpace S
  have hSclosed : IsClosed (S : Set (Lp ℝ (⊤ : ENNReal) mu)) := frozen.isClosed_ker
  letI : CompleteSpace S := hSclosed.completeSpace_coe
  letI : BaireSpace S := by
    set_option synthInstance.maxHeartbeats 100000 in
      infer_instance
  have hfull :=
    countablePatterns_global_injectiveShifts_actualNevanlinna_fullRankWitness_dense_residual
      row κ ι hCmin hD hnoCommon hCp hCc
      hupperMap m0 hm0 zf hqf_inj hupperf nf degree orders exponent
      hexponent hrows mu hmu baseDensity hdim
  exact countablePatterns_relationFree_dense_residual_of_fullRankWitness
    row κ ι m0 a q degree orders exponent mu baseDensity S hfull

end

end GaloisForLFunctions.HTGeometry
