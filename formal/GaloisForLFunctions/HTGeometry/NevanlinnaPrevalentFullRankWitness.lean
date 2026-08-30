import GaloisForLFunctions.HTGeometry.NevanlinnaProjectiveUniformFiniteProbe
import GaloisForLFunctions.HTGeometry.PrevalentCountableIntersection

/-!
# The actual-Nevanlinna full-rank phase is prevalent, not merely residual

A compact configuration patch is covered by finitely many complete row charts, each carrying its
own smooth affine control family.  One finite probe that is onto over every chart therefore avoids
the expanded-evaluation rank defect on the whole patch, and — because the probe is Euclidean and
the bad parameter set is Lebesgue null — it does so with probability one, after every deterministic
recentring and for every positive amplitude.  Merging the countably many blocks of a countable
pattern/patch enumeration into one convergent random series upgrades the corpus's dense residual
rank law to a block-prevalence law.
-/

open MeasureTheory Set Topology
open scoped ENNReal NNReal OnePoint

namespace GaloisForLFunctions.HTGeometry

/-- Scaling a probe by a nonzero amplitude preserves controllability. -/
theorem surjective_comp_smul {X Y Z : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    [SeminormedAddCommGroup Y] [NormedSpace ℝ Y] [SeminormedAddCommGroup Z] [NormedSpace ℝ Z]
    (T : X →L[ℝ] Y) (l : Z →L[ℝ] X) {c : ℝ} (hc : c ≠ 0)
    (h : Function.Surjective (T.comp l)) : Function.Surjective (T.comp (c • l)) := by
  intro y
  obtain ⟨z, hz⟩ := h (c⁻¹ • y)
  refine ⟨z, ?_⟩
  have hval : (T.comp (c • l)) z = c • ((T.comp l) z) := by
    simp [ContinuousLinearMap.comp_apply]
  rw [hval, hz, smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- **Block-controlled avoidance over a finite atlas.**  The simultaneous avoidance phase of a
finite family of smooth affine control pieces is open, and one Euclidean probe that is onto over
every piece makes it full for every absolutely continuous parameter law, every positive amplitude
and every deterministic recentring. -/
theorem blockControlled_finite_atlas
    {X H Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    {n : ℕ} {Dblk : ℕ}
    (base : Fin n → H → Y) (direction : Fin n → H → (X →L[ℝ] Y))
    (bad : Fin n → Set Y) (hbad : ∀ j, IsClosed (bad j)) (codim : ℕ)
    (U K : Fin n → Set H)
    (hU : ∀ j, IsOpen (U j)) (hKU : ∀ j, K j ⊆ U j) (hK : ∀ j, IsCompact (K j))
    (hbase : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (base j) (U j))
    (hdirection : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (direction j) (U j))
    (l : (Fin Dblk → ℝ) →L[ℝ] X)
    (hsurj : ∀ j, ∀ h ∈ K j, Function.Surjective ((direction j h).comp l))
    (hstrata : ∀ j, FiniteRegularStratification (bad j) codim)
    (hdim : Module.finrank ℝ H < codim) :
    IsOpen (⋂ j, compactConfigurationAvoidance
        (smoothAffineControlFamily (base j) (direction j)) (bad j) (K j)) ∧
      ∀ γ : ℝ, 0 < γ → ∀ center : X, ∀ μ : Measure (Fin Dblk → ℝ), μ ≪ volume →
        μ {p | center + (γ • l) p ∉ ⋂ j, compactConfigurationAvoidance
            (smoothAffineControlFamily (base j) (direction j)) (bad j) (K j)} = 0 := by
  classical
  set good : Fin n → Set X := fun j => compactConfigurationAvoidance
    (smoothAffineControlFamily (base j) (direction j)) (bad j) (K j) with hgood
  have hopen : ∀ j, IsOpen (good j) := by
    intro j
    exact compactConfigurationAvoidance_isOpen_of_continuousOn_open
      (smoothAffineControlFamily (base j) (direction j)) (bad j) (hbad j) (U j) (hU j)
      (contDiffOn_smoothAffineControlFamily (hbase j) (hdirection j)).continuousOn
      (K j) (hK j) (hKU j)
  refine ⟨isOpen_iInter_of_finite hopen, ?_⟩
  intro γ hγ center μ hμ
  have hγne : γ ≠ 0 := ne_of_gt hγ
  set lc : (Fin Dblk → ℝ) →L[ℝ] X := γ • l with hlc
  have hcompL : Continuous (fun T : X →L[ℝ] Y => T.comp lc) :=
    ((ContinuousLinearMap.compL ℝ (Fin Dblk → ℝ) X Y).flip lc).continuous
  have hnull : ∀ j, μ {p : Fin Dblk → ℝ | ∃ h ∈ K j,
      smoothAffineControlFamily (base j) (direction j) (center + lc p, h) ∈ bad j} = 0 := by
    intro j
    have hU'open : IsOpen (U j ∩ {h | Function.Surjective ((direction j h).comp lc)}) :=
      isOpen_inter_surjective_continuousLinearMap_family
        (fun h => (direction j h).comp lc) (U j) (hU j)
        (hcompL.comp_continuousOn (hdirection j).continuousOn)
    have hKU' : K j ⊆ U j ∩ {h | Function.Surjective ((direction j h).comp lc)} := by
      intro h hh
      exact ⟨hKU j hh, surjective_comp_smul (direction j h) l hγne (hsurj j h hh)⟩
    exact measure_recentred_parameter_bad_eq_zero lc (base j) (direction j) (bad j) codim
      (U j ∩ {h | Function.Surjective ((direction j h).comp lc)}) (K j)
      hU'open hKU' ((hbase j).mono Set.inter_subset_left)
      ((hdirection j).mono Set.inter_subset_left) (fun h hh => hh.2) (hstrata j) hdim μ hμ center
  have hcover : {p : Fin Dblk → ℝ | center + lc p ∉ ⋂ j, good j}
      = ⋃ j, {p : Fin Dblk → ℝ | ∃ h ∈ K j,
          smoothAffineControlFamily (base j) (direction j) (center + lc p, h) ∈ bad j} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, hgood,
      compactConfigurationAvoidance]
    push Not
    rfl
  rw [hcover]
  exact measure_iUnion_null hnull

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem compact_injectiveShiftPatch_blockControlled_completeAtlas_actualNevanlinna
    {row κ ι ιf : Type}
    [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    [Fintype ιf] [DecidableEq ιf]
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C) (hD : Differentiable ℂ D)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {pz : ℂ} (hCp : C pz = 0) {cz : ℂ} (hCc : C cz ≠ 0)
    (hupperMap : ∀ z, z.im < 0 → 0 < (projectiveNevanlinnaQuotient C D z).im)
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
    ∃ (Dblk : ℕ) (l : (Fin Dblk → ℝ) →L[ℝ] S) (G : Set S), IsOpen G ∧
      (∀ γ : ℝ, 0 < γ → ∀ center : S, ∀ μ : Measure (Fin Dblk → ℝ), μ ≪ volume →
        μ {pp | center + (γ • l) pp ∉ G} = 0) ∧
      ∀ w ∈ G, ∀ shift ∈ Kshift,
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
    compact_injectiveShiftPatch_finite_noncriticalProjectiveLowerGoodCombinedRowPacket_refinement
      (row := row) (ι := ι) (κ := ιf) hCmin hD hnoCommon hCp hCc
      (fun i => q (zf i)) hKshift
  let nodes : Fin n → (ι → ℂ) → (row × ι → ℂ) := fun j =>
    ambientCombinedProjectiveNodes (row := row) (ι := ι) (packets j)
  let control := fun j h =>
    projectiveNevanlinnaJetExpansionSmoothControl
      a q (fun x : row × ι => orders x.2) mu (nodes j h)
  let background := fun j h
      (pt : row × Fin (Fintype.card (Σ i, Fin (orders i)))) =>
    let s := (Fintype.equivFin (Σ i, Fin (orders i))).symm pt.2
    iteratedDeriv s.2 m0 (nodes j h (pt.1, s.1))
  let base := fun j h =>
    background j h + reshapeCombinedJetsFinCLM row ι orders (control j h baseDensity)
  let direction := fun j h =>
    (reshapeCombinedJetsFinCLM row ι orders).comp ((control j h).domRestrict S)
  let Kj : Fin n → Set (ι → ℂ) := fun j => ambientImageOfInjectiveShiftPiece (pieces j)
  have hprobe : ∀ j : Fin n, ∃ (dd : ℕ) (v : Fin dd → S) (U : Set (ι → ℂ)),
      IsOpen U ∧ Kj j ⊆ U ∧ ContDiffOn ℝ ⊤ (base j) U ∧ ContDiffOn ℝ ⊤ (direction j) U ∧
      ∀ h ∈ Kj j, Function.Surjective ((direction j h).comp (blockCLM v)) := by
    intro j
    obtain ⟨dd, v, U, hj⟩ := compact_completeProjectiveRowPiece_has_uniform_finiteProbe
      hCmin.1 hD hupperMap m0 hm0 zf hqf_inj hupperf nf orders (packets j) mu hmu baseDensity
      (pieces j) (hpiecesCompact j) (hpiecesChart j)
    refine ⟨dd, v, U, ?_⟩
    simpa [Kj, base, direction, control, background, nodes, frozen, S, a, q] using hj
  choose dd v U hUopen hKU hbaseSm hdirSm hsurj using hprobe
  let V := concatBlock v
  let l := blockCLM V
  have hsurjAll : ∀ j, ∀ h ∈ Kj j, Function.Surjective ((direction j h).comp l) := by
    intro j h hh
    exact surjective_comp_concatBlock (direction j h) v j (hsurj j h hh)
  have hbadClosed : ∀ j, IsClosed (expandedDifferentialEvaluationRankDefect degree
      (Fintype.card (Σ i, Fin (orders i))) (packets j).1 exponent) :=
    fun j => expandedDifferentialEvaluationRankDefect_isClosed degree
      (Fintype.card (Σ i, Fin (orders i))) (packets j).1 exponent
  have hstrata : ∀ j, FiniteRegularStratification
      (expandedDifferentialEvaluationRankDefect degree
        (Fintype.card (Σ i, Fin (orders i))) (packets j).1 exponent)
      (2 * (Fintype.card row - Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :=
    fun j => expandedDifferentialEvaluationRankDefect_finiteRegularStratification_unconditional
      degree (Fintype.card (Σ i, Fin (orders i))) (packets j).1 (packets j).2 exponent
      hexponent hrows
  obtain ⟨hGopen, hGnull⟩ := blockControlled_finite_atlas base direction
    (fun j => expandedDifferentialEvaluationRankDefect degree
      (Fintype.card (Σ i, Fin (orders i))) (packets j).1 exponent)
    hbadClosed _ U Kj hUopen hKU
    (fun j => (hpiecesCompact j).image continuous_subtype_val)
    (fun j => (hbaseSm j).of_le le_top) (fun j => (hdirSm j).of_le le_top)
    l hsurjAll hstrata hdim
  refine ⟨_, l, _, hGopen, hGnull, ?_⟩
  intro w hw shift hshift
  obtain ⟨j, hjpiece⟩ := Set.mem_iUnion.mp (hcover hshift)
  refine ⟨packets j, (hpiecesChart j hjpiece).2, ?_⟩
  have hjgood := Set.mem_iInter.mp hw j
  have hambient : shift.1 ∈ Kj j := ⟨shift, hjpiece, rfl⟩
  have havoid := hjgood shift.1 hambient
  have hinjective : Function.Injective
      (expandedDifferentialEvaluationMatrix degree
        (Fintype.card (Σ i, Fin (orders i))) (packets j).1 exponent
        (smoothAffineControlFamily (base j) (direction j) (w, shift.1))).mulVec := by
    simpa only [mem_expandedDifferentialEvaluationRankDefect_iff, not_not] using havoid
  have hfamily : smoothAffineControlFamily (base j) (direction j) (w, shift.1) =
      actualNevanlinnaExpandedPacketValue
        m0 a q orders mu baseDensity S (packets j) w shift := by
    funext pt
    simp [smoothAffineControlFamily, background, base, direction, control, nodes,
      actualNevanlinnaExpandedPacketValue, ambientCombinedProjectiveNodes,
      ContinuousLinearMap.domRestrict_apply, map_add, add_assoc]
  simpa [hfamily] using hinjective

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal NNReal OnePoint

/-- **Countable-pattern actual-Nevanlinna full-rank prevalence.**  One compact product probe of
finite moment-preserving control blocks, of arbitrarily small radius, makes the full-rank phase
full after every deterministic recentring. -/
theorem countablePatterns_actualNevanlinna_fullRankWitness_blockPrevalentRadius
    (row κ ι : ℕ → Type)
    [∀ n, Fintype (row n)] [∀ n, DecidableEq (row n)]
    [∀ n, Fintype (κ n)] [∀ n, DecidableEq (κ n)]
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    {ιf : Type} [Fintype ιf] [DecidableEq ιf]
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C) (hD : Differentiable ℂ D)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {pz : ℂ} (hCp : C pz = 0) {cz : ℂ} (hCc : C cz ≠ 0)
    (hupperMap : ∀ z, z.im < 0 → 0 < (projectiveNevanlinnaQuotient C D z).im)
    (m0 : ℂ → ℂ)
    (hm0 : ∀ k, ContDiffOn ℂ ⊤ (iteratedDeriv k m0) (projectiveRegularLocus C))
    (zf : ιf → ℂ)
    (hqf_inj : Function.Injective (fun i => projectiveNevanlinnaQuotient C D (zf i)))
    (hupperf : ∀ i, 0 < (projectiveNevanlinnaQuotient C D (zf i)).im)
    (nf : ιf → ℕ)
    (degree : ℕ → ℕ) (orders : ∀ n, ι n → ℕ)
    (exponent : ∀ n, κ n → (Fin (Fintype.card (Σ i, Fin (orders n i))) →₀ ℕ))
    (hexponent : ∀ n, Function.Injective (exponent n))
    (hrows : ∀ n,
      Fintype.card (κ n × Fin (degree n + 1)) + degree n < Fintype.card (row n))
    (mu : Measure (OnePoint ℝ)) [IsProbabilityMeasure mu] (hmu : mu.support.Infinite)
    (baseDensity : Lp ℝ (⊤ : ENNReal) mu)
    (hdim : ∀ n, Module.finrank ℝ (ι n → ℂ) <
      2 * (Fintype.card (row n) -
        Fintype.card (κ n × Fin (degree n + 1)) - degree n + 1))
    {r : ℝ} (hr : 0 < r) :
    let a := projectiveNevanlinnaAmplitude C
    let q := projectiveNevanlinnaQuotient C D
    let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
      (fun i => q (zf i)) nf mu hupperf
    let S := LinearMap.ker frozen.toLinearMap
    BlockPrevalentRadius r {w : S | ∀ n (shift : InjectiveShiftConfiguration (ι n)),
      actualNevanlinnaExpandedFullRankWitness
        (row := row n) (κ := κ n) (ι := ι n)
        m0 a q (degree n) (orders n) (exponent n) mu baseDensity S w shift} := by
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
  refine globalWitness_blockPrevalentRadius_of_sigmaCompact_family
    (H := fun n => InjectiveShiftConfiguration (ι n))
    (fun n w shift => actualNevanlinnaExpandedFullRankWitness
      (row := row n) (κ := κ n) (ι := ι n)
      m0 a q (degree n) (orders n) (exponent n) mu baseDensity S w shift) ?_ hr
  intro n Kshift hKshift
  simpa [a, q, frozen, S] using
    compact_injectiveShiftPatch_blockControlled_completeAtlas_actualNevanlinna
      hCmin hD hnoCommon hCp hCc hupperMap m0 hm0 zf hqf_inj hupperf nf
      (degree n) (orders n) (exponent n) (hexponent n) (hrows n) mu hmu baseDensity
      Kshift hKshift (hdim n)

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal NNReal OnePoint

/-- Countably simultaneous full-rank witnesses promote to coefficient rigidity for every encoded
finite relation pattern, prevalently. -/
theorem countablePatterns_relationFree_blockPrevalentRadius_of_fullRankWitness
    (row κ ι : ℕ → Type)
    [∀ n, Fintype (row n)] [∀ n, Fintype (κ n)] [∀ n, DecidableEq (κ n)] [∀ n, Fintype (ι n)]
    (m0 a q : ℂ → ℂ) (degree : ℕ → ℕ) (orders : ∀ n, ι n → ℕ)
    (exponent : ∀ n, κ n → (Fin (Fintype.card (Σ i, Fin (orders n i))) →₀ ℕ))
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu]
    (baseDensity : Lp ℝ (⊤ : ENNReal) mu)
    (S : Submodule ℝ (Lp ℝ (⊤ : ENNReal) mu))
    {r : ℝ}
    (hfull : BlockPrevalentRadius r {w : S | ∀ n (shift : InjectiveShiftConfiguration (ι n)),
      actualNevanlinnaExpandedFullRankWitness
        (row := row n) (κ := κ n) (ι := ι n)
        m0 a q (degree n) (orders n) (exponent n) mu baseDensity S w shift}) :
    BlockPrevalentRadius r {w : S | ∀ n (shift : InjectiveShiftConfiguration (ι n))
      (coeff : κ n × Fin (degree n + 1) → ℂ),
      actualNevanlinnaExpandedPatternRelationHolds
        (row := row n) m0 a q (degree n) (orders n) (exponent n)
          mu baseDensity S w shift coeff →
        ∀ col, coeff col = 0} := by
  refine BlockPrevalentRadius.mono hfull ?_
  intro w hw n shift coeff hrel
  exact actualNevanlinnaExpandedPatternRelation_coefficients_eq_zero_of_fullRankWitness
    m0 a q (degree n) (orders n) (exponent n) mu baseDensity S w shift (hw n shift) coeff hrel

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal NNReal OnePoint

/-- **Actual Nevanlinna countable-pattern relation-rigidity is prevalent.**  This is the exact
moment-fibre prevalence law: one explicit compact product probe of finite moment-preserving
control blocks, of arbitrarily small radius, makes coefficient rigidity for every encoded finite
differential pattern and every tuple of distinct complex shifts hold with probability one after
every deterministic recentring. -/
theorem countablePatterns_actualNevanlinna_relationFree_blockPrevalentRadius
    (row κ ι : ℕ → Type)
    [∀ n, Fintype (row n)] [∀ n, DecidableEq (row n)]
    [∀ n, Fintype (κ n)] [∀ n, DecidableEq (κ n)]
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    {ιf : Type} [Fintype ιf] [DecidableEq ιf]
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C) (hD : Differentiable ℂ D)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {pz : ℂ} (hCp : C pz = 0) {cz : ℂ} (hCc : C cz ≠ 0)
    (hupperMap : ∀ z, z.im < 0 → 0 < (projectiveNevanlinnaQuotient C D z).im)
    (m0 : ℂ → ℂ)
    (hm0 : ∀ k, ContDiffOn ℂ ⊤ (iteratedDeriv k m0) (projectiveRegularLocus C))
    (zf : ιf → ℂ)
    (hqf_inj : Function.Injective (fun i => projectiveNevanlinnaQuotient C D (zf i)))
    (hupperf : ∀ i, 0 < (projectiveNevanlinnaQuotient C D (zf i)).im)
    (nf : ιf → ℕ)
    (degree : ℕ → ℕ) (orders : ∀ n, ι n → ℕ)
    (exponent : ∀ n, κ n → (Fin (Fintype.card (Σ i, Fin (orders n i))) →₀ ℕ))
    (hexponent : ∀ n, Function.Injective (exponent n))
    (hrows : ∀ n,
      Fintype.card (κ n × Fin (degree n + 1)) + degree n < Fintype.card (row n))
    (mu : Measure (OnePoint ℝ)) [IsProbabilityMeasure mu] (hmu : mu.support.Infinite)
    (baseDensity : Lp ℝ (⊤ : ENNReal) mu)
    (hdim : ∀ n, Module.finrank ℝ (ι n → ℂ) <
      2 * (Fintype.card (row n) -
        Fintype.card (κ n × Fin (degree n + 1)) - degree n + 1))
    {r : ℝ} (hr : 0 < r) :
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
    BlockPrevalentRadius r relationFree := by
  dsimp only
  let a := projectiveNevanlinnaAmplitude C
  let q := projectiveNevanlinnaQuotient C D
  let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
    (fun i => q (zf i)) nf mu hupperf
  let S := LinearMap.ker frozen.toLinearMap
  letI normedAddCommGroupS : NormedAddCommGroup S := Submodule.normedAddCommGroup S
  letI : NormedSpace ℝ S := Submodule.normedSpace S
  have hfull := countablePatterns_actualNevanlinna_fullRankWitness_blockPrevalentRadius
    row κ ι hCmin hD hnoCommon hCp hCc hupperMap m0 hm0 zf hqf_inj hupperf nf
    degree orders exponent hexponent hrows mu hmu baseDensity hdim hr
  exact countablePatterns_relationFree_blockPrevalentRadius_of_fullRankWitness
    row κ ι m0 a q degree orders exponent mu baseDensity S hfull

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal NNReal OnePoint

/-- **Full moment-fibre probability clouds.**  The prevalence law is uniform in the base density,
so an arbitrarily small convex insertion of the probe cloud into any fixed density carries the same
relation rigidity: the mixture `(1-ε)·d₀ + ε·(base + x)` is again a base density, and the probe is
the cloud of radius `r`, which can be taken inside any weak neighbourhood margin. -/
theorem convexInsertion_actualNevanlinna_relationFree_blockPrevalentRadius
    (row κ ι : ℕ → Type)
    [∀ n, Fintype (row n)] [∀ n, DecidableEq (row n)]
    [∀ n, Fintype (κ n)] [∀ n, DecidableEq (κ n)]
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    {ιf : Type} [Fintype ιf] [DecidableEq ιf]
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C) (hD : Differentiable ℂ D)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {pz : ℂ} (hCp : C pz = 0) {cz : ℂ} (hCc : C cz ≠ 0)
    (hupperMap : ∀ z, z.im < 0 → 0 < (projectiveNevanlinnaQuotient C D z).im)
    (m0 : ℂ → ℂ)
    (hm0 : ∀ k, ContDiffOn ℂ ⊤ (iteratedDeriv k m0) (projectiveRegularLocus C))
    (zf : ιf → ℂ)
    (hqf_inj : Function.Injective (fun i => projectiveNevanlinnaQuotient C D (zf i)))
    (hupperf : ∀ i, 0 < (projectiveNevanlinnaQuotient C D (zf i)).im)
    (nf : ιf → ℕ)
    (degree : ℕ → ℕ) (orders : ∀ n, ι n → ℕ)
    (exponent : ∀ n, κ n → (Fin (Fintype.card (Σ i, Fin (orders n i))) →₀ ℕ))
    (hexponent : ∀ n, Function.Injective (exponent n))
    (hrows : ∀ n,
      Fintype.card (κ n × Fin (degree n + 1)) + degree n < Fintype.card (row n))
    (mu : Measure (OnePoint ℝ)) [IsProbabilityMeasure mu] (hmu : mu.support.Infinite)
    (baseDensity d0 xshift : Lp ℝ (⊤ : ENNReal) mu) (ε : ℝ)
    (hdim : ∀ n, Module.finrank ℝ (ι n → ℂ) <
      2 * (Fintype.card (row n) -
        Fintype.card (κ n × Fin (degree n + 1)) - degree n + 1))
    {r : ℝ} (hr : 0 < r) :
    let a := projectiveNevanlinnaAmplitude C
    let q := projectiveNevanlinnaQuotient C D
    let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
      (fun i => q (zf i)) nf mu hupperf
    let S := LinearMap.ker frozen.toLinearMap
    let mixed : Lp ℝ (⊤ : ENNReal) mu := (1 - ε) • d0 + ε • (baseDensity + xshift)
    let relationFree : Set S := {w | ∀ n (shift : InjectiveShiftConfiguration (ι n))
      (coeff : κ n × Fin (degree n + 1) → ℂ),
      actualNevanlinnaExpandedPatternRelationHolds
        (row := row n) m0 a q (degree n) (orders n) (exponent n)
          mu mixed S w shift coeff →
        ∀ col, coeff col = 0}
    BlockPrevalentRadius r relationFree :=
  countablePatterns_actualNevanlinna_relationFree_blockPrevalentRadius
    row κ ι hCmin hD hnoCommon hCp hCc hupperMap m0 hm0 zf hqf_inj hupperf nf
    degree orders exponent hexponent hrows mu hmu
    ((1 - ε) • d0 + ε • (baseDensity + xshift)) hdim hr

/-- The moment-fibre relation-rigidity phase is block prevalent. -/
theorem countablePatterns_actualNevanlinna_relationFree_blockPrevalent
    (row κ ι : ℕ → Type)
    [∀ n, Fintype (row n)] [∀ n, DecidableEq (row n)]
    [∀ n, Fintype (κ n)] [∀ n, DecidableEq (κ n)]
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    {ιf : Type} [Fintype ιf] [DecidableEq ιf]
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C) (hD : Differentiable ℂ D)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {pz : ℂ} (hCp : C pz = 0) {cz : ℂ} (hCc : C cz ≠ 0)
    (hupperMap : ∀ z, z.im < 0 → 0 < (projectiveNevanlinnaQuotient C D z).im)
    (m0 : ℂ → ℂ)
    (hm0 : ∀ k, ContDiffOn ℂ ⊤ (iteratedDeriv k m0) (projectiveRegularLocus C))
    (zf : ιf → ℂ)
    (hqf_inj : Function.Injective (fun i => projectiveNevanlinnaQuotient C D (zf i)))
    (hupperf : ∀ i, 0 < (projectiveNevanlinnaQuotient C D (zf i)).im)
    (nf : ιf → ℕ)
    (degree : ℕ → ℕ) (orders : ∀ n, ι n → ℕ)
    (exponent : ∀ n, κ n → (Fin (Fintype.card (Σ i, Fin (orders n i))) →₀ ℕ))
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
    BlockPrevalent relationFree :=
  BlockPrevalentRadius.blockPrevalent
    (countablePatterns_actualNevanlinna_relationFree_blockPrevalentRadius
      row κ ι hCmin hD hnoCommon hCp hCc hupperMap m0 hm0 zf hqf_inj hupperf nf
      degree orders exponent hexponent hrows mu hmu baseDensity hdim one_pos)

end

end GaloisForLFunctions.HTGeometry
