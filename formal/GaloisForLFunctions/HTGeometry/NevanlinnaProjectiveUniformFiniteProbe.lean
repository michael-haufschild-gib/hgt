import GaloisForLFunctions.HTGeometry.NevanlinnaNoncriticalProjectiveCompactPatch
import GaloisForLFunctions.HTGeometry.NevanlinnaTranslatedUniformFiniteProbe

/-!
# The uniform finite probe of a noncritical projective row piece

The same construction that makes the compact-patch avoidance dense produces an explicit finite
family of density directions whose span the smooth row control maps onto at every configuration of
the piece.  That explicit family is what a probability statement needs: it is the linear
parametrization along which a Lebesgue block law is pushed into the density space.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set Topology
open scoped ENNReal OnePoint

noncomputable section

/-- **A noncritical projective row piece has an explicit uniform finite probe.** -/
theorem compact_completeProjectiveRowPiece_has_uniform_finiteProbe
    {row ι ιf : Type}
    [Fintype row] [DecidableEq row]
    [Fintype ι] [DecidableEq ι]
    [Fintype ιf] [DecidableEq ιf]
    {C D : ℂ → ℂ} (hC : Differentiable ℂ C) (hD : Differentiable ℂ D)
    (hupperMap : ∀ z, z.im < 0 → 0 < (projectiveNevanlinnaQuotient C D z).im)
    (m0 : ℂ → ℂ)
    (hm0 : ∀ k, ContDiffOn ℂ ⊤ (iteratedDeriv k m0) (projectiveRegularLocus C))
    (zf : ιf → ℂ)
    (hqf_inj : Function.Injective (fun i => projectiveNevanlinnaQuotient C D (zf i)))
    (hupperf : ∀ i, 0 < (projectiveNevanlinnaQuotient C D (zf i)).im)
    (nf : ιf → ℕ)
    (orders : ι → ℕ)
    (packet : InjectiveProjectiveRowPacket row)
    (mu : Measure (OnePoint ℝ)) [IsProbabilityMeasure mu] (hmu : mu.support.Infinite)
    (baseDensity : Lp ℝ (⊤ : ENNReal) mu)
    (piece : Set (InjectiveShiftConfiguration ι)) (hpiece : IsCompact piece)
    (hpieceChart : piece ⊆ noncriticalProjectiveLowerGoodCombinedRowPacketSet
      (ι := ι) (κ := ιf) C D
      (fun i => projectiveNevanlinnaQuotient C D (zf i)) packet) :
    let a := projectiveNevanlinnaAmplitude C
    let q := projectiveNevanlinnaQuotient C D
    let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
      (fun i => q (zf i)) nf mu hupperf
    let S := LinearMap.ker frozen.toLinearMap
    ∃ (d : ℕ) (v : Fin d → S) (U : Set (ι → ℂ)),
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
      IsOpen U ∧ ambientImageOfInjectiveShiftPiece piece ⊆ U ∧
        ContDiffOn ℝ ⊤ base U ∧ ContDiffOn ℝ ⊤ direction U ∧
        ∀ h ∈ ambientImageOfInjectiveShiftPiece piece,
          Function.Surjective ((direction h).comp (blockCLM v)) := by
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
  have hchartOpen := noncriticalProjectiveLowerGoodCombinedRowPacketSet_isOpen
    (row := row) (ι := ι) (κ := ιf) hC hD
      (fun i => q (zf i)) packet
  rw [isOpen_induced_iff] at hchartOpen
  obtain ⟨O, hOopen, hOeq⟩ := hchartOpen
  let U0 : Set (ι → ℂ) := O ∩ injectiveShiftConfigurationSet ι
  have hU0 : IsOpen U0 := hOopen.inter (injectiveShiftConfigurationSet_isOpen ι)
  have hchartU0 : ∀ (h : ι → ℂ) (hh : h ∈ U0),
      (⟨h, hh.2⟩ : InjectiveShiftConfiguration ι) ∈
        noncriticalProjectiveLowerGoodCombinedRowPacketSet
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
    have hdata := noncriticalProjectiveLowerGoodCombinedRowPacket_complete_data
      hC hD (fun i => q (zf i)) packet (hchartU0 h hh)
    have hnodesEq :
        combinedProjectiveRowShiftPacket packet
            (⟨h, hh.2⟩ : InjectiveShiftConfiguration ι) =
          nodes h := by
      funext x
      rfl
    simpa only [hnodesEq] using hdata
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
  have hnodesContDiff : ContDiff ℝ ⊤ nodes := by
    rw [contDiff_pi]
    intro x
    simpa [nodes, ambientCombinedProjectiveNodes] using
      (contDiff_const.add (contDiff_apply ℝ ℂ x.2))
  have hnodesOmega : ∀ h ∈ U, ∀ x, nodes h x ∈ Omega := by
    intro h hh x
    exact hnodesOmegaU0 h hh.1 x
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
  let background : (ι → ℂ) →
      (row × Fin (Fintype.card (Σ i, Fin (orders i))) → ℂ) := fun h p =>
    let s := (Fintype.equivFin (Σ i, Fin (orders i))).symm p.2
    iteratedDeriv s.2 m0 (nodes h (p.1, s.1))
  have hbackground : ContDiffOn ℝ ⊤ background U := by
    apply contDiffOn_pi'
    intro p
    let s := (Fintype.equivFin (Σ i, Fin (orders i))).symm p.2
    have hnode : ContDiff ℝ ⊤ (fun h : ι → ℂ => nodes h (p.1, s.1)) := by
      simpa [nodes, ambientCombinedProjectiveNodes] using
        (contDiff_const.add (contDiff_apply ℝ ℂ s.1))
    have hjetReal : ContDiffOn ℝ ⊤ (iteratedDeriv s.2 m0) Omega :=
      contDiffOn_real_of_contDiffOn_complex_of_isOpen hOmega (hm0 s.2)
    change ContDiffOn ℝ ⊤
      (fun h : ι → ℂ =>
        iteratedDeriv s.2 m0 (nodes h (p.1, s.1))) U
    convert hjetReal.comp hnode.contDiffOn
      (fun h hh => hnodesOmega h hh (p.1, s.1)) using 1
    funext h
    rfl
  obtain ⟨d, v, hv⟩ :=
    compact_translatedNevanlinnaExpandedEvaluation_has_uniform_finiteProbe
      a q Omega hOmega ha hq η hη
      zf hqf_inj hupperf nf orders mu hmu nodes hnodesContDiff U K hK hKU
      hnodesOmega hupper hqt_inj hcross hat hqdt
  refine ⟨d, v, U, hU, hKU, ?_, ?_, hv⟩
  · -- smoothness of the base
    have hcontrol : ContDiffOn ℝ ⊤
        (fun h => projectiveNevanlinnaJetExpansionSmoothControl
          a q (fun x : row × ι => orders x.2) mu (nodes h)) U := by
      exact (contDiffOn_projectiveNevanlinnaJetExpansionSmoothControl_within
        a q hOmega ha hq (fun x : row × ι => orders x.2) mu).comp hnodesContDiff.contDiffOn
          (fun h hh => ⟨fun x => hη.trans_le (hupper h hh x),
            fun x _ => hnodesOmega h hh x⟩)
    exact hbackground.add
      ((reshapeCombinedJetsFinCLM row ι orders).contDiff.comp_contDiffOn
        (hcontrol.clm_apply contDiffOn_const))
  · -- smoothness of the direction
    have hcontrol : ContDiffOn ℝ ⊤
        (fun h => projectiveNevanlinnaJetExpansionSmoothControl
          a q (fun x : row × ι => orders x.2) mu (nodes h)) U := by
      exact (contDiffOn_projectiveNevanlinnaJetExpansionSmoothControl_within
        a q hOmega ha hq (fun x : row × ι => orders x.2) mu).comp hnodesContDiff.contDiffOn
          (fun h hh => ⟨fun x => hη.trans_le (hupper h hh x),
            fun x _ => hnodesOmega h hh x⟩)
    have hS : ContDiffOn ℝ ⊤
        (fun h => (projectiveNevanlinnaJetExpansionSmoothControl
          a q (fun x : row × ι => orders x.2) mu (nodes h)).domRestrict
            (LinearMap.ker (normalizedProjectiveCauchyJetLinftyContinuousControl
              (fun i => q (zf i)) nf mu hupperf).toLinearMap)) U := by
      have hsubS : ContDiffOn ℝ ⊤ (fun _ : ι → ℂ =>
        (LinearMap.ker (normalizedProjectiveCauchyJetLinftyContinuousControl
          (fun i => q (zf i)) nf mu hupperf).toLinearMap).subtypeL) U := contDiffOn_const
      simpa only [ContinuousLinearMap.domRestrict] using hcontrol.clm_comp hsubS
    have hreindex : ContDiffOn ℝ ⊤
        (fun _ : ι → ℂ => reshapeCombinedJetsFinCLM row ι orders) U := contDiffOn_const
    exact hreindex.clm_comp hS

end

end GaloisForLFunctions.HTGeometry
