import GaloisForLFunctions.HTGeometry.NevanlinnaTranslatedExpandedEvaluationCompactPatch
import GaloisForLFunctions.HTGeometry.StratifiedParametricPrevalence

/-!
# The uniform finite probe of a translated Nevanlinna jet packet, as an explicit family

The compact-patch density theorem constructs a finitely generated probe submodule internally and
then discards it.  For a *measure* statement the probe itself is needed: one has to push a Lebesgue
law from a Euclidean block into the density space, and that requires an explicit finite family of
directions together with the uniform surjectivity of the control restricted to their span.  This
file records exactly that data.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set Topology
open scoped ENNReal OnePoint

noncomputable section

/-- **The translated Nevanlinna control has an explicit uniform finite probe.**  On a compact
regular configuration patch there is one finite family of mean-frozen density directions whose span
the smooth row control maps onto, at every configuration of the patch. -/
theorem compact_translatedNevanlinnaExpandedEvaluation_has_uniform_finiteProbe
    {H row ι ιf : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [Fintype row] [DecidableEq row]
    [Fintype ι] [DecidableEq ι]
    [Fintype ιf] [DecidableEq ιf]
    (a q : ℂ → ℂ) (Omega : Set ℂ) (hOmega : IsOpen Omega)
    (ha : ContDiffOn ℂ ⊤ a Omega) (hq : ContDiffOn ℂ ⊤ q Omega)
    (η : ℝ) (hη : 0 < η)
    (zf : ιf → ℂ) (hqf_inj : Function.Injective (fun i => q (zf i)))
    (hupperf : ∀ i, 0 < (q (zf i)).im)
    (nf : ιf → ℕ)
    (orders : ι → ℕ)
    (mu : Measure (OnePoint ℝ)) [IsProbabilityMeasure mu] (hmu : mu.support.Infinite)
    (nodes : H → (row × ι → ℂ)) (hnodes : ContDiff ℝ ⊤ nodes)
    (U K : Set H) (hK : IsCompact K) (hKU : K ⊆ U)
    (hnodesOmega : ∀ h ∈ U, ∀ x, nodes h x ∈ Omega)
    (hupper : ∀ h ∈ U, ∀ x, η ≤ (q (nodes h x)).im)
    (hqt_inj : ∀ h ∈ K, Function.Injective (fun x => q (nodes h x)))
    (hcross : ∀ h ∈ K, ∀ i x, q (zf i) ≠ q (nodes h x))
    (hat : ∀ h ∈ K, ∀ x, a (nodes h x) ≠ 0)
    (hqdt : ∀ h ∈ K, ∀ x, deriv q (nodes h x) ≠ 0) :
    let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
      (fun i => q (zf i)) nf mu hupperf
    let S := LinearMap.ker frozen.toLinearMap
    ∃ (d : ℕ) (v : Fin d → S),
      let control := fun h =>
        projectiveNevanlinnaJetExpansionSmoothControl
          a q (fun x : row × ι => orders x.2) mu (nodes h)
      let direction := fun h =>
        (reshapeCombinedJetsFinCLM row ι orders).comp ((control h).domRestrict S)
      ∀ h ∈ K, Function.Surjective ((direction h).comp (blockCLM v)) := by
  dsimp only
  let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
    (fun i => q (zf i)) nf mu hupperf
  let S := LinearMap.ker frozen.toLinearMap
  letI normedAddCommGroupS : NormedAddCommGroup S := Submodule.normedAddCommGroup S
  letI : NormedSpace ℝ S := Submodule.normedSpace S
  let nodeLift : K → (row × ι → NevanlinnaUpperNodeAtLeast q η) :=
    fun h x => ⟨nodes h.1 x, hupper h.1 (hKU h.2) x⟩
  have hnodeLift : Continuous nodeLift := by
    apply continuous_pi
    intro x
    exact ((continuous_apply x).comp
      (hnodes.continuous.comp continuous_subtype_val)).subtype_mk _
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let Knode : Set (row × ι → NevanlinnaUpperNodeAtLeast q η) := Set.range nodeLift
  have hKnode : IsCompact Knode := isCompact_range hnodeLift
  let target := fun z : row × ι → NevanlinnaUpperNodeAtLeast q η =>
    projectiveNevanlinnaJetExpansionSmoothControl
      a q (fun x : row × ι => orders x.2) mu (fun x => (z x).1)
  let L := fun z : row × ι → NevanlinnaUpperNodeAtLeast q η =>
    (target z).domRestrict S
  have htargetOn : ContinuousOn target Knode := by
    have hval : Continuous
        (fun z : row × ι → NevanlinnaUpperNodeAtLeast q η =>
          fun x => (z x).1) := by
      apply continuous_pi
      intro x
      exact continuous_subtype_val.comp (continuous_apply x)
    apply (contDiffOn_projectiveNevanlinnaJetExpansionSmoothControl_within
      a q hOmega ha hq (fun x : row × ι => orders x.2) mu).continuousOn.comp
        hval.continuousOn
    intro z hz
    constructor
    · intro x
      exact hη.trans_le (z x).2
    · intro x hx
      obtain ⟨h, rfl⟩ := hz
      exact hnodesOmega h.1 (hKU h.2) x
  have hLOn : ContinuousOn L Knode := by
    have hsubS : ContinuousOn
        (fun _ : row × ι → NevanlinnaUpperNodeAtLeast q η => S.subtypeL) Knode :=
      continuousOn_const
    simpa only [L, ContinuousLinearMap.domRestrict] using
      htargetOn.clm_comp hsubS
  have hLsurj : ∀ z ∈ Knode, Function.Surjective (L z) := by
    intro z hz
    have hqt_z : Function.Injective (fun x => q (z x).1) := by
      obtain ⟨h, rfl⟩ := hz
      exact hqt_inj h.1 h.2
    have hcross_z : ∀ i x, q (zf i) ≠ q (z x).1 := by
      obtain ⟨h, rfl⟩ := hz
      exact hcross h.1 h.2
    have hat_z : ∀ x, a (z x).1 ≠ 0 := by
      obtain ⟨h, rfl⟩ := hz
      exact hat h.1 h.2
    have hqdt_z : ∀ x, deriv q (z x).1 ≠ 0 := by
      obtain ⟨h, rfl⟩ := hz
      exact hqdt h.1 h.2
    have heq := projectiveNevanlinnaJetExpansionSmoothControl_eq_existing
      a q (fun x : row × ι => orders x.2) mu η hη z
    have heqExisting := projectiveNevanlinnaJetExpansionLinftyControl_eq_existing
      a q η hη (fun x : row × ι => orders x.2) mu z hat_z hqdt_z
    have hexisting : Function.Surjective
        ((projectiveNevanlinnaJetLinftyContinuousControl
          a q (fun x => (z x).1) (fun x : row × ι => orders x.2)
          hat_z hqdt_z mu (fun x => hη.trans_le (z x).2)).domRestrict S) := by
      simpa [frozen, S,
        projectiveNevanlinnaJetLinftyContinuousControl_toLinearMap] using!
        (constrainedNormalizedProjectiveCauchyFrozenNevanlinnaTarget_linftyControl_surjective
          a q (fun i => q (zf i)) hqf_inj (fun x => (z x).1) hqt_z hcross_z
          hupperf (fun x => hη.trans_le (z x).2)
          nf (fun x : row × ι => orders x.2) hat_z hqdt_z mu hmu)
    simpa [L, target, heq, heqExisting] using hexisting
  obtain ⟨V, hVfg, hVsurj⟩ :=
    compact_surjectiveControls_have_uniform_finiteProbe_of_continuousOn
      L Knode hKnode hLOn hLsurj
  obtain ⟨d, v, hv⟩ := exists_blockCLM_of_fg hVfg
  refine ⟨d, v, ?_⟩
  intro h hh
  let control := fun h =>
    projectiveNevanlinnaJetExpansionSmoothControl
      a q (fun x : row × ι => orders x.2) mu (nodes h)
  let direction := fun h =>
    (reshapeCombinedJetsFinCLM row ι orders).comp ((control h).domRestrict S)
  have hdirSurj : Function.Surjective ((direction h).domRestrict V) := by
    intro y
    obtain ⟨ys, hys⟩ := reshapeCombinedJetsFinCLM_surjective row ι orders y
    have hzmem : nodeLift (⟨h, hh⟩ : K) ∈ Knode :=
      Set.mem_range_self (⟨h, hh⟩ : K)
    obtain ⟨w, hw⟩ := hVsurj (nodeLift (⟨h, hh⟩ : K)) hzmem ys
    refine ⟨w, ?_⟩
    change reshapeCombinedJetsFinCLM row ι orders (control h (w.1.1)) = y
    have heq := projectiveNevanlinnaJetExpansionSmoothControl_eq_existing
      a q (fun x : row × ι => orders x.2) mu η hη
        (nodeLift (⟨h, hh⟩ : K))
    have heq' : control h =
        linftyBochnerControl mu
          (projectiveNevanlinnaJetExpansionColumn
            a q (nodes h) (fun x : row × ι => orders x.2))
          (memLp_projectiveNevanlinnaJetExpansionColumn η hη
            (fun x : row × ι => orders x.2) mu (nodeLift (⟨h, hh⟩ : K))) := by
      simpa only [control, nodeLift] using heq
    have hw' :
        (linftyBochnerControl mu
          (projectiveNevanlinnaJetExpansionColumn
            a q (nodes h) (fun x : row × ι => orders x.2))
          (memLp_projectiveNevanlinnaJetExpansionColumn η hη
            (fun x : row × ι => orders x.2) mu
            (nodeLift (⟨h, hh⟩ : K)))) w.1.1 = ys := by
      simpa only [L, target, nodeLift, heq,
        ContinuousLinearMap.domRestrict, ContinuousLinearMap.comp_apply,
        Submodule.subtypeL_apply] using hw
    rw [heq', hw', hys]
  exact surjective_comp_blockCLM_of_domRestrict (direction h) v hv hdirSurj

end

end GaloisForLFunctions.HTGeometry
