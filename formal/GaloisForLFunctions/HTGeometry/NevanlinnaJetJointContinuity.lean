import GaloisForLFunctions.HTGeometry.NevanlinnaControlNodeContinuity
import GaloisForLFunctions.HTGeometry.ShiftQuantifierClosure

/-!
# Joint continuity of the Nevanlinna jets in nodes and density

The shift-quantifier reduction needs the jets to be continuous in the node configuration and the
density *together*, which does not follow from continuity in each separately.

It does follow here, because the jets are the evaluation of a node-dependent operator at the
density, evaluation of a continuous linear map at a vector is a bounded bilinear operation, and the
operator depends continuously on the nodes in operator norm.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- Evaluation of a continuous linear map at a vector is jointly continuous. -/
theorem continuous_clm_apply_pair
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Continuous (fun p : (E →L[ℝ] F) × E => p.1 p.2) :=
  isBoundedBilinearMap_apply.continuous

/-- **The Nevanlinna jets are jointly continuous in nodes and density.**  On the upper packet locus,
the jet packet depends continuously on the node configuration and the bounded density together. -/
theorem continuousOn_nevanlinnaJets_pair
    {ι : Type} [Fintype ι] (a q : ℂ → ℂ) (ha : ContDiff ℂ ⊤ a) (hq : ContDiff ℂ ⊤ q)
    (n : ι → ℕ) (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu] :
    ContinuousOn
      (fun p : (ι → ℂ) × Lp ℝ ⊤ mu =>
        projectiveNevanlinnaJetExpansionSmoothControl a q n mu p.1 p.2)
      (nevanlinnaUpperPacketSet q ×ˢ (Set.univ : Set (Lp ℝ ⊤ mu))) := by
  have hctrl : ContinuousOn
      (fun p : (ι → ℂ) × Lp ℝ ⊤ mu =>
        projectiveNevanlinnaJetExpansionSmoothControl a q n mu p.1)
      (nevanlinnaUpperPacketSet q ×ˢ (Set.univ : Set (Lp ℝ ⊤ mu))) :=
    (continuousOn_projectiveNevanlinnaJetExpansionSmoothControl a q ha hq n mu).comp
      continuous_fst.continuousOn (fun p hp => hp.1)
  have hpair : ContinuousOn
      (fun p : (ι → ℂ) × Lp ℝ ⊤ mu =>
        (projectiveNevanlinnaJetExpansionSmoothControl a q n mu p.1, p.2))
      (nevanlinnaUpperPacketSet q ×ˢ (Set.univ : Set (Lp ℝ ⊤ mu))) :=
    hctrl.prodMk continuous_snd.continuousOn
  exact continuous_clm_apply_pair.comp_continuousOn hpair

end

end GaloisForLFunctions.HTGeometry
