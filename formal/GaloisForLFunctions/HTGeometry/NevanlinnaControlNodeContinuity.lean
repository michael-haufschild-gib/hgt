import GaloisForLFunctions.HTGeometry.NevanlinnaPacketFullRankGenericity

/-!
# Continuity of the Nevanlinna control map in its nodes

A compact-patch reduction of the shift quantifier needs the jets to move continuously with the node
configuration, not only with the density.  That is a different continuity from the one used for the
residual half, where the density varies and the nodes are fixed.

It is available: the control map is smooth in operator norm on the upper packet locus, so it is
continuous there, and evaluating at a fixed density is a continuous linear operation.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- The Nevanlinna control map is continuous in its node configuration on the upper packet locus. -/
theorem continuousOn_projectiveNevanlinnaJetExpansionSmoothControl
    {ι : Type} [Fintype ι] (a q : ℂ → ℂ) (ha : ContDiff ℂ ⊤ a) (hq : ContDiff ℂ ⊤ q)
    (n : ι → ℕ) (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu] :
    ContinuousOn (projectiveNevanlinnaJetExpansionSmoothControl a q n mu)
      (nevanlinnaUpperPacketSet q) :=
  (contDiffOn_projectiveNevanlinnaJetExpansionSmoothControl a q ha hq n mu).continuousOn

/-- **The Nevanlinna jets move continuously with the nodes.**  At a fixed bounded density, the jet
packet depends continuously on the node configuration throughout the upper packet locus. -/
theorem continuousOn_nevanlinnaJets_nodes
    {ι : Type} [Fintype ι] (a q : ℂ → ℂ) (ha : ContDiff ℂ ⊤ a) (hq : ContDiff ℂ ⊤ q)
    (n : ι → ℕ) (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu] (u : Lp ℝ ⊤ mu) :
    ContinuousOn (fun z => projectiveNevanlinnaJetExpansionSmoothControl a q n mu z u)
      (nevanlinnaUpperPacketSet q) :=
  ((ContinuousLinearMap.apply ℝ ((Σ i, Fin (n i)) → ℂ) u).continuous).comp_continuousOn
    (continuousOn_projectiveNevanlinnaJetExpansionSmoothControl a q ha hq n mu)

end

end GaloisForLFunctions.HTGeometry
