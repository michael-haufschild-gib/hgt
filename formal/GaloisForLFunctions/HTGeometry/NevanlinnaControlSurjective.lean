import GaloisForLFunctions.HTGeometry.NevanlinnaControlKernelRigidity

/-!
# Surjectivity of the Nevanlinna jet control map

The smooth Nevanlinna row-evaluation control map pairs bounded densities against the `L¹` class of
the projective jet kernel.  That kernel is rigid at distinct noncritical upper packet nodes, and a
kernel control map with a rigid kernel is surjective.

Every finite Nevanlinna jet packet is therefore realized by a bounded density.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- **The Nevanlinna jet control map is surjective.**  At distinct noncritical upper packet nodes,
over a projective pushforward of a finite measure of infinite support, every finite jet packet is
attained by a bounded density. -/
theorem surjective_projectiveNevanlinnaJetExpansionSmoothControl
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {ν : Measure ℝ} [IsFiniteMeasure ν] (hsupp : ν.support.Infinite)
    (a q : ℂ → ℂ) (n : ι → ℕ) (z : ι → ℂ)
    (hz : z ∈ nevanlinnaUpperPacketSet q)
    (hx : Function.Injective fun i => q (z i))
    (ha : ∀ i, a (z i) ≠ 0) (hq : ∀ i, deriv q (z i) ≠ 0) :
    Function.Surjective
      (projectiveNevanlinnaJetExpansionSmoothControl a q n (ν.map (OnePoint.some)) z) := by
  classical
  haveI : IsFiniteMeasure (ν.map (OnePoint.some)) :=
    Measure.isFiniteMeasure_map ν (OnePoint.some)
  rw [projectiveNevanlinnaJetExpansionSmoothControl]
  refine surjective_linftyLpKernelControl_of_rigidity _ _ ?_
  intro c hc
  exact nevanlinnaControlKernel_coeff_eq_zero_of_ae_re hsupp a q n z hz hx ha hq c hc

end

end GaloisForLFunctions.HTGeometry
