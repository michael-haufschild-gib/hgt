import GaloisForLFunctions.HTGeometry.OnePointPullbackRigidity
import GaloisForLFunctions.HTGeometry.ProjectiveNevanlinnaRowEvaluationSmoothness

/-!
# Rigidity for the kernel of the Nevanlinna control map

The control map pairs against the `L¹` class of the projective Nevanlinna Banach kernel, while the
rigidity statement is about the honest jet column.  On the upper packet locus the Banach kernel is
pointwise that column, and an `L¹` class agrees almost everywhere with the continuous function
representing it, so rigidity passes to the class.

This is the hypothesis the kernel-control surjectivity criterion consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- **Rigidity for the `L¹` class carried by the Nevanlinna control map.**  At distinct noncritical
upper packet nodes, over a projective pushforward of a measure of infinite support, no nonzero
coefficient packet annihilates the real part of the control kernel almost everywhere. -/
theorem nevanlinnaControlKernel_coeff_eq_zero_of_ae_re
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {ν : Measure ℝ} [IsFiniteMeasure ν] (hsupp : ν.support.Infinite)
    (a q : ℂ → ℂ) (n : ι → ℕ) (z : ι → ℂ)
    (hz : z ∈ nevanlinnaUpperPacketSet q)
    (hx : Function.Injective fun i => q (z i))
    (ha : ∀ i, a (z i) ≠ 0) (hq : ∀ i, deriv q (z i) ≠ 0)
    (c : (Σ i, Fin (n i)) → ℂ)
    (hc : ∀ᵐ t ∂(ν.map (OnePoint.some)),
      (∑ s : Σ i, Fin (n i),
        c s * (ContinuousMap.toLp 1 (ν.map (OnePoint.some)) ℝ
          (projectiveNevanlinnaJetExpansionBanachMap a q n z)) t s).re = 0) :
    ∀ s, c s = 0 := by
  classical
  refine nevanlinnaJetColumn_coeff_eq_zero_of_ae_re_map hsupp a q n z hx hz ha hq c ?_
  have hrep0 :
      (ContinuousMap.toLp 1 (ν.map (OnePoint.some)) ℝ
        (projectiveNevanlinnaJetExpansionBanachMap a q n z) :
          OnePoint ℝ → ((Σ i, Fin (n i)) → ℂ))
        =ᵐ[ν.map (OnePoint.some)]
          (projectiveNevanlinnaJetExpansionBanachMap a q n z) :=
    ContinuousMap.coeFn_toLp _ _
  filter_upwards [hc, hrep0] with t ht hrep
  rw [← projectiveNevanlinnaJetExpansionBanachMap_apply a q n z hz t, ← hrep]
  exact ht

end

end GaloisForLFunctions.HTGeometry
