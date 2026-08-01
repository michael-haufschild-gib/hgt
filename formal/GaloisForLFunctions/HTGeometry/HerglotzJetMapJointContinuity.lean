import GaloisForLFunctions.HTGeometry.HerglotzTranslatedExpandedEvaluationCompactPatch
import GaloisForLFunctions.HTGeometry.NodeJetUniformLipschitz
import GaloisForLFunctions.HTGeometry.UpperHalfPlaneExhaustion

/-!
# Joint continuity of arbitrary-measure Herglotz jets

Compact-patch openness needs continuity in the bounded exponential parameter and moving upper node
simultaneously.  Uniform parameter Lipschitz bounds on the compact upper-half-plane exhaustion,
combined with node continuity, give this coordinatewise; finite product continuity then gives the
whole jet packet and its translated-row reshaping.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- A node jet is jointly continuous at every bounded parameter and strict upper node. -/
theorem continuousAt_nodeJet_upper
    (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ)
    (hwnn : ∀ t, 0 ≤ w t) (k : ℕ)
    (u : Lp ℝ ⊤ μ) {z : ℂ} (hz : 0 < z.im) :
    ContinuousAt (fun p : Lp ℝ ⊤ μ × ℂ => nodeJet μ w k p.1 p.2) (u, z) := by
  have hzUnion : z ∈ ⋃ m, upperPatch m := by
    rw [iUnion_upperPatch]
    exact hz
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hzUnion
  exact continuousAt_nodeJet_uncurry μ w hw hwnn
    hw.aestronglyMeasurable.aemeasurable k
    (isCompact_upperPatch (m + 1)) (upperPatch_im_ne_zero (m + 1)) u
    (upperPatch_subset_interior_succ m hm)

/-- Herglotz jet packets are jointly continuous in the bounded parameter and every strict upper
node coordinate. -/
theorem continuousOn_herglotzJetMap_pair
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ)
    (hwnn : ∀ t, 0 ≤ w t) (n : ι → ℕ) :
    ContinuousOn
      (fun p : Lp ℝ ⊤ μ × (ι → ℂ) => herglotzJetMap μ w p.2 n p.1)
      (Set.univ ×ˢ nevanlinnaUpperPacketSet (fun z : ℂ => z)) := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  rw [continuousAt_pi]
  intro s
  have hz : 0 < (p.2 s.1).im := by
    simpa [nevanlinnaUpperPacketSet] using hp.2 s.1
  have hnode := continuousAt_nodeJet_upper μ w hw hwnn s.2.1 p.1 hz
  have hargs : ContinuousAt
      (fun q : Lp ℝ ⊤ μ × (ι → ℂ) => (q.1, q.2 s.1)) p :=
    continuousAt_fst.prodMk ((continuous_apply s.1).continuousAt.comp continuousAt_snd)
  have hcomp : ContinuousAt
      (fun q : Lp ℝ ⊤ μ × (ι → ℂ) => nodeJet μ w s.2.1 q.1 (q.2 s.1)) p :=
    hnode.comp (f := fun q : Lp ℝ ⊤ μ × (ι → ℂ) => (q.1, q.2 s.1)) hargs
  simpa only [Function.comp_apply, herglotzJetMap, nodeJet, cauchyJetKernel] using
    hcomp

/-- Finite translated-row reassociation preserves joint Herglotz packet continuity. -/
theorem continuousOn_reshapedHerglotzJetMap_pair
    {row ι : Type} [Fintype row] [DecidableEq row] [Fintype ι] [DecidableEq ι]
    (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ)
    (hwnn : ∀ t, 0 ≤ w t) (orders : ι → ℕ) :
    ContinuousOn
      (fun p : Lp ℝ ⊤ μ × (row × ι → ℂ) =>
        reshapeCombinedJetsFinCLM row ι orders
          (herglotzJetMap μ w p.2 (fun x : row × ι => orders x.2) p.1))
      (Set.univ ×ˢ nevanlinnaUpperPacketSet (fun z : ℂ => z)) := by
  exact (reshapeCombinedJetsFinCLM row ι orders).continuous.comp_continuousOn
    (continuousOn_herglotzJetMap_pair μ w hw hwnn
      (fun x : row × ι => orders x.2))

end

end GaloisForLFunctions.HTGeometry
