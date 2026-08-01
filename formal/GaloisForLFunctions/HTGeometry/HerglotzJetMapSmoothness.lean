import GaloisForLFunctions.HTGeometry.HerglotzGenericity
import GaloisForLFunctions.HTGeometry.WeightedCauchyJetControlSmoothness

/-!
# Smooth node dependence of arbitrary-measure Herglotz jets

The usual constant-one element of `L∞` in Mathlib is packaged under a finite-measure instance.
At exponent infinity no such hypothesis is mathematically needed.  We therefore construct the
constant-one class directly from its uniform bound, identify weighted control at that class with
the Herglotz jet map, and inherit smooth node dependence from the operator-norm smooth weighted
Cauchy control.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Constant one in `L∞(μ)`, available for an arbitrary measure. -/
def arbitraryLinftyOne {α : Type*} [MeasurableSpace α] (μ : Measure α) : Lp ℝ ⊤ μ :=
  (memLp_top_const (μ := μ) (1 : ℝ)).toLp (fun _ => 1)

/-- The chosen representative of `arbitraryLinftyOne` equals one almost everywhere. -/
theorem arbitraryLinftyOne_coeFn {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    arbitraryLinftyOne μ =ᵐ[μ] fun _ => (1 : ℝ) :=
  MemLp.coeFn_toLp _

/-- Weighted Cauchy control at constant one is the Herglotz jet of the same density. -/
theorem weightedJetControl_arbitraryLinftyOne_eq_herglotzJetMap
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ)
    (z : ι → ℂ) (hz : ∀ i, (z i).im ≠ 0) (n : ι → ℕ) :
    weightedJetControl μ w hw z hz n (arbitraryLinftyOne μ) =
      fun s => ∫ t, ((w t : ℝ) : ℂ) * cauchyJetKernel z n t s ∂μ := by
  funext s
  rw [weightedJetControl_apply]
  apply integral_congr_ae
  filter_upwards [arbitraryLinftyOne_coeFn μ] with t ht
  rw [ht]
  push_cast
  ring

/-- The smooth weighted control at constant one is exactly the nonlinear Herglotz chart at its
base parameter. -/
theorem weightedCauchyJetSmoothControl_arbitraryLinftyOne_eq_herglotzJetMap
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ)
    (z : ι → ℂ) (hz : ∀ i, 0 < (z i).im) (n : ι → ℕ)
    (u : Lp ℝ ⊤ μ) :
    weightedCauchyJetSmoothControl μ (fun t => Real.exp (u t) * w t)
        (integrable_exp_Lp_top_mul μ u w hw) n z (arbitraryLinftyOne μ) =
      herglotzJetMap μ w z n u := by
  rw [weightedCauchyJetSmoothControl_eq_weightedJetControl μ _ _ n z hz]
  exact weightedJetControl_arbitraryLinftyOne_eq_herglotzJetMap
    μ _ (integrable_exp_Lp_top_mul μ u w hw) z (fun i => ne_of_gt (hz i)) n

/-- For each bounded parameter, its Herglotz jet packet varies smoothly with strict upper nodes.
No finiteness assumption on the base measure is used. -/
theorem contDiffOn_herglotzJetMap_nodes
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ)
    (n : ι → ℕ) (u : Lp ℝ ⊤ μ) :
    ContDiffOn ℝ ⊤ (fun z : ι → ℂ => herglotzJetMap μ w z n u)
      (nevanlinnaUpperPacketSet (fun z : ℂ => z)) := by
  have hone : ContDiffOn ℝ ⊤
      (fun _ : ι → ℂ => arbitraryLinftyOne μ)
      (nevanlinnaUpperPacketSet (fun z : ℂ => z)) := contDiffOn_const
  have hsmooth : ContDiffOn ℝ ⊤
      (fun z : ι → ℂ =>
        weightedCauchyJetSmoothControl μ (fun t => Real.exp (u t) * w t)
          (integrable_exp_Lp_top_mul μ u w hw) n z (arbitraryLinftyOne μ))
      (nevanlinnaUpperPacketSet (fun z : ℂ => z)) :=
    (contDiffOn_weightedCauchyJetSmoothControl μ
      (fun t => Real.exp (u t) * w t)
      (integrable_exp_Lp_top_mul μ u w hw) n).clm_apply hone
  apply hsmooth.congr
  intro z hz
  exact (weightedCauchyJetSmoothControl_arbitraryLinftyOne_eq_herglotzJetMap
    μ w hw z (fun i => by simpa [nevanlinnaUpperPacketSet] using hz i) n u).symm

end

end GaloisForLFunctions.HTGeometry
