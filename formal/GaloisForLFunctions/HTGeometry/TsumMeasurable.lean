import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Measurability of a pointwise sum

A pointwise convergent series of almost-everywhere strongly measurable functions is again almost
everywhere strongly measurable, because its partial sums converge to it pointwise.  Mathlib records
the integral of such a series but not its measurability, which is what a domination argument for the
sum itself needs.
-/

open MeasureTheory

noncomputable section

namespace HTGeometry

/-- **A pointwise convergent series of measurable functions is measurable.** -/
theorem aestronglyMeasurable_tsum_nat {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E : Type*} [NormedAddCommGroup E]
    {F : ℕ → α → E} (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hsum : ∀ᵐ a ∂μ, Summable fun n => F n a) :
    AEStronglyMeasurable (fun a => ∑' n, F n a) μ := by
  refine aestronglyMeasurable_of_tendsto_ae Filter.atTop
    (fun N : ℕ => Finset.aestronglyMeasurable_sum (Finset.range N) fun n _ => hF n) ?_
  filter_upwards [hsum] with a ha
  refine ha.hasSum.tendsto_sum_nat.congr fun n => ?_
  simp [Finset.sum_apply]

end HTGeometry
