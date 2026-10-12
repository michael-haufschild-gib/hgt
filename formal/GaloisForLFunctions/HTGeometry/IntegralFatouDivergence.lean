import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Order.LiminfLimsup

/-! Nonnegative integrable approximants of a measurable nonintegrable limit
have integrals tending to positive infinity. -/

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

theorem tendsto_integral_atTop_of_ae_nonnegative_nonintegrable_limit
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : ℕ → α → ℝ} {g : α → ℝ}
    (hfi : ∀ n, Integrable (f n) μ) (hfnn : ∀ n, 0 ≤ᵐ[μ] f n)
    (hgm : AEStronglyMeasurable g μ) (hgnn : 0 ≤ᵐ[μ] g) (hg : ¬ Integrable g μ)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop atTop := by
  have hgTop : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) = ⊤ := by
    by_contra h
    exact hg ⟨hgm, (hasFiniteIntegral_iff_ofReal hgnn).mpr (lt_top_iff_ne_top.mpr h)⟩
  have hlim : (fun x => liminf (fun n => ENNReal.ofReal (f n x)) atTop) =ᵐ[μ]
      (fun x => ENNReal.ofReal (g x)) :=
    hae.mono fun x hx => ((ENNReal.continuous_ofReal.tendsto (g x)).comp hx).liminf_eq
  have hFatou := lintegral_liminf_le' (μ := μ) (u := atTop)
    (f := fun n x => ENNReal.ofReal (f n x)) (fun n =>
      ENNReal.continuous_ofReal.measurable.comp_aemeasurable
        (hfi n).aestronglyMeasurable.aemeasurable)
  rw [lintegral_congr_ae hlim, hgTop] at hFatou
  have htop : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (f n x) ∂μ) atTop (𝓝 ⊤) :=
    tendsto_of_le_liminf_of_limsup_le hFatou le_top
  apply ENNReal.tendsto_ofReal_nhds_top.mp
  exact htop.congr fun n => (ofReal_integral_eq_lintegral_ofReal (hfi n) (hfnn n)).symm

end GaloisForLFunctions.HTGeometry
