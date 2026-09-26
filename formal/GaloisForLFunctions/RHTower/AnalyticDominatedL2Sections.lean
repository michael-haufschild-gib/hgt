import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy
import GaloisForLFunctions.RHTower.AnalyticHermitianClosedSpanRealization
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Locally dominated analytic L2 sections

Local L2 bounds imply weak holomorphy through the Cauchy dominated integral theorem.
For an analytic Hermitian realization, nonnegativity on any accumulating sample
set is equivalent to nonnegativity on the entire closed section span.
-/

open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace
noncomputable section
namespace RHTower.DominatedL2Sections
open GaloisForLFunctions.HTGeometry

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- Local L2 bounds for a pointwise holomorphic section family. -/
structure Family where
  domain : Set ℂ
  isOpen_domain : IsOpen domain
  value : ℂ → α → ℂ
  measurable : ∀ z ∈ domain, AEStronglyMeasurable (value z) μ
  holomorphic : ∀ a, DifferentiableOn ℂ (fun z => value z a) domain
  local_bound : ∀ z ∈ domain, ∃ R : ℝ, 0<R ∧ ball z R ⊆ domain ∧
    ∃ B : α → ℝ, MemLp B 2 μ ∧ ∀ a w, w ∈ ball z R → ‖value w a‖ ≤ B a

variable {μ}

theorem Family.memLp (F : Family μ) {z : ℂ} (hz : z ∈ F.domain) :
    MemLp (F.value z) 2 μ := by
  obtain ⟨R, hR, _, B, hB, hbound⟩ := F.local_bound z hz
  exact hB.mono' (F.measurable z hz)
    (Eventually.of_forall fun a => hbound a z (mem_ball_self hR))

def Family.section (F : Family μ) (z : ℂ) : Lp ℂ 2 μ := by
  classical
  exact if hz : z ∈ F.domain then (F.memLp hz).toLp (F.value z) else 0

theorem Family.section_coe (F : Family μ) {z : ℂ} (hz : z ∈ F.domain) :
    (F.section z : α → ℂ) =ᵐ[μ] F.value z := by
  simpa only [Family.section, dif_pos hz] using (F.memLp hz).coeFn_toLp

theorem Family.inner_section (F : Family μ) (v : Lp ℂ 2 μ)
    {z : ℂ} (hz : z ∈ F.domain) :
    inner ℂ v (F.section z) = ∫ a, star (v a)*F.value z a ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [F.section_coe hz] with a ha
  rw [ha]
  rw [RCLike.inner_apply]
  change F.value z a*star (v a) = star (v a)*F.value z a
  ring

/-- Every Hilbert pairing of the actual L2 sections is holomorphic; only local
bounds of the family are needed, not separate derivative estimates. -/
theorem Family.analytic_inner (F : Family μ) (v : Lp ℂ 2 μ) :
    AnalyticOnNhd ℂ (fun z => inner ℂ v (F.section z)) F.domain := by
  apply DifferentiableOn.analyticOnNhd _ F.isOpen_domain
  intro z hz
  obtain ⟨R, hR, hsub, B, hB, hbound⟩ := F.local_bound z hz
  have hd : DifferentiableAt ℂ (fun w => ∫ a, star (v a)*F.value w a ∂μ) z := by
    apply differentiableAt_integral_of_cauchy_dominated (R := R)
      (bound := fun a => ‖v a‖*B a) hR
    · intro w hw
      exact (Lp.aestronglyMeasurable v).star.mul (F.measurable w (hsub hw))
    · intro a
      exact ((F.holomorphic a).mono hsub).const_mul (star (v a))
    · intro a w hw
      rw [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left (hbound a w hw) (norm_nonneg _)
    · exact (Lp.memLp v).norm.integrable_mul hB
  apply (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [ball_mem_nhds z hR] with w hw
  exact F.inner_section v (hsub hw)

theorem Family.inner_sections (F : Family μ) {z w : ℂ}
    (hz : z ∈ F.domain) (hw : w ∈ F.domain) :
    inner ℂ (F.section w) (F.section z) = ∫ a, star (F.value w a)*F.value z a ∂μ := by
  rw [F.inner_section _ hz]
  apply integral_congr_ae
  filter_upwards [F.section_coe hw] with a ha
  rw [ha]

end RHTower.DominatedL2Sections

noncomputable section
namespace RHTower
open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace

namespace AnalyticHermitianKernelRealization
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : AnalyticHermitianKernelRealization H)

/-- Positivity on an accumulating sampling set tests the whole analytic realization. -/
theorem nonneg_on_accumulationSet_iff
    (D : R.toAnalyticTotalSectionFamily.AccumulationSet) :
    (∀ d : D.nodes →₀ ℂ, 0 ≤ R.finiteKernelGramQuadratic D.nodes d) ↔
      ∀ v : H, 0 ≤ (inner ℂ v (R.form v)).re := by
  constructor
  · intro h v
    let A := Submodule.span ℂ (R.kernelSection '' D.nodes)
    have hc : IsClosed {v : H | 0 ≤ (inner ℂ v (R.form v)).re} := by
      apply isClosed_le continuous_const
      exact Complex.continuous_re.comp (continuous_id.inner R.form.continuous)
    have ha : (A : Set H) ⊆ {v : H | 0 ≤ (inner ℂ v (R.form v)).re} := by
      intro w hw
      obtain ⟨d, rfl⟩ := R.exists_finiteKernelCombination_eq_of_mem_span D.nodes hw
      change 0 ≤ (inner ℂ (R.finiteKernelCombination D.nodes d)
        (R.form (R.finiteKernelCombination D.nodes d))).re
      rw [← R.finiteKernelGramQuadratic_eq]
      exact h d
    have hcl := hc.closure_subset_iff.mpr ha
    apply hcl
    change v ∈ A.topologicalClosure
    rw [show A.topologicalClosure = ⊤ from
      R.toAnalyticTotalSectionFamily.accumulationSet_total D]
    trivial
  · intro h d
    rw [R.finiteKernelGramQuadratic_eq]
    exact h _

theorem exists_negative_packet_on_accumulationSet
    (D : R.toAnalyticTotalSectionFamily.AccumulationSet)
    {v : H} (hv : (inner ℂ v (R.form v)).re < 0) :
    ∃ d : D.nodes →₀ ℂ, R.finiteKernelGramQuadratic D.nodes d < 0 := by
  by_contra hn
  push Not at hn
  exact (not_le_of_gt hv) ((R.nonneg_on_accumulationSet_iff D).1 hn v)
end AnalyticHermitianKernelRealization


end RHTower
