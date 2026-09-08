import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! Uniform convergence with a fixed finite-measure support gives convergence in the actual L² norm. -/
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {α E ι : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  {μ : Measure α} {l : Filter ι}

/-- No countable index or dominated-convergence certificate is needed for a uniformly supported net. -/
theorem toLp_tendsto_of_uniform_finite_support {F : ι → α → E} {f : α → E}
    (hF : ∀ i, MemLp (F i) 2 μ) (hf : MemLp f 2 μ)
    {K : Set α} (hK : MeasurableSet K) (hμK : μ K ≠ ∞)
    (hFs : ∀ i x, x ∉ K → F i x = 0) (hfs : ∀ x, x ∉ K → f x = 0)
    (hu : TendstoUniformly F f l) :
    Tendsto (fun i => (hF i).toLp (F i)) l (𝓝 (hf.toLp f)) := by
  let H : Lp ℝ 2 μ := indicatorConstLp 2 hK hμK 1
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε/(‖H‖+1)
  have hden : 0 < ‖H‖+1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  filter_upwards [Metric.tendstoUniformly_iff.mp hu δ hδ] with i hi
  rw [dist_eq_norm]
  have hb : ‖(hF i).toLp (F i)-hf.toLp f‖ ≤ δ*‖H‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(hF i).coeFn_toLp,hf.coeFn_toLp,
      Lp.coeFn_sub ((hF i).toLp (F i)) (hf.toLp f),
      (indicatorConstLp_coeFn (p := 2) (hs := hK) (hμs := hμK) (c := (1:ℝ)))]
      with x hx hx' hsub hH
    change H x = K.indicator (fun _ => (1:ℝ)) x at hH
    rw [hsub,Pi.sub_apply,hx,hx',hH]
    by_cases h : x ∈ K
    · simp only [indicator_of_mem h,norm_one,mul_one]
      simpa only [dist_eq_norm,norm_sub_rev] using (hi x).le
    · simp only [indicator_of_notMem h,hFs i x h,hfs x h,sub_self,norm_zero,mul_zero,le_refl]
  apply hb.trans_lt
  calc
    δ*‖H‖ < δ*(‖H‖+1) := mul_lt_mul_of_pos_left (lt_add_one _) hδ
    _ = ε := div_mul_cancel₀ ε (ne_of_gt hden)

end
end GaloisForLFunctions.HTGeometry
