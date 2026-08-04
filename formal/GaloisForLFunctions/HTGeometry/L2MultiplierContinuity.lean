import GaloisForLFunctions.HTGeometry.L2FourierMultiplier
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Strong continuity of a family of bounded multipliers

A family of symbols bounded by one constant and converging pointwise induces multiplication
operators converging *strongly*: applied to a fixed `L²` function they converge in `L²`. The
operators themselves do **not** converge in operator norm — that is the reason a propagator group is
strongly and not norm continuous — but strong convergence is what an evolution equation consumes.

The proof is dominated convergence for the Lebesgue integral: the `L²` distance of the two images is
the integral of `|φᵢ - ψ|²|f|²`, which is dominated by `(2C)²|f|²` and tends to zero pointwise.

Conjugating by Plancherel transports the statement to Fourier multipliers.
-/

noncomputable section

namespace MeasureTheory

open Filter

open scoped ENNReal

section Continuity

variable {α 𝕜 : Type*} [MeasurableSpace α] [RCLike 𝕜] [SecondCountableTopology 𝕜]
variable {μ : Measure α}

omit [SecondCountableTopology 𝕜] in
/-- The square of the `L²` function has finite Lebesgue integral. -/
theorem lintegral_enorm_rpow_two_ne_top (f : Lp 𝕜 2 μ) :
    ∫⁻ x, ‖(f : α → 𝕜) x‖ₑ ^ (2 : ℝ) ∂μ ≠ ∞ := by
  have hlt : eLpNorm ((f : α → 𝕜)) 2 μ < ∞ := (Lp.eLpNorm_ne_top f).lt_top
  have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (μ := μ) (f := (f : α → 𝕜))
    (p := 2) (by norm_num) (by norm_num)).mp hlt
  simpa using h.ne

/-- **A pointwise convergent family of uniformly bounded symbols multiplies convergently.** -/
theorem tendsto_lpBoundedMulCLM_apply {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {φ : ι → α → 𝕜} {ψ : α → 𝕜} (hφ : ∀ i, Measurable (φ i)) (hψ : Measurable ψ)
    {C : ℝ} (hC0 : 0 ≤ C) (hCi : ∀ i x, ‖φ i x‖ ≤ C) (hCψ : ∀ x, ‖ψ x‖ ≤ C)
    (hpt : ∀ x, Tendsto (fun i => φ i x) l (nhds (ψ x))) (f : Lp 𝕜 2 μ) :
    Tendsto (fun i => lpBoundedMulCLM (p := 2) (μ := μ) (hφ i) hC0 (hCi i) f) l
      (nhds (lpBoundedMulCLM (p := 2) (μ := μ) hψ hC0 hCψ f)) := by
  refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr ?_
  have hcongr : ∀ i : ι,
      eLpNorm ((lpBoundedMulCLM (p := 2) (μ := μ) (hφ i) hC0 (hCi i) f : α → 𝕜)
          - (lpBoundedMulCLM (p := 2) (μ := μ) hψ hC0 hCψ f : α → 𝕜)) 2 μ
        = eLpNorm (fun x => (φ i x - ψ x) * (f : α → 𝕜) x) 2 μ := by
    intro i
    refine eLpNorm_congr_ae ?_
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := μ) (hφ i) hC0 (hCi i) f,
      lpBoundedMulCLM_coeFn (p := 2) (μ := μ) hψ hC0 hCψ f] with x h1 h2
    rw [Pi.sub_apply, h1, h2, sub_mul]
  simp_rw [hcongr]
  have hform : ∀ i : ι, eLpNorm (fun x => (φ i x - ψ x) * (f : α → 𝕜) x) 2 μ
      = (∫⁻ x, ‖(φ i x - ψ x) * (f : α → 𝕜) x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    intro i
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num
  simp_rw [hform]
  have hlim : Tendsto (fun i : ι => ∫⁻ x, ‖(φ i x - ψ x) * (f : α → 𝕜) x‖ₑ ^ (2 : ℝ) ∂μ) l
      (nhds 0) := by
    have hzero : (0 : ℝ≥0∞) = ∫⁻ _x : α, (0 : ℝ≥0∞) ∂μ := by simp
    rw [hzero]
    refine tendsto_lintegral_filter_of_dominated_convergence'
      (bound := fun x => ‖(2 * C : ℝ)‖ₑ ^ (2 : ℝ) * ‖(f : α → 𝕜) x‖ₑ ^ (2 : ℝ)) ?_ ?_ ?_ ?_
    · refine Filter.Eventually.of_forall fun i => ?_
      have hmeas : AEMeasurable (fun x => (φ i x - ψ x) * (f : α → 𝕜) x) μ :=
        (((hφ i).sub hψ).aemeasurable).mul (Lp.aestronglyMeasurable f).aemeasurable
      exact (hmeas.enorm.pow_const _)
    · refine Filter.Eventually.of_forall fun i => Filter.Eventually.of_forall fun x => ?_
      have hr : ‖φ i x - ψ x‖ ≤ 2 * C := by
        have h1 := hCi i x
        have h2 := hCψ x
        have := norm_sub_le (φ i x) (ψ x)
        linarith
      have hb : ‖φ i x - ψ x‖ₑ ≤ ‖(2 * C : ℝ)‖ₑ := by
        rw [← ofReal_norm, ← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        exact hr
      calc ‖(φ i x - ψ x) * (f : α → 𝕜) x‖ₑ ^ (2 : ℝ)
          = (‖φ i x - ψ x‖ₑ * ‖(f : α → 𝕜) x‖ₑ) ^ (2 : ℝ) := by rw [enorm_mul]
        _ ≤ (‖(2 * C : ℝ)‖ₑ * ‖(f : α → 𝕜) x‖ₑ) ^ (2 : ℝ) :=
            ENNReal.rpow_le_rpow (by gcongr) (by norm_num)
        _ = ‖(2 * C : ℝ)‖ₑ ^ (2 : ℝ) * ‖(f : α → 𝕜) x‖ₑ ^ (2 : ℝ) :=
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    · rw [lintegral_const_mul' _ _ (by finiteness)]
      exact ENNReal.mul_ne_top (by finiteness) (lintegral_enorm_rpow_two_ne_top f)
    · refine Filter.Eventually.of_forall fun x => ?_
      have h1 : Tendsto (fun i => (φ i x - ψ x) * (f : α → 𝕜) x) l (nhds 0) := by
        have h := ((hpt x).sub (tendsto_const_nhds (x := ψ x))).mul_const ((f : α → 𝕜) x)
        simpa using h
      have h2 : Tendsto (fun i => ‖(φ i x - ψ x) * (f : α → 𝕜) x‖ₑ) l (nhds ‖(0 : 𝕜)‖ₑ) :=
        ((ContinuousENorm.continuous_enorm (E := 𝕜)).tendsto (0 : 𝕜)).comp h1
      rw [enorm_zero] at h2
      have h3 : Tendsto (fun i => ‖(φ i x - ψ x) * (f : α → 𝕜) x‖ₑ ^ (2 : ℝ)) l
          (nhds ((0 : ℝ≥0∞) ^ (2 : ℝ))) :=
        (ENNReal.continuous_rpow_const.tendsto (0 : ℝ≥0∞)).comp h2
      rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
  have hfinal : Tendsto
      (fun i : ι => (∫⁻ x, ‖(φ i x - ψ x) * (f : α → 𝕜) x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) l
      (nhds ((0 : ℝ≥0∞) ^ (1 / (2 : ℝ)))) :=
    (ENNReal.continuous_rpow_const.tendsto (0 : ℝ≥0∞)).comp hlim
  rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at hfinal

end Continuity

end MeasureTheory

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A pointwise convergent family of uniformly bounded symbols gives strongly convergent Fourier
multipliers.** -/
theorem tendsto_fourierMulCLM_apply {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {φ : ι → E → ℂ} {ψ : E → ℂ} (hφ : ∀ i, Measurable (φ i)) (hψ : Measurable ψ)
    {C : ℝ} (hC0 : 0 ≤ C) (hCi : ∀ i ξ, ‖φ i ξ‖ ≤ C) (hCψ : ∀ ξ, ‖ψ ξ‖ ≤ C)
    (hpt : ∀ ξ, Tendsto (fun i => φ i ξ) l (nhds (ψ ξ))) (f : Lp (α := E) ℂ 2) :
    Tendsto (fun i => fourierMulCLM (hφ i) hC0 (hCi i) f) l (nhds (fourierMulCLM hψ hC0 hCψ f)) := by
  have hbase := tendsto_lpBoundedMulCLM_apply (μ := (volume : Measure E)) hφ hψ hC0 hCi hCψ hpt
    (fourierL2 E f)
  exact ((fourierL2inv E).continuous.tendsto _).comp hbase

end GaloisForLFunctions.HTGeometry
