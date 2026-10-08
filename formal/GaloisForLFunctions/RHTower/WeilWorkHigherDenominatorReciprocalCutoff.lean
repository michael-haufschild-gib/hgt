import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorCutoffHead

/-!
# Reciprocal cutoffs and slowly dilated jets

Inversion exchanges a lower cutoff with the complement of a smooth tail
cutoff. Every logarithmic jet of its slow dilation tends to zero against
an absolutely integrable weight. These facts use explicit endpoint buffers.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped ContDiff
namespace RHTower.WeilHigherDenominator

def mellinReciprocalCutoff (ψ : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0 < x then 1 - ψ x⁻¹ else 0

private lemma reciprocalCutoff_zero_near_origin {ψ : ℝ → ℂ}
    (hψ : IsMellinTailCutoff ψ) :
    ∃ a : ℝ, 0 < a ∧ ∀ x < a, mellinReciprocalCutoff ψ x = 0 := by
  obtain ⟨b, hb⟩ := hψ.one_near_infinity
  let B := max b 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B⁻¹, inv_pos.mpr hB, fun x hx => ?_⟩
  by_cases hx0 : 0 < x
  · have hi : B < x⁻¹ := by
      simpa only [inv_inv] using (inv_lt_inv₀ (inv_pos.mpr hB) hx0).mpr hx
    have hbx : b < x⁻¹ := (by dsimp [B]; linarith [le_max_left b 0] : b < B).trans hi
    simp [mellinReciprocalCutoff, hx0, hb x⁻¹ hbx]
  · simp [mellinReciprocalCutoff, hx0]

theorem IsMellinTailCutoff.reciprocal {ψ : ℝ → ℂ} (hψ : IsMellinTailCutoff ψ) :
    IsMellinTailCutoff (mellinReciprocalCutoff ψ) := by
  obtain ⟨a, ha, h0⟩ := reciprocalCutoff_zero_near_origin hψ
  refine ⟨?_, ⟨a, ha, h0⟩, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x < a
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact h0 y hy
    · have hx0 : 0 < x := ha.trans_le (le_of_not_gt hx)
      apply ((contDiffAt_const (c := (1 : ℂ))).sub
        (hψ.smooth.contDiffAt.comp x (contDiffAt_id.inv hx0.ne'))).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hx0] with y hy
      simp only [mellinReciprocalCutoff, if_pos (show 0 < y from hy), Function.comp_def, Pi.inv_apply, id_eq]
  · obtain ⟨c, hc, hψ0⟩ := hψ.zero_near_origin
    refine ⟨c⁻¹, fun x hx => ?_⟩
    have hx0 : 0 < x := (inv_pos.mpr hc).trans hx
    have hi : x⁻¹ < c := by
      simpa only [inv_inv] using (inv_lt_inv₀ hx0 (inv_pos.mpr hc)).mpr hx
    simp [mellinReciprocalCutoff, hx0, hψ0 x⁻¹ hi]

/-- Every slowly dilated logarithmic jet eventually vanishes at every real point. -/
theorem IsMellinTailCutoff.eventually_slow_jet_zero {ψ : ℝ → ℂ}
    (hψ : IsMellinTailCutoff ψ) (x : ℝ) (n : ℕ) :
    ∀ᶠ R : ℝ in atTop, iteratedDeriv n (fun y : ℝ => ψ (R⁻¹ * y)) x = 0 := by
  obtain ⟨a, ha, h0⟩ := hψ.zero_near_origin
  filter_upwards [eventually_gt_atTop (x / a), eventually_gt_atTop (0 : ℝ)] with R hR hR0
  have hRx : R⁻¹ * x < a := by
    have H := (div_lt_iff₀ ha).mp hR
    rw [mul_comm] at H
    simpa only [div_eq_mul_inv, mul_comm] using (div_lt_iff₀ hR0).mpr H
  have he : (fun y : ℝ => ψ (R⁻¹ * y)) =ᶠ[𝓝 x] fun _ => 0 := by
    have hc : ContinuousAt (fun y : ℝ => R⁻¹ * y) x := continuousAt_const.mul continuousAt_id
    filter_upwards [hc.eventually (Iio_mem_nhds hRx)] with y hy
    exact h0 (R⁻¹ * y) hy
  simpa only [iteratedDeriv_const, ite_self] using he.iteratedDeriv_eq n

/-- Every slowly dilated logarithmic jet tends to zero against an integrable weight. -/
theorem tendsto_integral_slow_weighted_iteratedDeriv {ψ G : ℝ → ℂ}
    (hψ : IsMellinTailCutoff ψ) (hG : IntegrableOn G (Ioi 0)) (n : ℕ) :
    Tendsto (fun R : ℝ => ∫ x : ℝ in Ioi 0,
      G x * ((x : ℂ) ^ n * iteratedDeriv n (fun y : ℝ => ψ (R⁻¹ * y)) x)) atTop
      (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := hψ.dilate_weighted_iteratedDeriv_bounded n
  have hm : ∀ R : ℝ, AEStronglyMeasurable (fun x : ℝ =>
      G x * ((x : ℂ) ^ n * iteratedDeriv n (fun y : ℝ => ψ (R⁻¹ * y)) x))
        (volume.restrict (Ioi 0)) := by
    intro R
    have hs : ContDiff ℝ ∞ (fun y : ℝ => ψ (R⁻¹ * y)) :=
      hψ.smooth.comp (contDiff_const.mul contDiff_id)
    exact hG.aestronglyMeasurable.mul
      (((Complex.continuous_ofReal.pow n).mul
        (hs.continuous_iteratedDeriv n (by exact_mod_cast le_top (a := (n : ℕ∞))))).aestronglyMeasurable)
  have hb : ∀ R : ℝ, ∀ᵐ x : ℝ ∂volume.restrict (Ioi 0),
      ‖G x * ((x : ℂ) ^ n * iteratedDeriv n (fun y : ℝ => ψ (R⁻¹ * y)) x)‖ ≤ ‖G x‖ * C := by
    intro R
    exact Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC R⁻¹ x) (norm_nonneg _)
  have hl : ∀ᵐ x : ℝ ∂volume.restrict (Ioi 0), Tendsto (fun R : ℝ =>
      G x * ((x : ℂ) ^ n * iteratedDeriv n (fun y : ℝ => ψ (R⁻¹ * y)) x)) atTop (𝓝 0) := by
    apply Eventually.of_forall
    intro x
    apply tendsto_const_nhds.congr'
    filter_upwards [hψ.eventually_slow_jet_zero x n] with R hR
    simp only [hR, mul_zero]
  simpa only [integral_zero] using
    tendsto_integral_filter_of_dominated_convergence (fun x => ‖G x‖ * C)
      (Eventually.of_forall hm) (Eventually.of_forall hb) (hG.norm.mul_const C) hl
end RHTower.WeilHigherDenominator
