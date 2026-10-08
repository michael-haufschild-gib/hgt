import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorCutoffIntegration
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Uniform logarithmic jets and actual cutoff limits

Every dilated smooth cutoff has uniformly bounded logarithmic jets of every
order. At positive points its zeroth jet tends to one and higher jets vanish.
Dominated convergence therefore gives the actual integral limit against any
absolutely integrable weight. No stronger exponent or boundary regularity is
needed for this cutoff step.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped ContDiff
namespace RHTower.WeilHigherDenominator

/-- Every logarithmically weighted cutoff derivative is bounded on the entire line. -/
theorem IsMellinTailCutoff.weighted_iteratedDeriv_bounded {ψ : ℝ → ℂ}
    (hψ : IsMellinTailCutoff ψ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖(x : ℂ) ^ n * iteratedDeriv n ψ x‖ ≤ C := by
  by_cases hn : n = 0
  · subst n
    obtain ⟨C, hC⟩ := hψ.bounded
    refine ⟨max 0 C, le_max_left _ _, fun x => ?_⟩
    simpa using (hC x).trans (le_max_right 0 C)
  obtain ⟨a, _, ha⟩ := hψ.iteratedDeriv_zero_near_origin n
  obtain ⟨b, hb⟩ := hψ.iteratedDeriv_zero_near_infinity hn
  have hc : Continuous (fun x : ℝ => (x : ℂ) ^ n * iteratedDeriv n ψ x) :=
    (Complex.continuous_ofReal.pow n).mul
      (hψ.smooth.continuous_iteratedDeriv n (by exact_mod_cast le_top (a := (n : ℕ∞))))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc.continuousOn (s := Icc a b))
  refine ⟨max 0 C, le_max_left _ _, fun x => ?_⟩
  by_cases hxa : x < a
  · simp only [ha x hxa, mul_zero, norm_zero]
    exact le_max_left _ _
  by_cases hxb : b < x
  · simp only [hb x hxb, mul_zero, norm_zero]
    exact le_max_left _ _
  exact (hC x ⟨le_of_not_gt hxa, le_of_not_gt hxb⟩).trans (le_max_right _ _)

/-- Logarithmically weighted jets of a dilated cutoff equal its jets at the dilated point. -/
theorem weighted_iteratedDeriv_cutoff_dilate {ψ : ℝ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (n : ℕ) (R x : ℝ) :
    (x : ℂ) ^ n * iteratedDeriv n (fun y : ℝ => ψ (R * y)) x =
      ((R * x : ℝ) : ℂ) ^ n * iteratedDeriv n ψ (R * x) := by
  have hs : ContDiff ℝ n ψ := hψ.of_le (by exact_mod_cast le_top (a := (n : ℕ∞)))
  rw [iteratedDeriv_comp_const_smul hs]
  simp only [Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_mul, mul_pow]
  ring

/-- Dilation introduces no loss in the logarithmic jet envelope. -/
theorem IsMellinTailCutoff.dilate_weighted_iteratedDeriv_bounded {ψ : ℝ → ℂ}
    (hψ : IsMellinTailCutoff ψ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R x : ℝ,
      ‖(x : ℂ) ^ n * iteratedDeriv n (fun y : ℝ => ψ (R * y)) x‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := hψ.weighted_iteratedDeriv_bounded n
  refine ⟨C, hC0, fun R x => ?_⟩
  rw [weighted_iteratedDeriv_cutoff_dilate hψ.smooth]
  exact hC (R * x)

/-- At every positive point a dilated cutoff eventually agrees locally with one. -/
theorem IsMellinTailCutoff.eventually_dilate_eq_one {ψ : ℝ → ℂ}
    (hψ : IsMellinTailCutoff ψ) {x : ℝ} (hx : 0 < x) :
    ∀ᶠ R : ℝ in atTop, (fun y : ℝ => ψ (R * y)) =ᶠ[𝓝 x] fun _ => 1 := by
  obtain ⟨b, hb⟩ := hψ.one_near_infinity
  filter_upwards [eventually_gt_atTop (b / x)] with R hR
  have hRx : b < R * x := (div_lt_iff₀ hx).mp hR
  have hc : ContinuousAt (fun y : ℝ => R * y) x := continuousAt_const.mul continuousAt_id
  filter_upwards [hc.eventually (Ioi_mem_nhds hRx)] with y hy
  exact hb (R * y) hy

/-- Every positive derivative of the dilated cutoff eventually vanishes pointwise. -/
theorem IsMellinTailCutoff.eventually_dilate_iteratedDeriv {ψ : ℝ → ℂ}
    (hψ : IsMellinTailCutoff ψ) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ∀ᶠ R : ℝ in atTop, iteratedDeriv n (fun y : ℝ => ψ (R * y)) x =
      if n = 0 then 1 else 0 := by
  filter_upwards [hψ.eventually_dilate_eq_one hx] with R hR
  simpa only [iteratedDeriv_const] using hR.iteratedDeriv_eq n

/-- Absolute integrability suffices for every dilated logarithmic jet limit. -/
theorem tendsto_integral_dilate_weighted_iteratedDeriv {ψ G : ℝ → ℂ}
    (hψ : IsMellinTailCutoff ψ) (hG : IntegrableOn G (Ioi 0)) (n : ℕ) :
    Tendsto (fun R : ℝ => ∫ x : ℝ in Ioi 0,
      G x * ((x : ℂ) ^ n * iteratedDeriv n (fun y : ℝ => ψ (R * y)) x)) atTop
      (𝓝 (if n = 0 then ∫ x : ℝ in Ioi 0, G x else 0)) := by
  obtain ⟨C, hC0, hC⟩ := hψ.dilate_weighted_iteratedDeriv_bounded n
  have hm : ∀ R : ℝ, AEStronglyMeasurable (fun x : ℝ =>
      G x * ((x : ℂ) ^ n * iteratedDeriv n (fun y : ℝ => ψ (R * y)) x))
        (volume.restrict (Ioi 0)) := by
    intro R
    have hs : ContDiff ℝ ∞ (fun y : ℝ => ψ (R * y)) :=
      hψ.smooth.comp (contDiff_const.mul contDiff_id)
    exact hG.aestronglyMeasurable.mul
      (((Complex.continuous_ofReal.pow n).mul
        (hs.continuous_iteratedDeriv n (by exact_mod_cast le_top (a := (n : ℕ∞))))).aestronglyMeasurable)
  have hb : ∀ R : ℝ, ∀ᵐ x : ℝ ∂volume.restrict (Ioi 0),
      ‖G x * ((x : ℂ) ^ n * iteratedDeriv n (fun y : ℝ => ψ (R * y)) x)‖ ≤ ‖G x‖ * C := by
    intro R
    exact Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC R x) (norm_nonneg _)
  have hl : ∀ᵐ x : ℝ ∂volume.restrict (Ioi 0), Tendsto (fun R : ℝ =>
      G x * ((x : ℂ) ^ n * iteratedDeriv n (fun y : ℝ => ψ (R * y)) x)) atTop
        (𝓝 (if n = 0 then G x else 0)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [hψ.eventually_dilate_iteratedDeriv hx n] with R hR
    rw [hR]
    split_ifs with hn
    · simp [hn]
    · simp
  have H := tendsto_integral_filter_of_dominated_convergence (fun x => ‖G x‖ * C)
    (Eventually.of_forall hm) (Eventually.of_forall hb) (hG.norm.mul_const C) hl
  by_cases hn : n = 0
  · simpa only [hn, if_pos, integral_zero] using H
  · simpa only [hn, if_false, integral_zero] using H
end RHTower.WeilHigherDenominator
