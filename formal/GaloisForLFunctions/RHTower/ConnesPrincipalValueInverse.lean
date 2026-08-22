import GaloisForLFunctions.RHTower.ConnesSgnFourierKernel
import GaloisForLFunctions.RHTower.ConnesTraceErrorRapidDecay

/-!
# The principal value `PV ∫ G(u)/u du`

Step 1b of the route to the last §V identification of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Connes' principal value is written here as an *absolutely convergent* expression,

  `PV ∫ G(u)/u du = ∫_{|u| ≤ 1} (G(u) − G(0))/u du + ∫_{|u| > 1} G(u)/u du`,

so that no improper limit has to be carried around.  The inner integrand is bounded because a
Schwartz function is Lipschitz (`connes_schwartz_diffQuotient_bound`), and the outer one is
dominated by `‖G‖`.  The module also records the oddness cancellation
`∫_{|u| ≤ 1} c/u du = 0`, which is what removes the Euler-Mascheroni constant from the final
identification.
-/

open MeasureTheory Set Filter Topology Real
open scoped SchwartzMap

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The unit ball and its complement are measurable. -/
theorem connes_unitBall_measurable : MeasurableSet {u : ℝ | |u| ≤ 1} :=
  measurableSet_le measurable_norm measurable_const

theorem connes_unitBallCompl_measurable : MeasurableSet {u : ℝ | 1 < |u|} :=
  measurableSet_lt measurable_const measurable_norm

/-- **A Schwartz function is globally Lipschitz.** -/
theorem connes_schwartz_diffQuotient_bound (G : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, ‖G u - G 0‖ ≤ C * |u| := by
  set C : ℝ := SchwartzMap.seminorm ℂ 0 0 (SchwartzMap.derivCLM ℂ ℂ G) with hC
  have hC0 : (0 : ℝ) ≤ C := apply_nonneg _ _
  refine ⟨C, hC0, fun u => ?_⟩
  have hbound : ∀ x ∈ (Set.univ : Set ℝ), ‖deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ ≤ C := by
    intro x _
    have hd : deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x = (SchwartzMap.derivCLM ℂ ℂ G) x := by
      rw [SchwartzMap.derivCLM_apply]
    rw [hd]
    have h0 := SchwartzMap.norm_pow_mul_le_seminorm ℂ (SchwartzMap.derivCLM ℂ ℂ G) 0 x
    simpa using h0
  have hdiff : ∀ x ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x :=
    fun x _ => G.differentiable.differentiableAt
  have h := (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_deriv_le
    hdiff hbound (Set.mem_univ (0 : ℝ)) (Set.mem_univ u)
  simpa [Real.norm_eq_abs] using h

/-- The inner principal-value integrand is integrable on the unit ball. -/
theorem connes_pv_inner_integrable (G : 𝓢(ℝ, ℂ)) :
    IntegrableOn (fun u : ℝ => (G u - G 0) / u) {u : ℝ | |u| ≤ 1} volume := by
  obtain ⟨C, hC0, hC⟩ := connes_schwartz_diffQuotient_bound G
  have hset : {u : ℝ | |u| ≤ 1} = Set.Icc (-1 : ℝ) 1 := by
    ext u
    simp [abs_le]
  rw [hset]
  refine Measure.integrableOn_of_bounded (M := C) measure_Icc_lt_top.ne ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    exact (G.continuous.measurable.sub measurable_const).div
      (Complex.measurable_ofReal.comp measurable_id)
  · filter_upwards with u
    rcases eq_or_ne u 0 with hu | hu
    · simp [hu, hC0]
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
      rw [div_le_iff₀ (abs_pos.mpr hu)]
      exact hC u

/-- The outer principal-value integrand is integrable off the unit ball. -/
theorem connes_pv_outer_integrable (G : 𝓢(ℝ, ℂ)) :
    IntegrableOn (fun u : ℝ => G u / u) {u : ℝ | 1 < |u|} volume := by
  refine Integrable.mono' ((G.integrable (μ := volume)).norm.integrableOn) ?_ ?_
  · refine AEStronglyMeasurable.restrict ?_
    refine Measurable.aestronglyMeasurable ?_
    exact G.continuous.measurable.div (Complex.measurable_ofReal.comp measurable_id)
  · filter_upwards [ae_restrict_mem connes_unitBallCompl_measurable] with u hu
    have hu1 : 1 < |u| := hu
    have hu0 : (0 : ℝ) < |u| := lt_trans zero_lt_one hu1
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    rw [div_le_iff₀ hu0]
    exact le_mul_of_one_le_right (norm_nonneg _) hu1.le

/-- **Connes' principal value**, as an absolutely convergent expression. -/
def connesPVinv (G : ℝ → ℂ) : ℂ :=
  (∫ u in {u : ℝ | |u| ≤ 1}, (G u - G 0) / u) + ∫ u in {u : ℝ | 1 < |u|}, G u / u

/-- **The oddness cancellation.**  An odd interval-integrable function has vanishing integral over
a symmetric interval.  This is what removes the Euler-Mascheroni constant: the constant part of
the principal-value integrand pairs with the *even* factor `1 − cos 2πXu` to give an odd
integrand. -/
theorem connes_integral_odd_symmetric {f : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hodd : ∀ x : ℝ, f (-x) = -f x)
    (hint : IntervalIntegrable f volume (-a) a) :
    (∫ x in (-a : ℝ)..a, f x) = 0 := by
  have hna : (-a : ℝ) ≤ a := by linarith
  have huIcc : Set.uIcc (-a : ℝ) a = Set.Icc (-a) a := Set.uIcc_of_le hna
  have h1 : Set.uIcc (-a : ℝ) (0 : ℝ) ⊆ Set.uIcc (-a : ℝ) a := by
    rw [huIcc, Set.uIcc_of_le (by linarith : (-a : ℝ) ≤ 0)]
    exact Set.Icc_subset_Icc (le_refl _) ha
  have h2 : Set.uIcc (0 : ℝ) a ⊆ Set.uIcc (-a : ℝ) a := by
    rw [huIcc, Set.uIcc_of_le ha]
    exact Set.Icc_subset_Icc (by linarith) (le_refl _)
  have hsplit : (∫ x in (-a : ℝ)..a, f x)
      = (∫ x in (-a : ℝ)..(0 : ℝ), f x) + ∫ x in (0 : ℝ)..a, f x :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hint.mono_set h1) (hint.mono_set h2)).symm
  have hrefl : (∫ x in (-a : ℝ)..(0 : ℝ), f x) = ∫ x in (0 : ℝ)..a, f (-x) := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := a) f
    simpa using h.symm
  rw [hsplit, hrefl]
  have hcongr : (∫ x in (0 : ℝ)..a, f (-x)) = ∫ x in (0 : ℝ)..a, -f x :=
    intervalIntegral.integral_congr (fun x _ => hodd x)
  rw [hcongr, intervalIntegral.integral_neg, neg_add_cancel]

end

end GaloisForLFunctions.RHTower
