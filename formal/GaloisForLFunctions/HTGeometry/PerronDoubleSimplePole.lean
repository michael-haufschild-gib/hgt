import GaloisForLFunctions.HTGeometry.PerronRationalKernels

/-!
# Perron integrals with a double and a simple pole

For `Re a, Re b < σ`, `a ≠ b`:

* `(1/2π) ∫ X^{σ+it}/(σ+it−a)² dt = 0` for `0 < X ≤ 1` (`perron_doublePole_of_le_one`), the
  complement of `perron_doublePole`;
* `(1/2π) ∫ X^{σ+it}/((σ+it−a)²(σ+it−b)) dt = (X^b − X^a)/(b−a)² − X^a log X/(b−a)` for `X > 1`
  (`perron_doubleSimple`), from the partial fraction
  `1/((s−a)²(s−b)) = (1/(b−a))·(1/((s−a)(s−b)) − 1/(s−a)²)`.
-/

open MeasureTheory Complex Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The double-pole Perron integral vanishes for `X ≤ 1`. -/
theorem perron_doublePole_of_le_one {σ : ℝ} {a : ℂ} (ha : a.re < σ) {X : ℝ} (hX0 : 0 < X)
    (hX : X ≤ 1) :
    (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, (X : ℂ) ^ ((σ : ℂ) + t * I) / (((σ : ℂ) + t * I) - a) ^ 2
      = 0 := by
  have hδ : 0 < σ - a.re := by linarith
  set F : ℂ → ℂ := fun b => (1 / (2 * Real.pi) : ℝ) •
    ∫ t : ℝ, (X : ℂ) ^ ((σ : ℂ) + t * I) / ((((σ : ℂ) + t * I) - a) * (((σ : ℂ) + t * I) - b))
    with hF
  have hFval : ∀ᶠ b in 𝓝[≠] a, F b = 0 := by
    have hball : Metric.ball a ((σ - a.re) / 2) ∈ 𝓝[≠] a :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds a (by positivity))
    filter_upwards [hball, self_mem_nhdsWithin] with b hb hba
    have hbre : b.re < σ := by
      have h1 : ‖b - a‖ < (σ - a.re) / 2 := by simpa [dist_eq_norm] using hb
      have h2 : |(b - a).re| ≤ ‖b - a‖ := Complex.abs_re_le_norm _
      rw [Complex.sub_re] at h2
      linarith [abs_le.mp h2 |>.2]
    rw [hF]
    simp only
    rw [perron_twoPole ha hbre (Ne.symm hba) hX0, if_neg (not_lt.mpr hX)]
  have hFlim : Tendsto F (𝓝[≠] a) (𝓝 (F a)) := by
    rw [hF]
    simp only
    refine Tendsto.const_smul ?_ _
    have hball : Metric.closedBall a ((σ - a.re) / 2) ∈ 𝓝[≠] a :=
      nhdsWithin_le_nhds (Metric.closedBall_mem_nhds a (by positivity))
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => (X ^ σ * 2 * (1 / min (σ - a.re) 1 ^ 2)) * (1 / (1 + (t - a.im) ^ 2))) ?_ ?_ ?_ ?_
    · filter_upwards [hball] with b hb
      have hbre : b.re < σ := by
        have h1 : ‖b - a‖ ≤ (σ - a.re) / 2 := by simpa [dist_eq_norm] using hb
        have h2 : |(b - a).re| ≤ ‖b - a‖ := Complex.abs_re_le_norm _
        rw [Complex.sub_re] at h2
        linarith [abs_le.mp h2 |>.2]
      have hne : ∀ (c : ℂ), c.re < σ → ∀ t : ℝ, (σ : ℂ) + t * I - c ≠ 0 := by
        intro c hc t h
        have := congrArg Complex.re h
        simp at this; linarith
      refine Continuous.aestronglyMeasurable ?_
      have hcp : Continuous (fun t : ℝ => (X : ℂ) ^ ((σ : ℂ) + t * I)) :=
        (by fun_prop : Continuous (fun t : ℝ => (σ : ℂ) + t * I)).const_cpow
          (Or.inl (by exact_mod_cast hX0.ne'))
      apply Continuous.div hcp
      · fun_prop
      · intro t; exact mul_ne_zero (hne a ha t) (hne b hbre t)
    · filter_upwards [hball] with b hb
      refine Filter.Eventually.of_forall fun t => ?_
      exact norm_twoPole_integrand_le ha (by simpa [dist_eq_norm] using hb) hX0 t
    · have := (integrable_inv_one_add_sq.comp_sub_right a.im).const_mul
        (X ^ σ * 2 * (1 / min (σ - a.re) 1 ^ 2))
      refine this.congr (Filter.Eventually.of_forall fun t => ?_)
      simp only [one_div]
    · refine Filter.Eventually.of_forall fun t => ?_
      have hne : (σ : ℂ) + t * I - a ≠ 0 := by
        intro h
        have := congrArg Complex.re h
        simp at this; linarith
      have hca : ContinuousAt (fun b : ℂ => (X : ℂ) ^ ((σ : ℂ) + t * I) /
          ((((σ : ℂ) + t * I) - a) * (((σ : ℂ) + t * I) - b))) a := by
        refine ContinuousAt.div continuousAt_const
          (continuousAt_const.mul (continuousAt_const.sub continuousAt_id)) ?_
        exact mul_ne_zero hne hne
      exact hca.tendsto.mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto F (𝓝[≠] a) (𝓝 0) :=
    tendsto_const_nhds.congr' (hFval.mono fun b hb => hb.symm)
  have := tendsto_nhds_unique hFlim hlim2
  rw [hF] at this
  simp only at this
  rw [← this]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp [sq]

theorem integrable_cpow_div_doubleSimple {σ : ℝ} {a b : ℂ} (ha : a.re < σ) (hb : b.re < σ)
    (hab : a ≠ b) {X : ℝ} (hX : 0 < X) :
    Integrable (fun t : ℝ => (X : ℂ) ^ ((σ : ℂ) + t * I) /
      ((((σ : ℂ) + t * I) - a) ^ 2 * (((σ : ℂ) + t * I) - b))) := by
  have h := ((integrable_cpow_div_twoPole ha hb hX).sub
    (integrable_cpow_div_doublePole ha hX)).const_mul (1 / (b - a))
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  have hne : ∀ (c : ℂ), c.re < σ → (σ : ℂ) + t * I - c ≠ 0 := by
    intro c hc h
    have := congrArg Complex.re h
    simp at this; linarith
  have h1 := hne a ha
  have h2 := hne b hb
  have h3 : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  simp only [Pi.sub_apply]
  field_simp
  ring

/-- **Double-plus-simple pole.**  For `X > 1`,
`(1/2π)∫ X^s/((s−a)²(s−b)) dt = (X^b − X^a)/(b−a)² − X^a log X/(b−a)`. -/
theorem perron_doubleSimple {σ : ℝ} {a b : ℂ} (ha : a.re < σ) (hb : b.re < σ) (hab : a ≠ b)
    {X : ℝ} (hX : 1 < X) :
    (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, (X : ℂ) ^ ((σ : ℂ) + t * I) /
        ((((σ : ℂ) + t * I) - a) ^ 2 * (((σ : ℂ) + t * I) - b))
      = ((X : ℂ) ^ b - (X : ℂ) ^ a) / (b - a) ^ 2 - (X : ℂ) ^ a * Complex.log X / (b - a) := by
  have hX0 : 0 < X := by linarith
  have h3 : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have h3' : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hsplit : (fun t : ℝ => (X : ℂ) ^ ((σ : ℂ) + t * I) /
      ((((σ : ℂ) + t * I) - a) ^ 2 * (((σ : ℂ) + t * I) - b))) =
      fun t : ℝ => (1 / (b - a)) * ((X : ℂ) ^ ((σ : ℂ) + t * I) /
        ((((σ : ℂ) + t * I) - a) * (((σ : ℂ) + t * I) - b)) -
        (X : ℂ) ^ ((σ : ℂ) + t * I) / (((σ : ℂ) + t * I) - a) ^ 2) := by
    funext t
    have hne : ∀ (c : ℂ), c.re < σ → (σ : ℂ) + t * I - c ≠ 0 := by
      intro c hc h
      have := congrArg Complex.re h
      simp at this; linarith
    have h1 := hne a ha
    have h2 := hne b hb
    field_simp
    ring
  rw [hsplit, integral_const_mul, integral_sub (integrable_cpow_div_twoPole ha hb hX0)
    (integrable_cpow_div_doublePole ha hX0), ← mul_smul_comm, smul_sub,
    perron_twoPole ha hb hab hX0, if_pos hX, perron_doublePole ha hX]
  field_simp
  ring

end GaloisForLFunctions.HTGeometry
