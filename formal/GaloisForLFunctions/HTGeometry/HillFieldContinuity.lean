import GaloisForLFunctions.HTGeometry.HillDensityTwoSided

/-!
# Joint continuity of the field, and the nonvanishing near an event

A probe must be nonvanishing on a neighbourhood of its event, so the field has to be continuous in
the time and the point together. Dominated convergence gives that: the fibre is continuous in time,
the character is continuous in the point, and the dominating function of the previous file is the
same for all nearby times because the speed is bounded below.

Since the field at time zero is the plain synthesis of its datum, a datum whose synthesis does not
vanish at a point produces a field that does not vanish on a whole neighbourhood of that event.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Metric

open scoped RealInnerProductSpace

section Continuity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {m K C cmin : ℝ} {c dc : ℝ → ℝ} {G₀ : E → ℂ}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The fibre of the density is continuous in time. -/
theorem continuous_hillDensity_time (hm : 0 < m) (hc : Continuous c) (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ))
    (ξ : E) : Continuous fun t : ℝ => hillDensity m c G₀ t ξ := by
  have hM1 : (1 : ℝ) ≤ max 1 (m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) := le_max_left _ _
  have hMb : ∀ r, massiveFreq m c ‖ξ‖ r ^ (2 : ℕ) ≤ max 1 (m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) := fun r =>
    (massiveFreq_sq_le hm hC le_rfl r).trans (le_max_right _ _)
  have hcont : Continuous fun t : ℝ => hillSolution (massiveFreq m c ‖ξ‖) (1, 0) t := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    exact (hasDerivAt_hillSolution (continuous_massiveFreq hc m ‖ξ‖) hM1 hMb (1, 0) t).continuousAt
  exact (Complex.continuous_ofReal.comp hcont).mul continuous_const

/-- **The field is continuous in the time and the point together.** -/
theorem continuousAt_hillEvolutionField (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r)
    (hG : Continuous G₀) (hint : Integrable (fun ξ : E => ‖G₀ ξ‖) (volume : Measure E))
    (t₀ : ℝ) (x₀ : E) :
    ContinuousAt (fun p : ℝ × E => hillEvolutionField m c G₀ p.1 p.2) (t₀, x₀) := by
  have hK0 : 0 ≤ K := by
    have h0 : (0 : ℝ) ≤ |dc 0| := abs_nonneg _
    have h1 := hK 0
    have h2 := hcpos 0
    nlinarith
  set R : ℝ := max 1 (c 0 / cmin) * Real.exp (K * (|t₀| + 1)) with hR
  have hFmeas : ∀ᶠ p : ℝ × E in nhds (t₀, x₀),
      AEStronglyMeasurable (fun ξ : E => kgChar p.2 ξ * hillDensity m c G₀ p.1 ξ)
        (volume : Measure E) := by
    filter_upwards with p
    exact (((continuous_kgChar' p.2).aestronglyMeasurable)).mul
      (aestronglyMeasurable_hillDensity_all (C := C) hm hc hC hG p.1 _)
  have hbound : ∀ᶠ p : ℝ × E in nhds (t₀, x₀), ∀ᵐ ξ : E ∂(volume : Measure E),
      ‖kgChar p.2 ξ * hillDensity m c G₀ p.1 ξ‖ ≤ R * ‖G₀ ξ‖ := by
    have hball : ball ((t₀, x₀) : ℝ × E) 1 ∈ nhds ((t₀, x₀) : ℝ × E) :=
      ball_mem_nhds _ one_pos
    filter_upwards [hball] with p hp
    have hdist : dist p.1 t₀ < 1 := lt_of_le_of_lt (le_max_left _ _) hp
    have habs : |p.1| ≤ |t₀| + 1 := by
      have h1 : |p.1 - t₀| < 1 := by simpa [Real.dist_eq] using hdist
      have hpair := abs_lt.mp h1
      cases abs_cases p.1 with
      | inl h => cases abs_cases t₀ with
        | inl h2 => linarith [h.1, h2.1, hpair.1, hpair.2]
        | inr h2 => linarith [h.1, h2.1, hpair.1, hpair.2]
      | inr h => cases abs_cases t₀ with
        | inl h2 => linarith [h.1, h2.1, hpair.1, hpair.2]
        | inr h2 => linarith [h.1, h2.1, hpair.1, hpair.2]
    filter_upwards with ξ
    have hbase := norm_hillDensity_le_abs (G₀ := G₀) hm hc hcd hcpos hK hC p.1 ξ
    have hratio : max 1 (c 0 / c p.1) ≤ max 1 (c 0 / cmin) :=
      max_le_max le_rfl (div_le_div_of_nonneg_left (le_of_lt (hcpos 0)) hcmin (hclow p.1))
    have hexp : Real.exp (K * |p.1|) ≤ Real.exp (K * (|t₀| + 1)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs hK0)
    have hstep : max 1 (c 0 / c p.1) * Real.exp (K * |p.1|) ≤ R :=
      mul_le_mul hratio hexp (le_of_lt (Real.exp_pos _))
        (le_trans zero_le_one (le_max_left _ _))
    calc ‖kgChar p.2 ξ * hillDensity m c G₀ p.1 ξ‖
        = ‖hillDensity m c G₀ p.1 ξ‖ := by rw [norm_mul, norm_kgChar, one_mul]
      _ ≤ (max 1 (c 0 / c p.1) * Real.exp (K * |p.1|)) * ‖G₀ ξ‖ := hbase
      _ ≤ R * ‖G₀ ξ‖ := mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
  have hcont : ∀ᵐ ξ : E ∂(volume : Measure E),
      ContinuousAt (fun p : ℝ × E => kgChar p.2 ξ * hillDensity m c G₀ p.1 ξ) (t₀, x₀) := by
    filter_upwards with ξ
    have hcharx : Continuous fun x : E => kgChar x ξ := by
      have hinner : Continuous fun x : E => ⟪ξ, x⟫ :=
        continuous_inner.comp (continuous_const.prodMk continuous_id)
      exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp hinner)
    have h1 : Continuous fun p : ℝ × E => kgChar p.2 ξ := hcharx.comp continuous_snd
    have h2 : Continuous fun p : ℝ × E => hillDensity m c G₀ p.1 ξ :=
      (continuous_hillDensity_time (C := C) hm hc hC ξ).comp continuous_fst
    exact (h1.mul h2).continuousAt
  exact continuousAt_of_dominated hFmeas hbound (hint.const_mul R) hcont

/-- **The field does not vanish near an event where its datum's synthesis does not vanish.** -/
theorem eventually_hillEvolutionField_ne_zero (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r)
    (hG : Continuous G₀) (hint : Integrable (fun ξ : E => ‖G₀ ξ‖) (volume : Measure E))
    {x₀ : E} (hne : kgSynthesis G₀ x₀ ≠ 0) :
    ∀ᶠ p : ℝ × E in nhds ((0 : ℝ), x₀), hillEvolutionField m c G₀ p.1 p.2 ≠ 0 := by
  have hcontAt := continuousAt_hillEvolutionField hm hc hcd hcpos hK hC hcmin hclow hG hint 0 x₀
  have hval : hillEvolutionField m c G₀ 0 x₀ ≠ 0 := by
    rw [hillEvolutionField_zero (C := C) hm hc hC x₀]
    exact hne
  exact hcontAt.eventually_ne hval

end Continuity

end GaloisForLFunctions.HTGeometry
