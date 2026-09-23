import GaloisForLFunctions.HTGeometry.HillWeightTransfers

/-!
# Syntheses of a time-dependent density are continuous in the event

Each object of the second-order calculus is the synthesis of a density that depends on time. If the
family is continuous in time at each frequency and is dominated, uniformly on every window of times,
by one fixed integrable function of the frequency, then dominated convergence makes the synthesis
continuous in the time and the point together.

The three families of the calculus — the second-derivative density, the derived velocity density and
the twice-derived density — all satisfy those hypotheses, with the weight of the previous file.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Metric

open scoped RealInnerProductSpace

section EventContinuity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {m K C : ℝ} {c dc : ℝ → ℝ} {G₀ : E → ℂ}

/-- **A dominated time-dependent density has a synthesis continuous in the event.** -/
theorem continuous_kgSynthesis_event {F : ℝ → E → ℂ} {B : E → ℝ}
    (hmeas : ∀ r : ℝ, AEStronglyMeasurable (F r) (volume : Measure E))
    (htime : ∀ ξ : E, Continuous fun r : ℝ => F r ξ)
    (hbound : ∀ T : ℝ, ∃ A : ℝ, ∀ r : ℝ, |r| ≤ T → ∀ ξ : E, ‖F r ξ‖ ≤ A * B ξ)
    (hB : Integrable B (volume : Measure E)) :
    Continuous fun p : ℝ × E => kgSynthesis (F p.1) p.2 := by
  refine continuous_iff_continuousAt.mpr fun p₀ => ?_
  obtain ⟨t₀, x₀⟩ := p₀
  obtain ⟨A, hA⟩ := hbound (|t₀| + 1)
  simp only [kgSynthesis]
  have hFmeas : ∀ᶠ p : ℝ × E in nhds (t₀, x₀),
      AEStronglyMeasurable (fun ξ : E => kgChar p.2 ξ * F p.1 ξ) (volume : Measure E) := by
    filter_upwards with p
    exact ((continuous_kgChar' p.2).aestronglyMeasurable).mul (hmeas p.1)
  have hdom : ∀ᶠ p : ℝ × E in nhds (t₀, x₀), ∀ᵐ ξ : E ∂(volume : Measure E),
      ‖kgChar p.2 ξ * F p.1 ξ‖ ≤ A * B ξ := by
    have hball : ball ((t₀, x₀) : ℝ × E) 1 ∈ nhds ((t₀, x₀) : ℝ × E) := ball_mem_nhds _ one_pos
    filter_upwards [hball] with p hp
    have hdist : dist p.1 t₀ < 1 := lt_of_le_of_lt (le_max_left _ _) hp
    have habs : |p.1| ≤ |t₀| + 1 := abs_le_abs_add_one_of_dist_lt hdist
    filter_upwards with ξ
    rw [norm_mul, norm_kgChar, one_mul]
    exact hA p.1 habs ξ
  have hcont : ∀ᵐ ξ : E ∂(volume : Measure E),
      ContinuousAt (fun p : ℝ × E => kgChar p.2 ξ * F p.1 ξ) (t₀, x₀) := by
    filter_upwards with ξ
    exact (((continuous_kgChar_point ξ).comp continuous_snd).mul
      ((htime ξ).comp continuous_fst)).continuousAt
  exact continuousAt_of_dominated hFmeas hdom (hB.const_mul A) hcont

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The second-derivative density is continuous in time.** -/
theorem continuous_hillDensitySecond_time (hm : 0 < m) (hc : Continuous c)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (ξ : E) :
    Continuous fun t : ℝ => hillDensitySecond m c G₀ t ξ := by
  have hM1 : (1 : ℝ) ≤ max 1 (m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) := le_max_left _ _
  have hMb : ∀ r, massiveFreq m c ‖ξ‖ r ^ (2 : ℕ) ≤ max 1 (m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) := fun r =>
    (massiveFreq_sq_le hm hC le_rfl r).trans (le_max_right _ _)
  have hflow : Continuous (hillFlow (massiveFreq m c ‖ξ‖) (1, 0)) :=
    continuous_hillFlow (continuous_massiveFreq hc m ‖ξ‖) hM1 hMb (1, 0)
  have hsol : Continuous fun t : ℝ => hillSolution (massiveFreq m c ‖ξ‖) (1, 0) t :=
    continuous_fst.comp hflow
  have hfreq : Continuous fun t : ℝ => massiveFreq m c ‖ξ‖ t := continuous_massiveFreq hc m ‖ξ‖
  have hprod : Continuous fun t : ℝ =>
      (-(massiveFreq m c ‖ξ‖ t ^ (2 : ℕ)) * hillSolution (massiveFreq m c ‖ξ‖) (1, 0) t : ℝ) :=
    ((hfreq.pow 2).neg).mul hsol
  exact (Complex.continuous_ofReal.comp hprod).mul continuous_const

end EventContinuity

end GaloisForLFunctions.HTGeometry
