import GaloisForLFunctions.HTGeometry.HillMassiveFrequency

/-!
# The frequency density of a time-dependent-speed evolution

The field of a massive species on the chart `-dt² + c(t)²δ` is the synthesis, over spatial
frequencies, of the fibrewise oscillator times an initial density. This file introduces that density
and proves the two facts a synthesis consumes: it is continuous — hence measurable — in the
frequency, and it is dominated by the initial density times a factor that does not depend on the
frequency at all.

The domination is what makes the construction possible: the fibrewise bound
`|û(t,ξ)| ≤ max(1, c(0)/c(t))e^{Kt}` holds for each frequency with its own existence constant, and
the right-hand side does not mention that constant, so the same function dominates every fibre.
-/

namespace GaloisForLFunctions.HTGeometry

open Set MeasureTheory

section Density

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {m K C : ℝ} {c dc : ℝ → ℝ} {G₀ : E → ℂ}

/-- The frequency density of the evolution: the fibrewise oscillator times the initial density. -/
noncomputable def hillDensity (m : ℝ) (c : ℝ → ℝ) (G₀ : E → ℂ) (t : ℝ) (ξ : E) : ℂ :=
  (hillSolution (massiveFreq m c ‖ξ‖) (1, 0) t : ℂ) * G₀ ξ

/-- The density of the time derivative. -/
noncomputable def hillDensityDeriv (m : ℝ) (c : ℝ → ℝ) (G₀ : E → ℂ) (t : ℝ) (ξ : E) : ℂ :=
  (hillSolutionDeriv (massiveFreq m c ‖ξ‖) (1, 0) t : ℂ) * G₀ ξ

/-! ## Continuity in the frequency -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem continuous_hillDensity (hm : 0 < m) (hc : Continuous c) (hC : ∀ r, c r ^ 2 ≤ C ^ 2)
    (hG : Continuous G₀) {t : ℝ} (ht : 0 ≤ t) : Continuous (hillDensity m c G₀ t) := by
  have hfibre : Continuous fun s : ℝ => hillFlow (massiveFreq m c s) (1, 0) t := by
    refine continuous_iff_continuousAt.mpr fun s₀ => ?_
    exact continuousAt_hillFlow_massive (C := C) (t := t) (b := t) hm hc hC (1, 0)
      ⟨ht, le_rfl⟩ s₀
  have hscalar : Continuous fun s : ℝ => hillSolution (massiveFreq m c s) (1, 0) t :=
    continuous_fst.comp hfibre
  have hnorm : Continuous fun ξ : E => ‖ξ‖ := continuous_norm
  have hcomp : Continuous fun ξ : E => hillSolution (massiveFreq m c ‖ξ‖) (1, 0) t :=
    hscalar.comp hnorm
  exact (Complex.continuous_ofReal.comp hcomp).mul hG

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem aestronglyMeasurable_hillDensity [MeasurableSpace E] [BorelSpace E]
    (hm : 0 < m) (hc : Continuous c) (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hG : Continuous G₀)
    {t : ℝ} (ht : 0 ≤ t) (μ : Measure E) :
    AEStronglyMeasurable (hillDensity m c G₀ t) μ :=
  (continuous_hillDensity hm hc hC hG ht).aestronglyMeasurable

/-! ## Domination, uniformly in the frequency -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **The density is dominated by the initial density**, with a factor that does not depend on the
frequency. -/
theorem norm_hillDensity_le (hm : 0 < m) (hc : Continuous c) (hcd : ∀ r, HasDerivAt c (dc r) r)
    (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r) (hC : ∀ r, c r ^ 2 ≤ C ^ 2)
    {t : ℝ} (ht : 0 ≤ t) (ξ : E) :
    ‖hillDensity m c G₀ t ξ‖ ≤ (max 1 (c 0 / c t) * Real.exp (K * t)) * ‖G₀ ξ‖ := by
  have hfib := abs_hillSolution_massive_cos_le (S := ‖ξ‖) (t := t) (b := t) hm hc hcd hcpos hK hC
    le_rfl ⟨ht, le_rfl⟩
  have hval : ‖hillDensity m c G₀ t ξ‖
      = |hillSolution (massiveFreq m c ‖ξ‖) (1, 0) t| * ‖G₀ ξ‖ := by
    rw [hillDensity, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hval]
  exact mul_le_mul_of_nonneg_right hfib (norm_nonneg _)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **The density of the time derivative costs one power of the frequency.** -/
theorem norm_hillDensityDeriv_le (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) {t : ℝ} (ht : 0 ≤ t) (ξ : E) :
    ‖hillDensityDeriv m c G₀ t ξ‖ ≤
      (massiveFreq m c ‖ξ‖ 0 * Real.exp (K * t)) * ‖G₀ ξ‖ := by
  have hfib := abs_hillSolutionDeriv_massive_cos_le (S := ‖ξ‖) (t := t) (b := t) hm hc hcd hcpos
    hK hC le_rfl ⟨ht, le_rfl⟩
  have hval : ‖hillDensityDeriv m c G₀ t ξ‖
      = |hillSolutionDeriv (massiveFreq m c ‖ξ‖) (1, 0) t| * ‖G₀ ξ‖ := by
    rw [hillDensityDeriv, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hval]
  exact mul_le_mul_of_nonneg_right hfib (norm_nonneg _)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The frequency weight of the derivative density is at most `m + c(0)‖ξ‖`. -/
theorem massiveFreq_zero_le (hm : 0 < m) (hcpos : ∀ r, 0 < c r) (ξ : E) :
    massiveFreq m c ‖ξ‖ 0 ≤ m + c 0 * ‖ξ‖ := by
  have hm0 : (0 : ℝ) ≤ m := le_of_lt hm
  have hc0 : (0 : ℝ) ≤ c 0 * ‖ξ‖ := mul_nonneg (le_of_lt (hcpos 0)) (norm_nonneg _)
  have hsq : m ^ 2 + (c 0 * ‖ξ‖) ^ 2 ≤ (m + c 0 * ‖ξ‖) ^ 2 := by nlinarith
  calc massiveFreq m c ‖ξ‖ 0 = Real.sqrt (m ^ 2 + (c 0 * ‖ξ‖) ^ 2) := rfl
    _ ≤ Real.sqrt ((m + c 0 * ‖ξ‖) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = m + c 0 * ‖ξ‖ := Real.sqrt_sq (by linarith)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Integrable domination.** If the initial density is integrable, so is the frequency density at
every time, with a dominating function that does not depend on the frequency. -/
theorem integrable_of_hillDensity_bound [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    (hm : 0 < m) (hc : Continuous c) (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r)
    (hK : ∀ r, |dc r| ≤ K * c r) (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hG : Continuous G₀)
    (hint : Integrable (fun ξ : E => ‖G₀ ξ‖) μ) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (hillDensity m c G₀ t) μ := by
  refine Integrable.mono' (hint.const_mul (max 1 (c 0 / c t) * Real.exp (K * t)))
    (aestronglyMeasurable_hillDensity hm hc hC hG ht μ) ?_
  filter_upwards with ξ
  exact norm_hillDensity_le hm hc hcd hcpos hK hC ht ξ

end Density

end GaloisForLFunctions.HTGeometry
