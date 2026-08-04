import GaloisForLFunctions.HTGeometry.HillFieldSpace
import GaloisForLFunctions.HTGeometry.HillFlowTwoSidedStability

/-!
# The density and the field, without a sign condition on time

The density statements were proved for nonnegative times, because the fibrewise estimates were. With
the two-sided estimates they hold for every time, with `|t|` in the exponential.

The file also records the value at time zero: the fibre starts at `1`, so the density starts at the
initial density and the field starts at its plain synthesis. That is where the nonvanishing of a
probe will come from, since the corpus's constant-coefficient construction already supplies data
whose synthesis does not vanish.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

section TwoSidedDensity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {m K C : ℝ} {c dc : ℝ → ℝ} {G₀ : E → ℂ}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The density at every time**, dominated by the initial density with a factor free of the
frequency. -/
theorem norm_hillDensity_le_abs (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (t : ℝ) (ξ : E) :
    ‖hillDensity m c G₀ t ξ‖ ≤ (max 1 (c 0 / c t) * Real.exp (K * |t|)) * ‖G₀ ξ‖ := by
  have hfib := abs_hillSolution_massive_le_abs (S := ‖ξ‖) hm hc hcd hcpos hK hC le_rfl t
  have hval : ‖hillDensity m c G₀ t ξ‖
      = |hillSolution (massiveFreq m c ‖ξ‖) (1, 0) t| * ‖G₀ ξ‖ := by
    rw [hillDensity, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hval]
  exact mul_le_mul_of_nonneg_right hfib (norm_nonneg _)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The velocity density at every time.** -/
theorem norm_hillDensityDeriv_le_abs (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (t : ℝ) (ξ : E) :
    ‖hillDensityDeriv m c G₀ t ξ‖ ≤
      (massiveFreq m c ‖ξ‖ 0 * Real.exp (K * |t|)) * ‖G₀ ξ‖ := by
  have hfib := abs_hillSolutionDeriv_massive_le_abs (S := ‖ξ‖) hm hc hcd hcpos hK hC le_rfl t
  have hval : ‖hillDensityDeriv m c G₀ t ξ‖
      = |hillSolutionDeriv (massiveFreq m c ‖ξ‖) (1, 0) t| * ‖G₀ ξ‖ := by
    rw [hillDensityDeriv, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hval]
  exact mul_le_mul_of_nonneg_right hfib (norm_nonneg _)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The density is continuous in the frequency at every time.** -/
theorem continuous_hillDensity_all (hm : 0 < m) (hc : Continuous c) (hC : ∀ r, c r ^ 2 ≤ C ^ 2)
    (hG : Continuous G₀) (t : ℝ) : Continuous (hillDensity m c G₀ t) := by
  have hfibre : Continuous fun s : ℝ => hillFlow (massiveFreq m c s) (1, 0) t :=
    continuous_iff_continuousAt.mpr fun s₀ =>
      continuousAt_hillFlow_massive_all (C := C) hm hc hC (1, 0) t s₀
  have hscalar : Continuous fun s : ℝ => hillSolution (massiveFreq m c s) (1, 0) t :=
    continuous_fst.comp hfibre
  exact (Complex.continuous_ofReal.comp (hscalar.comp continuous_norm)).mul hG

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem aestronglyMeasurable_hillDensity_all (hm : 0 < m) (hc : Continuous c)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hG : Continuous G₀) (t : ℝ) (μ : Measure E) :
    AEStronglyMeasurable (hillDensity m c G₀ t) μ :=
  (continuous_hillDensity_all (C := C) hm hc hC hG t).aestronglyMeasurable

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Integrability at every time.** -/
theorem integrable_hillDensity_all {μ : Measure E} (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hG : Continuous G₀)
    (hint : Integrable (fun ξ : E => ‖G₀ ξ‖) μ) (t : ℝ) :
    Integrable (hillDensity m c G₀ t) μ := by
  refine Integrable.mono' (hint.const_mul (max 1 (c 0 / c t) * Real.exp (K * |t|)))
    (aestronglyMeasurable_hillDensity_all (C := C) hm hc hC hG t μ) ?_
  filter_upwards with ξ
  exact norm_hillDensity_le_abs hm hc hcd hcpos hK hC t ξ

/-! ## The value at time zero -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The fibre starts at one, so the density starts at the initial density. -/
theorem hillDensity_zero (hm : 0 < m) (hc : Continuous c) (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (ξ : E) :
    hillDensity m c G₀ 0 ξ = G₀ ξ := by
  have hM1 : (1 : ℝ) ≤ max 1 (m ^ 2 + C ^ 2 * ‖ξ‖ ^ 2) := le_max_left _ _
  have hMb : ∀ r, massiveFreq m c ‖ξ‖ r ^ 2 ≤ max 1 (m ^ 2 + C ^ 2 * ‖ξ‖ ^ 2) := fun r =>
    (massiveFreq_sq_le hm hC le_rfl r).trans (le_max_right _ _)
  have hzero := hillSolution_zero (continuous_massiveFreq hc m ‖ξ‖) hM1 hMb (1, 0)
  rw [hillDensity, hzero]
  norm_num

/-- **The field starts at the plain synthesis of its datum.** -/
theorem hillEvolutionField_zero (hm : 0 < m) (hc : Continuous c) (hC : ∀ r, c r ^ 2 ≤ C ^ 2)
    (x : E) : hillEvolutionField m c G₀ 0 x = kgSynthesis G₀ x := by
  rw [hillEvolutionField, kgSynthesis, kgSynthesis]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show kgChar x ξ * hillDensity m c G₀ 0 ξ = kgChar x ξ * G₀ ξ
  rw [hillDensity_zero (C := C) hm hc hC ξ]

end TwoSidedDensity

end GaloisForLFunctions.HTGeometry
