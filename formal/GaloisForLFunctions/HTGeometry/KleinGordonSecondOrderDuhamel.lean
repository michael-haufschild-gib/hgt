import GaloisForLFunctions.HTGeometry.KleinGordonIllPosed

/-!
# The Duhamel term is second order in time

The half-order propagator is bounded by one uniformly in time, and that is what makes the mild theory
work with no regularity at all. It is also bounded by the *elapsed time*: `|sin(τω)/ω| ≤ |τ|`, because
`|sin a| ≤ |a|`. The second bound is worthless for large times and sharp for small ones, and it is the
one that governs how the solution leaves its initial datum.

Feeding it into the Duhamel formula shows that the perturbation contributes only at second order:
the field agrees with the free field to `O(t²)`, not merely to `O(t)`. So a bounded perturbation is
invisible to first order in time — the velocity at `t = 0` is the free one, which the closed formula
of statement 97 already showed, and now the whole first-order behaviour is free.

The multiplier bounds are stated in a reusable form: the operator norm of a Fourier multiplier obeys
*every* bound its symbol obeys, not only the one used to construct it.
-/

noncomputable section

namespace MeasureTheory

open scoped ENNReal

section Rebound

variable {α 𝕜 : Type*} [MeasurableSpace α] [RCLike 𝕜] [SecondCountableTopology 𝕜]
variable {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **A multiplier obeys every bound its symbol obeys**, not only the one it was built with. -/
theorem norm_lpBoundedMulCLM_le_of_bound {φ : α → 𝕜} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖φ x‖ ≤ C) {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ x, ‖φ x‖ ≤ D) :
    ‖lpBoundedMulCLM (p := p) (μ := μ) hφ hC0 hC‖ ≤ D := by
  refine ContinuousLinearMap.opNorm_le_bound _ hD0 fun g => ?_
  refine norm_lpBoundedMulCLM_apply_le_of_ae hφ hC0 hC hD0 g ?_
  filter_upwards with x
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hD x) (norm_nonneg _)

end Rebound

end MeasureTheory

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A Fourier multiplier obeys every bound its symbol obeys.** -/
theorem norm_fourierMulCLM_le_of_bound {φ : E → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ξ, ‖φ ξ‖ ≤ C) {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ ξ, ‖φ ξ‖ ≤ D) :
    ‖fourierMulCLM hφ hC0 hC‖ ≤ D := by
  refine ContinuousLinearMap.opNorm_le_bound _ hD0 fun f => ?_
  rw [fourierMulCLM_apply, norm_fourierL2inv_apply]
  refine le_trans (ContinuousLinearMap.le_of_opNorm_le _
    (norm_lpBoundedMulCLM_le_of_bound (p := 2) (μ := (volume : Measure E)) hφ hC0 hC hD0 hD) _) ?_
  rw [norm_fourierL2_apply]

/-! ## The half-order propagator is bounded by the elapsed time -/

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- `|sin(τ⟨ξ⟩)/⟨ξ⟩| ≤ |τ|`: the half-order symbol is bounded by the elapsed time. -/
theorem norm_kgSinOverFreq_le_abs (τ : ℝ) (ξ : E) : ‖kgSinOverFreq τ ξ‖ ≤ |τ| := by
  have hpos := kgFreq_pos ξ
  rw [kgSinOverFreq, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hpos,
    div_le_iff₀ hpos]
  calc |Real.sin (τ * kgFreq ξ)| ≤ |τ * kgFreq ξ| := Real.abs_sin_le_abs
    _ = |τ| * kgFreq ξ := by rw [abs_mul, abs_of_pos hpos]

/-- **The half-order propagator is bounded by the elapsed time.** -/
theorem norm_kgSinFreqOp_le_abs (τ : ℝ) : ‖kgSinFreqOp (E := E) τ‖ ≤ |τ| := by
  rw [kgSinFreqOp_eq]
  exact norm_fourierMulCLM_le_of_bound _ _ _ (abs_nonneg τ) (norm_kgSinOverFreq_le_abs τ)

theorem norm_kgSinFreqOp_apply_le_abs (τ : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    ‖kgSinFreqOp τ x‖ ≤ |τ| * ‖x‖ :=
  (kgSinFreqOp (E := E) τ).le_of_opNorm_le (norm_kgSinFreqOp_le_abs τ) x

omit [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] in
/-- On the interval between `0` and `t` the elapsed time never exceeds `|t|`. -/
theorem abs_sub_le_abs_of_mem_uIoc_zero {t s : ℝ} (hs : s ∈ Set.uIoc (0 : ℝ) t) :
    |t - s| ≤ |t| := by
  rcases Set.mem_uIoc.mp hs with hs' | hs'
  · have h1 : 0 < s := hs'.1
    have h2 : s ≤ t := hs'.2
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - s), abs_of_nonneg (by linarith : (0 : ℝ) ≤ t)]
    linarith
  · have h1 : t < s := hs'.1
    have h2 : s ≤ 0 := hs'.2
    rw [abs_of_nonpos (by linarith : t - s ≤ 0), abs_of_nonpos (by linarith : t ≤ 0)]
    linarith

/-! ## The perturbation enters at second order -/

section SecondOrder

variable {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- **The perturbation contributes only at second order in time.** The field agrees with the free
field to `O(t²)`, so the whole first-order behaviour of the solution is free. -/
theorem norm_kgFieldMild_sub_free_le_sq (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldMild W f h t - kgFieldFree f h t‖
      ≤ b * ((‖f‖ + ‖h‖) * Real.exp (b * |t|)) * t ^ 2 := by
  have hD0 : (0 : ℝ) ≤ ‖f‖ + ‖h‖ := by positivity
  have hbd : ∀ s ∈ Set.uIoc (0 : ℝ) t,
      ‖kgFieldKernel W t s (kgFieldMild W f h s)‖
        ≤ |t| * (b * ((‖f‖ + ‖h‖) * Real.exp (b * |t|))) := by
    intro s hs
    have habs : |s| ≤ |t| := abs_le_abs_of_mem_uIoc_zero hs
    have hts : |t - s| ≤ |t| := abs_sub_le_abs_of_mem_uIoc_zero hs
    have h1 : ‖kgFieldKernel W t s (kgFieldMild W f h s)‖
        ≤ |t - s| * ‖W (kgFieldMild W f h s)‖ := by
      rw [kgFieldKernel_apply]
      exact norm_kgSinFreqOp_apply_le_abs (t - s) _
    have h2 : ‖W (kgFieldMild W f h s)‖ ≤ b * ‖kgFieldMild W f h s‖ := W.le_of_opNorm_le hW _
    have h3 : ‖kgFieldMild W f h s‖ ≤ (‖f‖ + ‖h‖) * Real.exp (b * |s|) :=
      norm_kgFieldMild_le hb0 hW f h s
    have h4 : Real.exp (b * |s|) ≤ Real.exp (b * |t|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs hb0)
    have h5 : ‖kgFieldMild W f h s‖ ≤ (‖f‖ + ‖h‖) * Real.exp (b * |t|) :=
      h3.trans (mul_le_mul_of_nonneg_left h4 hD0)
    have h6 : ‖W (kgFieldMild W f h s)‖ ≤ b * ((‖f‖ + ‖h‖) * Real.exp (b * |t|)) :=
      h2.trans (mul_le_mul_of_nonneg_left h5 hb0)
    calc ‖kgFieldKernel W t s (kgFieldMild W f h s)‖
        ≤ |t - s| * ‖W (kgFieldMild W f h s)‖ := h1
      _ ≤ |t| * (b * ((‖f‖ + ‖h‖) * Real.exp (b * |t|))) :=
          mul_le_mul hts h6 (norm_nonneg _) (abs_nonneg t)
  have hsub : kgFieldMild W f h t - kgFieldFree f h t
      = ∫ s in (0 : ℝ)..t, kgFieldKernel W t s (kgFieldMild W f h s) := by
    rw [kgFieldMild_eq hb0 hW f h t]
    abel
  rw [hsub]
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  have hrw : |t| * (b * ((‖f‖ + ‖h‖) * Real.exp (b * |t|))) * |t - 0|
      = b * ((‖f‖ + ‖h‖) * Real.exp (b * |t|)) * t ^ 2 := by
    rw [sub_zero, sq_abs t |>.symm]
    ring
  rwa [hrw] at hle

end SecondOrder

section SecondOrderTime

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

/-- **The moving background also contributes only at second order in time.** -/
theorem norm_kgFieldMildT_sub_free_le_sq (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldMildT W f h t - kgFieldFree f h t‖
      ≤ b * ((‖f‖ + ‖h‖) * Real.exp (b * |t|)) * t ^ 2 := by
  have hD0 : (0 : ℝ) ≤ ‖f‖ + ‖h‖ := by positivity
  have hbd : ∀ s ∈ Set.uIoc (0 : ℝ) t,
      ‖kgFieldKernelT W t s (kgFieldMildT W f h s)‖
        ≤ |t| * (b * ((‖f‖ + ‖h‖) * Real.exp (b * |t|))) := by
    intro s hs
    have habs : |s| ≤ |t| := abs_le_abs_of_mem_uIoc_zero hs
    have hts : |t - s| ≤ |t| := abs_sub_le_abs_of_mem_uIoc_zero hs
    have h1 : ‖kgFieldKernelT W t s (kgFieldMildT W f h s)‖
        ≤ |t - s| * ‖W s (kgFieldMildT W f h s)‖ := by
      rw [kgFieldKernelT_apply]
      exact norm_kgSinFreqOp_apply_le_abs (t - s) _
    have h2 : ‖W s (kgFieldMildT W f h s)‖ ≤ b * ‖kgFieldMildT W f h s‖ :=
      (W s).le_of_opNorm_le (hWb s) _
    have h3 : ‖kgFieldMildT W f h s‖ ≤ (‖f‖ + ‖h‖) * Real.exp (b * |s|) :=
      norm_kgFieldMildT_le hb0 hWb hWs f h s
    have h4 : Real.exp (b * |s|) ≤ Real.exp (b * |t|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs hb0)
    have h5 : ‖kgFieldMildT W f h s‖ ≤ (‖f‖ + ‖h‖) * Real.exp (b * |t|) :=
      h3.trans (mul_le_mul_of_nonneg_left h4 hD0)
    have h6 : ‖W s (kgFieldMildT W f h s)‖ ≤ b * ((‖f‖ + ‖h‖) * Real.exp (b * |t|)) :=
      h2.trans (mul_le_mul_of_nonneg_left h5 hb0)
    calc ‖kgFieldKernelT W t s (kgFieldMildT W f h s)‖
        ≤ |t - s| * ‖W s (kgFieldMildT W f h s)‖ := h1
      _ ≤ |t| * (b * ((‖f‖ + ‖h‖) * Real.exp (b * |t|))) :=
          mul_le_mul hts h6 (norm_nonneg _) (abs_nonneg t)
  have hsub : kgFieldMildT W f h t - kgFieldFree f h t
      = ∫ s in (0 : ℝ)..t, kgFieldKernelT W t s (kgFieldMildT W f h s) := by
    rw [kgFieldMildT_eq hb0 hWb hWs f h t]
    abel
  rw [hsub]
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  have hrw : |t| * (b * ((‖f‖ + ‖h‖) * Real.exp (b * |t|))) * |t - 0|
      = b * ((‖f‖ + ‖h‖) * Real.exp (b * |t|)) * t ^ 2 := by
    rw [sub_zero, sq_abs t |>.symm]
    ring
  rwa [hrw] at hle

end SecondOrderTime

end GaloisForLFunctions.HTGeometry
