import GaloisForLFunctions.HTGeometry.HillSynthesisDensity

/-!
# Differentiating the synthesis in time

The field of the evolution is the integral over spatial frequencies of a bounded character times the
frequency density. Differentiating it in time is the parametric-integral theorem, and the estimates
of the previous files supply exactly its hypotheses: the fibre is differentiable in time with
derivative the velocity density, and that velocity density is dominated — uniformly in the time
parameter over a compact interval — by the weight `m + c(0)‖ξ‖` times the initial density.

The character is left arbitrary and merely bounded, so the statement covers the synthesis at every
point of space at once.
-/

namespace GaloisForLFunctions.HTGeometry

open Set MeasureTheory Metric

section Synthesis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {m K C b : ℝ} {c dc : ℝ → ℝ} {G₀ χ : E → ℂ} {μ : Measure E}

/-- The synthesis of the frequency density against a bounded character. -/
noncomputable def hillSynthesis (m : ℝ) (c : ℝ → ℝ) (G₀ χ : E → ℂ) (μ : Measure E) (t : ℝ) : ℂ :=
  ∫ ξ : E, χ ξ * hillDensity m c G₀ t ξ ∂μ

/-- The synthesis of the velocity density. -/
noncomputable def hillSynthesisDeriv (m : ℝ) (c : ℝ → ℝ) (G₀ χ : E → ℂ) (μ : Measure E) (t : ℝ) :
    ℂ :=
  ∫ ξ : E, χ ξ * hillDensityDeriv m c G₀ t ξ ∂μ

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The fibre of the synthesis is differentiable in time, with the velocity density as derivative. -/
theorem hasDerivAt_hillDensity (hm : 0 < m) (hc : Continuous c) (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ))
    (ξ : E) (t : ℝ) :
    HasDerivAt (fun r => χ ξ * hillDensity m c G₀ r ξ)
      (χ ξ * hillDensityDeriv m c G₀ t ξ) t := by
  have hM1 : (1 : ℝ) ≤ max 1 (m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) := le_max_left _ _
  have hMb : ∀ r, massiveFreq m c ‖ξ‖ r ^ (2 : ℕ) ≤ max 1 (m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) := fun r =>
    (massiveFreq_sq_le hm hC le_rfl r).trans (le_max_right _ _)
  have hreal := hasDerivAt_hillSolution (continuous_massiveFreq hc m ‖ξ‖) hM1 hMb (1, 0) t
  have hcx := hreal.ofReal_comp
  exact (hcx.mul_const (G₀ ξ)).const_mul (χ ξ)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **The synthesis is differentiable in time**, with derivative the synthesis of the velocity
density. -/
theorem hasDerivAt_hillSynthesis (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hG : Continuous G₀) (hχ : AEStronglyMeasurable χ μ)
    (hχ1 : ∀ ξ, ‖χ ξ‖ ≤ 1)
    (hint : Integrable (fun ξ : E => ‖G₀ ξ‖) μ)
    (hweight : Integrable (fun ξ : E => (m + c 0 * ‖ξ‖) * ‖G₀ ξ‖) μ)
    {t : ℝ} (ht0 : 0 < t) (htb : t < b) :
    HasDerivAt (hillSynthesis m c G₀ χ μ) (hillSynthesisDeriv m c G₀ χ μ t) t := by
  have hK0 : 0 ≤ K := by
    have h0 : (0 : ℝ) ≤ |dc 0| := abs_nonneg _
    have h1 := hK 0
    have h2 := hcpos 0
    nlinarith
  set ε : ℝ := min t (b - t) with hε
  have hεpos : 0 < ε := lt_min ht0 (by linarith)
  have hsub : ∀ r ∈ ball t ε, 0 ≤ r ∧ r ≤ b := by
    intro r hr
    have hdist : |r - t| < ε := by simpa [Real.dist_eq] using hr
    have h1 : ε ≤ t := min_le_left _ _
    have h2 : ε ≤ b - t := min_le_right _ _
    have hpair := abs_lt.mp hdist
    constructor <;> linarith [hpair.1, hpair.2]
  have hmeas : ∀ᶠ r in nhds t, AEStronglyMeasurable (fun ξ : E => χ ξ * hillDensity m c G₀ r ξ) μ := by
    have hball : ball t ε ∈ nhds t := ball_mem_nhds t hεpos
    filter_upwards [hball] with r hr
    exact hχ.mul (aestronglyMeasurable_hillDensity hm hc hC hG (hsub r hr).1 μ)
  have hFint : Integrable (fun ξ : E => χ ξ * hillDensity m c G₀ t ξ) μ := by
    refine Integrable.mono' (hint.const_mul (max 1 (c 0 / c t) * Real.exp (K * t)))
      (hχ.mul (aestronglyMeasurable_hillDensity hm hc hC hG (le_of_lt ht0) μ)) ?_
    filter_upwards with ξ
    calc ‖χ ξ * hillDensity m c G₀ t ξ‖ = ‖χ ξ‖ * ‖hillDensity m c G₀ t ξ‖ := norm_mul _ _
      _ ≤ 1 * ‖hillDensity m c G₀ t ξ‖ :=
          mul_le_mul_of_nonneg_right (hχ1 ξ) (norm_nonneg _)
      _ = ‖hillDensity m c G₀ t ξ‖ := one_mul _
      _ ≤ (max 1 (c 0 / c t) * Real.exp (K * t)) * ‖G₀ ξ‖ :=
          norm_hillDensity_le hm hc hcd hcpos hK hC (le_of_lt ht0) ξ
  have hF'meas : AEStronglyMeasurable (fun ξ : E => χ ξ * hillDensityDeriv m c G₀ t ξ) μ := by
    have hcont : Continuous fun ξ : E => hillDensityDeriv m c G₀ t ξ := by
      have hfibre : Continuous fun s : ℝ => hillFlow (massiveFreq m c s) (1, 0) t := by
        refine continuous_iff_continuousAt.mpr fun s₀ => ?_
        exact continuousAt_hillFlow_massive (C := C) (t := t) (b := t) hm hc hC (1, 0)
          ⟨le_of_lt ht0, le_rfl⟩ s₀
      have hscalar : Continuous fun s : ℝ => hillSolutionDeriv (massiveFreq m c s) (1, 0) t :=
        continuous_snd.comp hfibre
      exact (Complex.continuous_ofReal.comp (hscalar.comp continuous_norm)).mul hG
    exact hχ.mul hcont.aestronglyMeasurable
  have hbound : ∀ᵐ ξ : E ∂μ, ∀ r ∈ ball t ε,
      ‖χ ξ * hillDensityDeriv m c G₀ r ξ‖ ≤ (m + c 0 * ‖ξ‖) * Real.exp (K * b) * ‖G₀ ξ‖ := by
    filter_upwards with ξ r hr
    have hr0 : 0 ≤ r := (hsub r hr).1
    have hrb : r ≤ b := (hsub r hr).2
    have hexp : Real.exp (K * r) ≤ Real.exp (K * b) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hrb hK0)
    calc ‖χ ξ * hillDensityDeriv m c G₀ r ξ‖ = ‖χ ξ‖ * ‖hillDensityDeriv m c G₀ r ξ‖ := norm_mul _ _
      _ ≤ 1 * ‖hillDensityDeriv m c G₀ r ξ‖ :=
          mul_le_mul_of_nonneg_right (hχ1 ξ) (norm_nonneg _)
      _ = ‖hillDensityDeriv m c G₀ r ξ‖ := one_mul _
      _ ≤ (massiveFreq m c ‖ξ‖ 0 * Real.exp (K * r)) * ‖G₀ ξ‖ :=
          norm_hillDensityDeriv_le hm hc hcd hcpos hK hC hr0 ξ
      _ ≤ ((m + c 0 * ‖ξ‖) * Real.exp (K * b)) * ‖G₀ ξ‖ := by
          have hfreq := massiveFreq_zero_le (c := c) hm hcpos ξ
          have hnn : (0 : ℝ) ≤ ‖G₀ ξ‖ := norm_nonneg _
          have hpos : (0 : ℝ) ≤ Real.exp (K * r) := le_of_lt (Real.exp_pos _)
          have hmf : (0 : ℝ) ≤ massiveFreq m c ‖ξ‖ 0 := le_of_lt (massiveFreq_pos hm c ‖ξ‖ 0)
          have hsum : (0 : ℝ) ≤ m + c 0 * ‖ξ‖ := le_trans hmf hfreq
          have hprod : massiveFreq m c ‖ξ‖ 0 * Real.exp (K * r)
              ≤ (m + c 0 * ‖ξ‖) * Real.exp (K * b) :=
            mul_le_mul hfreq hexp hpos hsum
          exact mul_le_mul_of_nonneg_right hprod hnn
      _ = (m + c 0 * ‖ξ‖) * Real.exp (K * b) * ‖G₀ ξ‖ := by ring
  have hboundInt : Integrable
      (fun ξ : E => (m + c 0 * ‖ξ‖) * Real.exp (K * b) * ‖G₀ ξ‖) μ := by
    have := hweight.const_mul (Real.exp (K * b))
    refine this.congr ?_
    filter_upwards with ξ
    ring
  have hdiff : ∀ᵐ ξ : E ∂μ, ∀ r ∈ ball t ε,
      HasDerivAt (fun s => χ ξ * hillDensity m c G₀ s ξ)
        (χ ξ * hillDensityDeriv m c G₀ r ξ) r := by
    filter_upwards with ξ r _
    exact hasDerivAt_hillDensity hm hc hC ξ r
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun ξ : E =>
      (m + c 0 * ‖ξ‖) * Real.exp (K * b) * ‖G₀ ξ‖)
    (ball_mem_nhds t hεpos) hmeas hFint hF'meas hbound hboundInt hdiff
  exact hmain.2

/-! ## The second derivative -/

/-- The density of the second time derivative: the equation itself, at each frequency. -/
noncomputable def hillDensitySecond (m : ℝ) (c : ℝ → ℝ) (G₀ : E → ℂ) (t : ℝ) (ξ : E) : ℂ :=
  ((-(massiveFreq m c ‖ξ‖ t ^ (2 : ℕ)) * hillSolution (massiveFreq m c ‖ξ‖) (1, 0) t : ℝ) : ℂ) * G₀ ξ

/-- The synthesis of the second-derivative density. -/
noncomputable def hillSynthesisSecond (m : ℝ) (c : ℝ → ℝ) (G₀ χ : E → ℂ) (μ : Measure E)
    (t : ℝ) : ℂ :=
  ∫ ξ : E, χ ξ * hillDensitySecond m c G₀ t ξ ∂μ

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem hasDerivAt_hillDensityDeriv (hm : 0 < m) (hc : Continuous c) (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ))
    (ξ : E) (t : ℝ) :
    HasDerivAt (fun r => χ ξ * hillDensityDeriv m c G₀ r ξ)
      (χ ξ * hillDensitySecond m c G₀ t ξ) t := by
  have hM1 : (1 : ℝ) ≤ max 1 (m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) := le_max_left _ _
  have hMb : ∀ r, massiveFreq m c ‖ξ‖ r ^ (2 : ℕ) ≤ max 1 (m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) := fun r =>
    (massiveFreq_sq_le hm hC le_rfl r).trans (le_max_right _ _)
  have hreal := hasDerivAt_hillSolutionDeriv (continuous_massiveFreq hc m ‖ξ‖) hM1 hMb (1, 0) t
  have hcx := hreal.ofReal_comp
  exact (hcx.mul_const (G₀ ξ)).const_mul (χ ξ)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The second-derivative density costs two powers of the frequency, uniformly on a time interval
where the speed is bounded below. -/
theorem norm_hillDensitySecond_le {cmin : ℝ} (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (hK0 : 0 ≤ K)
    {t : ℝ} (ht : 0 ≤ t) (htb : t ≤ b) (ξ : E) :
    ‖hillDensitySecond m c G₀ t ξ‖ ≤
      ((m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) * (max 1 (c 0 / cmin) * Real.exp (K * b))) * ‖G₀ ξ‖ := by
  have hfib := abs_hillSolutionSecond_massive_cos_le (S := ‖ξ‖) (t := t) (b := t) hm hc hcd hcpos
    hK hC le_rfl ⟨ht, le_rfl⟩
  have hval : ‖hillDensitySecond m c G₀ t ξ‖
      = |(-(massiveFreq m c ‖ξ‖ t ^ (2 : ℕ))) * hillSolution (massiveFreq m c ‖ξ‖) (1, 0) t| *
          ‖G₀ ξ‖ := by
    rw [hillDensitySecond, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hval]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine hfib.trans ?_
  have hratio : max 1 (c 0 / c t) ≤ max 1 (c 0 / cmin) := by
    refine max_le_max le_rfl ?_
    exact div_le_div_of_nonneg_left (le_of_lt (hcpos 0)) hcmin (hclow t)
  have hexp : Real.exp (K * t) ≤ Real.exp (K * b) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htb hK0)
  have hfreq : massiveFreq m c ‖ξ‖ t ^ (2 : ℕ) ≤ m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ) :=
    massiveFreq_sq_le hm hC le_rfl t
  have hsq : (0 : ℝ) ≤ massiveFreq m c ‖ξ‖ t ^ (2 : ℕ) := sq_nonneg _
  have hR : (0 : ℝ) ≤ max 1 (c 0 / c t) := le_trans zero_le_one (le_max_left _ _)
  have hE : (0 : ℝ) ≤ Real.exp (K * t) := le_of_lt (Real.exp_pos _)
  have hstep : max 1 (c 0 / c t) * Real.exp (K * t)
      ≤ max 1 (c 0 / cmin) * Real.exp (K * b) := mul_le_mul hratio hexp hE
        (le_trans zero_le_one (le_max_left _ _))
  exact mul_le_mul hfreq hstep (mul_nonneg hR hE) (by positivity)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **The velocity synthesis is differentiable in time**, with derivative the synthesis of the
second-derivative density. -/
theorem hasDerivAt_hillSynthesisDeriv {cmin : ℝ} (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r)
    (hG : Continuous G₀) (hχ : AEStronglyMeasurable χ μ) (hχ1 : ∀ ξ, ‖χ ξ‖ ≤ 1)
    (hweight : Integrable (fun ξ : E => (m + c 0 * ‖ξ‖) * ‖G₀ ξ‖) μ)
    (hweight2 : Integrable (fun ξ : E => (m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) * ‖G₀ ξ‖) μ)
    {t : ℝ} (ht0 : 0 < t) (htb : t < b) :
    HasDerivAt (hillSynthesisDeriv m c G₀ χ μ) (hillSynthesisSecond m c G₀ χ μ t) t := by
  have hK0 : 0 ≤ K := by
    have h0 : (0 : ℝ) ≤ |dc 0| := abs_nonneg _
    have h1 := hK 0
    have h2 := hcpos 0
    nlinarith
  set ε : ℝ := min t (b - t) with hε
  have hεpos : 0 < ε := lt_min ht0 (by linarith)
  have hsub : ∀ r ∈ ball t ε, 0 ≤ r ∧ r ≤ b := by
    intro r hr
    have hdist : |r - t| < ε := by simpa [Real.dist_eq] using hr
    have h1 : ε ≤ t := min_le_left _ _
    have h2 : ε ≤ b - t := min_le_right _ _
    have hpair := abs_lt.mp hdist
    constructor <;> linarith [hpair.1, hpair.2]
  have hcontDeriv : ∀ r : ℝ, 0 ≤ r → Continuous fun ξ : E => hillDensityDeriv m c G₀ r ξ := by
    intro r hr
    have hfibre : Continuous fun s : ℝ => hillFlow (massiveFreq m c s) (1, 0) r := by
      refine continuous_iff_continuousAt.mpr fun s₀ => ?_
      exact continuousAt_hillFlow_massive (C := C) (t := r) (b := r) hm hc hC (1, 0)
        ⟨hr, le_rfl⟩ s₀
    have hscalar : Continuous fun s : ℝ => hillSolutionDeriv (massiveFreq m c s) (1, 0) r :=
      continuous_snd.comp hfibre
    exact (Complex.continuous_ofReal.comp (hscalar.comp continuous_norm)).mul hG
  have hmeas : ∀ᶠ r in nhds t,
      AEStronglyMeasurable (fun ξ : E => χ ξ * hillDensityDeriv m c G₀ r ξ) μ := by
    filter_upwards [ball_mem_nhds t hεpos] with r hr
    exact hχ.mul (hcontDeriv r (hsub r hr).1).aestronglyMeasurable
  have hFint : Integrable (fun ξ : E => χ ξ * hillDensityDeriv m c G₀ t ξ) μ := by
    refine Integrable.mono' (hweight.const_mul (Real.exp (K * t)))
      (hχ.mul (hcontDeriv t (le_of_lt ht0)).aestronglyMeasurable) ?_
    filter_upwards with ξ
    have hbase := norm_hillDensityDeriv_le (G₀ := G₀) hm hc hcd hcpos hK hC (le_of_lt ht0) ξ
    have hfreq := massiveFreq_zero_le (c := c) hm hcpos ξ
    have hE : (0 : ℝ) ≤ Real.exp (K * t) := le_of_lt (Real.exp_pos _)
    have hG0 : (0 : ℝ) ≤ ‖G₀ ξ‖ := norm_nonneg _
    calc ‖χ ξ * hillDensityDeriv m c G₀ t ξ‖ ≤ 1 * ‖hillDensityDeriv m c G₀ t ξ‖ := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hχ1 ξ) (norm_nonneg _)
      _ = ‖hillDensityDeriv m c G₀ t ξ‖ := one_mul _
      _ ≤ (massiveFreq m c ‖ξ‖ 0 * Real.exp (K * t)) * ‖G₀ ξ‖ := hbase
      _ ≤ Real.exp (K * t) * ((m + c 0 * ‖ξ‖) * ‖G₀ ξ‖) := by
          have h1 : massiveFreq m c ‖ξ‖ 0 * Real.exp (K * t)
              ≤ (m + c 0 * ‖ξ‖) * Real.exp (K * t) := mul_le_mul_of_nonneg_right hfreq hE
          have h2 := mul_le_mul_of_nonneg_right h1 hG0
          calc (massiveFreq m c ‖ξ‖ 0 * Real.exp (K * t)) * ‖G₀ ξ‖
              ≤ ((m + c 0 * ‖ξ‖) * Real.exp (K * t)) * ‖G₀ ξ‖ := h2
            _ = Real.exp (K * t) * ((m + c 0 * ‖ξ‖) * ‖G₀ ξ‖) := by ring
  have hF'meas : AEStronglyMeasurable (fun ξ : E => χ ξ * hillDensitySecond m c G₀ t ξ) μ := by
    have hfibre : Continuous fun s : ℝ => hillFlow (massiveFreq m c s) (1, 0) t := by
      refine continuous_iff_continuousAt.mpr fun s₀ => ?_
      exact continuousAt_hillFlow_massive (C := C) (t := t) (b := t) hm hc hC (1, 0)
        ⟨le_of_lt ht0, le_rfl⟩ s₀
    have hscalar : Continuous fun s : ℝ => hillSolution (massiveFreq m c s) (1, 0) t :=
      continuous_fst.comp hfibre
    have hfreqs : Continuous fun s : ℝ => massiveFreq m c s t := by
      show Continuous fun s : ℝ => Real.sqrt (m ^ (2 : ℕ) + (c t * s) ^ (2 : ℕ))
      exact Real.continuous_sqrt.comp
        (continuous_const.add ((continuous_const.mul continuous_id).pow 2))
    have hfreqcont : Continuous fun ξ : E => massiveFreq m c ‖ξ‖ t :=
      hfreqs.comp continuous_norm
    have hcont : Continuous fun ξ : E => hillDensitySecond m c G₀ t ξ := by
      have hprod : Continuous fun ξ : E =>
          (-(massiveFreq m c ‖ξ‖ t ^ (2 : ℕ)) * hillSolution (massiveFreq m c ‖ξ‖) (1, 0) t : ℝ) :=
        ((hfreqcont.pow 2).neg).mul (hscalar.comp continuous_norm)
      exact (Complex.continuous_ofReal.comp hprod).mul hG
    exact hχ.mul hcont.aestronglyMeasurable
  have hbound : ∀ᵐ ξ : E ∂μ, ∀ r ∈ ball t ε,
      ‖χ ξ * hillDensitySecond m c G₀ r ξ‖ ≤
        ((m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) * (max 1 (c 0 / cmin) * Real.exp (K * b))) * ‖G₀ ξ‖ := by
    filter_upwards with ξ r hr
    calc ‖χ ξ * hillDensitySecond m c G₀ r ξ‖ ≤ 1 * ‖hillDensitySecond m c G₀ r ξ‖ := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hχ1 ξ) (norm_nonneg _)
      _ = ‖hillDensitySecond m c G₀ r ξ‖ := one_mul _
      _ ≤ _ := norm_hillDensitySecond_le hm hc hcd hcpos hK hC hcmin hclow hK0
          (hsub r hr).1 (hsub r hr).2 ξ
  have hboundInt : Integrable (fun ξ : E =>
      ((m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) * (max 1 (c 0 / cmin) * Real.exp (K * b))) * ‖G₀ ξ‖) μ := by
    have := hweight2.const_mul (max 1 (c 0 / cmin) * Real.exp (K * b))
    refine this.congr ?_
    filter_upwards with ξ
    ring
  have hdiff : ∀ᵐ ξ : E ∂μ, ∀ r ∈ ball t ε,
      HasDerivAt (fun s => χ ξ * hillDensityDeriv m c G₀ s ξ)
        (χ ξ * hillDensitySecond m c G₀ r ξ) r := by
    filter_upwards with ξ r _
    exact hasDerivAt_hillDensityDeriv hm hc hC ξ r
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun ξ : E =>
      ((m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) * (max 1 (c 0 / cmin) * Real.exp (K * b))) * ‖G₀ ξ‖)
    (ball_mem_nhds t hεpos) hmeas hFint hF'meas hbound hboundInt hdiff
  exact hmain.2

end Synthesis

end GaloisForLFunctions.HTGeometry
