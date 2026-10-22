import GaloisForLFunctions.HTGeometry.ResolventSubordination
import GaloisForLFunctions.HTGeometry.CarlemanOperatorBound

/-!
# The cutoff commutator of the logarithmic symbol is a Carleman cross block

Cutting a kernel operator to an interval leaves exactly the kernel weighted by the difference of
the two indicators:

`[K, P](x, y) = K(x, y) (1_I(y) - 1_I(x))`,

so the defect is supported on the two crossing regions, one at each endpoint.  For the logarithmic
symbol the kernel is obtained by superposing the resolvent kernels in the subordination parameter:

`(1/2) ∫₀^∞ e^{-√(1+λ)|x-y|} / (2√(1+λ)) dλ = e^{-|x-y|} / (2|x-y|)`,

while the symbols superpose to `log √(1+4π²ξ²)`.  Writing the crossing region at an endpoint as
`x = a - s`, `y = a + t` with `s, t > 0` gives `|x - y| = s + t`, so the cross kernel is the
Carleman kernel `1/(s+t)` times `e^{-(s+t)}/2 ≤ 1/2`.  Schur's test then bounds the cross block on
`L²` by `π/2`.
-/

open Set MeasureTheory Filter Topology
open scoped FourierTransform Convolution

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The two kernels -/

/-- The resolvent kernel of `(μ² - Δ)⁻¹` on the line. -/
def resolventKernel (μ x y : ℝ) : ℝ := Real.exp (-(μ * |x - y|)) / (2 * μ)

/-- The off-diagonal kernel of the logarithmic symbol. -/
def logSymbolKernel (x y : ℝ) : ℝ := Real.exp (-|x - y|) / (2 * |x - y|)

/-- **The resolvent symbol is the Fourier transform of the resolvent kernel.** -/
theorem fourierIntegral_resolventKernel {μ : ℝ} (hμ : 0 < μ) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (resolventKernel μ x 0 : ℂ)) ξ
      = 1 / ((μ:ℂ) ^ 2 + 4 * (Real.pi : ℂ) ^ 2 * (ξ:ℂ) ^ 2) := by
  have hbase := fourierIntegral_exp_neg_mul_abs hμ ξ
  have hfun : (fun x : ℝ => (resolventKernel μ x 0 : ℂ))
      = fun x : ℝ => ((2 * (μ:ℂ))⁻¹) • (Real.exp (-(μ * |x|)) : ℂ) := by
    funext x
    rw [resolventKernel, sub_zero, smul_eq_mul]
    rw [Complex.ofReal_div, Complex.ofReal_mul]
    push_cast
    rw [div_eq_inv_mul]
  have hmuc : (2 * (μ:ℂ)) ≠ 0 := by
    have : (μ:ℂ) ≠ 0 := by
      simpa using ne_of_gt hμ
    simpa using this
  have hsmul : 𝓕 (fun x : ℝ => ((2 * (μ:ℂ))⁻¹) • (Real.exp (-(μ * |x|)) : ℂ)) ξ
      = ((2 * (μ:ℂ))⁻¹) • 𝓕 (fun x : ℝ => (Real.exp (-(μ * |x|)) : ℂ)) ξ := by
    rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
      ← MeasureTheory.integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    show Complex.exp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I)
        • ((2 * (μ:ℂ))⁻¹ • (Real.exp (-(μ * |v|)) : ℂ))
      = (2 * (μ:ℂ))⁻¹ • (Complex.exp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I)
        • (Real.exp (-(μ * |v|)) : ℂ))
    rw [smul_comm]
  have hμc0 : (μ:ℂ) ≠ 0 := by
    simpa using ne_of_gt hμ
  rw [hfun, hsmul, hbase, smul_eq_mul]
  field_simp

/-- The resolvent kernel is integrable. -/
theorem integrable_resolventKernel {μ : ℝ} (hμ : 0 < μ) :
    Integrable (fun x : ℝ => (resolventKernel μ x 0 : ℂ)) volume := by
  have hbase : Integrable (fun x : ℝ => Real.exp (-μ * |x|)) volume := by
    have h := HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 hμ
    simpa using h
  have hscaled : Integrable (fun x : ℝ => (2 * μ)⁻¹ * Real.exp (-μ * |x|)) volume :=
    hbase.const_mul _
  have hcongr : (fun x : ℝ => (resolventKernel μ x 0 : ℂ))
      = fun x : ℝ => (((2 * μ)⁻¹ * Real.exp (-μ * |x|) : ℝ) : ℂ) := by
    funext x
    rw [resolventKernel, sub_zero]
    norm_cast
    rw [div_eq_inv_mul]
    congr 2
    ring
  rw [hcongr]
  exact hscaled.ofReal

/-- **The resolvent operator is convolution by the resolvent kernel**, with the resolvent symbol
as its Fourier multiplier. -/
theorem fourier_resolventConvolution {μ : ℝ} (hμ : 0 < μ) {f : ℝ → ℂ} (hf : Integrable f)
    (ξ : ℝ) :
    𝓕 ((fun x : ℝ => (resolventKernel μ x 0 : ℂ))
        ⋆[ContinuousLinearMap.mul ℂ ℂ] f) ξ
      = (1 / ((μ:ℂ) ^ 2 + 4 * (Real.pi : ℂ) ^ 2 * (ξ:ℂ) ^ 2)) * 𝓕 f ξ := by
  rw [Real.fourier_mul_convolution_eq (integrable_resolventKernel hμ) hf ξ,
    fourierIntegral_resolventKernel hμ ξ]

/-! ## Superposition in the subordination parameter -/

/-- **The kernels superpose to the logarithmic kernel.** -/
theorem integral_Ioi_resolventKernel {x y : ℝ} (hxy : x ≠ y) :
    (1 / 2) * (∫ l in Ioi (0:ℝ), resolventKernel (Real.sqrt (1 + l)) x y)
      = logSymbolKernel x y := by
  have hr : 0 < |x - y| := by
    have : x - y ≠ 0 := sub_ne_zero.mpr hxy
    exact abs_pos.mpr this
  have hderiv : ∀ μ ∈ Ioi (1:ℝ), HasDerivWithinAt (fun t : ℝ => t ^ 2 - 1) (2 * μ) (Ioi (1:ℝ)) μ := by
    intro μ _
    have h : HasDerivAt (fun t : ℝ => t ^ 2 - 1) (2 * μ ^ 1) μ := by
      simpa using (hasDerivAt_pow 2 μ).sub_const 1
    rw [pow_one] at h
    exact h.hasDerivWithinAt
  have hinj : InjOn (fun t : ℝ => t ^ 2 - 1) (Ioi (1:ℝ)) := by
    intro a ha b hb hab
    have ha1 : (1:ℝ) < a := ha
    have hb1 : (1:ℝ) < b := hb
    have hab' : a ^ 2 - 1 = b ^ 2 - 1 := hab
    have hsq : a ^ 2 = b ^ 2 := by linarith
    nlinarith
  have himage : (fun t : ℝ => t ^ 2 - 1) '' Ioi (1:ℝ) = Ioi (0:ℝ) := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht1 : (1:ℝ) < t := ht
      show (0:ℝ) < t ^ 2 - 1
      nlinarith
    · intro hz
      have hz0 : (0:ℝ) < z := hz
      refine ⟨Real.sqrt (1 + z), ?_, ?_⟩
      · show (1:ℝ) < Real.sqrt (1 + z)
        have h1 : Real.sqrt 1 < Real.sqrt (1 + z) := by
          apply Real.sqrt_lt_sqrt (by norm_num)
          linarith
        rwa [Real.sqrt_one] at h1
      · show Real.sqrt (1 + z) ^ 2 - 1 = z
        rw [Real.sq_sqrt (by linarith)]
        ring
  have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun l => resolventKernel (Real.sqrt (1 + l)) x y)
  rw [himage] at hsub
  have hpoint : ∀ μ ∈ Ioi (1:ℝ),
      |2 * μ| • resolventKernel (Real.sqrt (1 + (μ ^ 2 - 1))) x y
        = Real.exp (-(μ * |x - y|)) := by
    intro μ hμ
    have hμ1 : (1:ℝ) < μ := hμ
    have hμ0 : (0:ℝ) < μ := by linarith
    have hsimp : Real.sqrt (1 + (μ ^ 2 - 1)) = μ := by
      rw [show 1 + (μ ^ 2 - 1) = μ ^ 2 by ring, Real.sqrt_sq hμ0.le]
    rw [hsimp, resolventKernel, smul_eq_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * μ)]
    field_simp
  rw [hsub, setIntegral_congr_fun measurableSet_Ioi hpoint,
    integral_Ioi_exp_neg_mul_right hr, logSymbolKernel]
  field_simp

/-- **The symbols superpose to the logarithmic symbol.** -/
theorem logSymbol_eq_integral (ξ : ℝ) :
    Real.log (Real.sqrt (1 + 4 * Real.pi ^ 2 * ξ ^ 2))
      = (1 / 2) * ∫ l in Ioi (0:ℝ),
          ((1 + l)⁻¹ - (1 + l + 4 * Real.pi ^ 2 * ξ ^ 2)⁻¹) := by
  have hz : (0:ℝ) ≤ 4 * Real.pi ^ 2 * ξ ^ 2 := by positivity
  rw [integral_Ioi_resolvent_diff hz, Real.log_sqrt (by linarith)]
  ring

/-! ## The cutoff commutator -/

/-- **The cutoff commutator of a kernel operator has the crossing kernel.**  Cutting the profile
and cutting the response differ by the kernel weighted with `1_I(y) - 1_I(x)`. -/
theorem kernel_cutoff_commutator (K : ℝ → ℝ → ℝ) (I : Set ℝ) (hI : MeasurableSet I) (f : ℝ → ℝ)
    (x : ℝ) (hint : Integrable (fun y => K x y * f y) volume) :
    (∫ y : ℝ, K x y * I.indicator f y)
        - I.indicator (fun _ => (1:ℝ)) x * ∫ y : ℝ, K x y * f y
      = ∫ y : ℝ, K x y * ((I.indicator (fun _ => (1:ℝ)) y
          - I.indicator (fun _ => (1:ℝ)) x) * f y) := by
  classical
  have hcut : Integrable (fun y => K x y * I.indicator f y) volume := by
    have h := hint.indicator hI
    refine h.congr (Filter.Eventually.of_forall fun y => ?_)
    show I.indicator (fun y => K x y * f y) y = K x y * I.indicator f y
    by_cases hy : y ∈ I
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
  rw [← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_sub hcut (hint.const_mul (I.indicator (fun _ => (1:ℝ)) x))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show K x y * I.indicator f y - I.indicator (fun _ => (1:ℝ)) x * (K x y * f y)
    = K x y * ((I.indicator (fun _ => (1:ℝ)) y - I.indicator (fun _ => (1:ℝ)) x) * f y)
  by_cases hy : y ∈ I
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    ring
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
    ring

/-! ## The crossing region at an endpoint -/

/-- **The crossing kernel at an endpoint is Carleman dominated.** -/
theorem logSymbolKernel_cross_le (a : ℝ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    logSymbolKernel (a - s) (a + t) ≤ 1 / 2 * (1 / (s + t)) := by
  have hdiff : (a - s) - (a + t) = -(s + t) := by ring
  have habs : |(a - s) - (a + t)| = s + t := by
    rw [hdiff, abs_neg, abs_of_pos (by linarith)]
  have hexp : Real.exp (-(s + t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hst : (0:ℝ) < s + t := by linarith
  rw [logSymbolKernel, habs, div_le_iff₀ (by positivity)]
  have hprod : 1 / 2 * (1 / (s + t)) * (2 * (s + t)) = 1 := by
    field_simp
  rw [hprod]
  exact hexp

/-- **`(26)`: the logarithmic cutoff defect is bounded on `L²`.**  Schur's test for the Carleman
kernel gives the endpoint cross block an operator norm at most `π/2`. -/
theorem lintegral_sq_logSymbolCross_le (a : ℝ) {F : ℝ → ENNReal} (hF : Measurable F) :
    (∫⁻ s in Ioi (0:ℝ),
        (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (logSymbolKernel (a - s) (a + t)) * F t) ^ 2)
      ≤ ENNReal.ofReal (Real.pi ^ 2) * ∫⁻ t in Ioi (0:ℝ), F t ^ 2 := by
  have hmono : ∀ s ∈ Ioi (0:ℝ),
      (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (logSymbolKernel (a - s) (a + t)) * F t) ^ 2
        ≤ (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (s + t)) * F t) ^ 2 := by
    intro s hs
    have hs0 : (0:ℝ) < s := hs
    refine pow_le_pow_left' (lintegral_mono_ae ?_) 2
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0:ℝ) < t := ht
    have hle : logSymbolKernel (a - s) (a + t) ≤ 1 / (s + t) := by
      have h := logSymbolKernel_cross_le a hs0 ht0
      have hpos : (0:ℝ) < 1 / (s + t) := by positivity
      nlinarith
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hle) (le_refl (F t))
  calc (∫⁻ s in Ioi (0:ℝ),
        (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (logSymbolKernel (a - s) (a + t)) * F t) ^ 2)
      ≤ ∫⁻ s in Ioi (0:ℝ), (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (s + t)) * F t) ^ 2 := by
        refine setLIntegral_mono' measurableSet_Ioi hmono
    _ ≤ ENNReal.ofReal (Real.pi ^ 2) * ∫⁻ t in Ioi (0:ℝ), F t ^ 2 := lintegral_carleman_sq_le hF

end

end RHTower
