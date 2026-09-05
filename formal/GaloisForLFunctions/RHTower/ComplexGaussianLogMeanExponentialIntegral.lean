import GaloisForLFunctions.RHTower.RiemannSiegelPhaseTorusLogMean
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# The complex-Gaussian logarithmic mean of `|1 + W|²` is the exponential integral

If the mollified deviation `W = ζΨ − 1` on the critical line had the complex Gaussian law
`CN(0, σ²)` (the law conjectured for it, with `σ² = 1/θ` for a mollifier of length `T^θ`), then the
logarithmic mean of the mollified product would be

```text
E log|1 + W|² = E₁(1/σ²),      E₁(x) = ∫_x^∞ e^{-u}/u du.
```

In polar coordinates the Gaussian expectation is the radial integral of `(2r/σ²) e^{-r²/σ²}` against
the circle average of `log|1 + z|²` at radius `r`, and by Jensen's mean-value identity that circle
average is `2 log max(r, 1)`.  The remaining one-dimensional integral is evaluated exactly by one
integration by parts and the substitution `u = r²/σ²`.

This is the exact prediction of the Gaussian law for the `(L)` ceiling on the logarithmic mean of
`|ζ|` on the line: `½ E₁(θ)` in place of the Jensen ceiling `½ log(1 + 1/θ)`.  It is a model
computation; no statement about `ζ` is made here.
-/

open Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The exponential integral `E₁(x) = ∫_x^∞ e^{-u}/u du`. -/
def expIntegralE1 (x : ℝ) : ℝ := ∫ u in Ioi x, Real.exp (-u) / u

/-- Radial (polar-coordinate) form of `E log|1 + W|²` for `W ~ CN(0, σ²)`: the Gaussian density
`(1/(πσ²)) e^{-|w|²/σ²}` in polar coordinates is `(2r/σ²) e^{-r²/σ²} dr · (dφ/2π)`, so the
expectation is the radial integral of `(2r/σ²) e^{-r²/σ²}` against the circle average of
`log|1 + z|² = 2 log|1 + z|` at radius `r`. -/
def complexGaussianLogMeanRadial (σ : ℝ) : ℝ :=
  ∫ r in Ioi (0 : ℝ), (2 * r / σ ^ 2) * Real.exp (-(r ^ 2) / σ ^ 2) *
    (2 * Real.circleAverage (fun z : ℂ => Real.log ‖(1 : ℂ) + z‖) 0 r)

/-! ## Monomial–exponential integrability -/

private theorem integrableOn_pow_mul_exp_neg_mul_Ioi' {r : ℝ} (hr : 0 < r) (j : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ j * Real.exp (-(r * t))) (Ioi (0:ℝ)) := by
  have hG : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (((j : ℝ) + 1) - 1)) (Ioi (0:ℝ)) :=
    Real.GammaIntegral_convergent (by positivity)
  have hscale := (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => Real.exp (-x) * x ^ (((j : ℝ) + 1) - 1)) 0 hr).mpr (by simpa using hG)
  have hc : IntegrableOn
      (fun x : ℝ => (r ^ j)⁻¹ * (Real.exp (-(r * x)) * (r * x) ^ (((j : ℝ) + 1) - 1)))
      (Ioi (0:ℝ)) := hscale.const_mul _
  refine MeasureTheory.IntegrableOn.congr_fun hc ?_ measurableSet_Ioi
  intro x hx
  have hx0 : (0:ℝ) < x := hx
  have hrj : (r : ℝ) ^ j ≠ 0 := by positivity
  have hexp : ((r * x) : ℝ) ^ (((j : ℝ) + 1) - 1) = r ^ j * x ^ j := by
    rw [show ((j : ℝ) + 1) - 1 = (j : ℝ) by ring, Real.rpow_natCast, mul_pow]
  simp only [hexp]
  field_simp

/-! ## The Gaussian log-mean identity -/

/-- **Complex-Gaussian logarithmic mean.**  `E log|1 + W|² = E₁(1/σ²)` for `W ~ CN(0, σ²)`, in
radial form. -/
theorem complexGaussianLogMeanRadial_eq_expIntegralE1 {σ : ℝ} (hσ : 0 < σ) :
    complexGaussianLogMeanRadial σ = expIntegralE1 (1 / σ ^ 2) := by
  have hσ2 : 0 < σ ^ 2 := by positivity
  set c : ℝ := 1 / σ ^ 2 with hc
  have hcpos : 0 < c := by positivity
  have hexpc : ∀ r : ℝ, Real.exp (-(c * r ^ 2)) = Real.exp (-(r ^ 2) / σ ^ 2) := by
    intro r
    congr 1
    rw [hc]
    ring
  -- ## Step 1: the circle average is `log (max r 1)`
  have hcirc : ∀ r : ℝ, 0 < r →
      Real.circleAverage (fun z : ℂ => Real.log ‖(1 : ℂ) + z‖) 0 r = Real.log (max r 1) := by
    intro r hr
    have h := circleAverage_log_norm_const_add (1 : ℂ) hr
    simpa using h
  -- ## Step 2: the integrand is supported on `r > 1`
  have hint : (fun r : ℝ => (2 * r / σ ^ 2) * Real.exp (-(r ^ 2) / σ ^ 2) *
        (2 * Real.circleAverage (fun z : ℂ => Real.log ‖(1 : ℂ) + z‖) 0 r))
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (Ioi (1 : ℝ)).indicator
          (fun r => (4 * r / σ ^ 2) * Real.exp (-(r ^ 2) / σ ^ 2) * Real.log r) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    refine Filter.Eventually.of_forall (fun r hr => ?_)
    dsimp only
    rw [hcirc r hr]
    by_cases h1 : r ∈ Ioi (1 : ℝ)
    · rw [Set.indicator_of_mem h1, max_eq_left (le_of_lt h1)]
      ring
    · rw [Set.indicator_of_notMem h1, max_eq_right (not_lt.mp h1), Real.log_one]
      ring
  unfold complexGaussianLogMeanRadial
  rw [integral_congr_ae hint, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Set.Ioi_inter_Ioi,
    max_eq_left (by norm_num : (0 : ℝ) ≤ 1)]
  -- ## Step 3: integration by parts on `(1, ∞)`
  set F : ℝ → ℝ := fun r => -2 * (Real.exp (-(r ^ 2) / σ ^ 2) * Real.log r) with hF
  have hexpderiv : ∀ r : ℝ, HasDerivAt (fun r : ℝ => Real.exp (-(r ^ 2) / σ ^ 2))
      (Real.exp (-(r ^ 2) / σ ^ 2) * (-(2 * r) / σ ^ 2)) r := by
    intro r
    have h1 : HasDerivAt (fun r : ℝ => -(r ^ 2) / σ ^ 2) (-(2 * r) / σ ^ 2) r := by
      have := ((hasDerivAt_pow 2 r).neg).div_const (σ ^ 2)
      simpa using this
    exact h1.exp
  have hFderiv : ∀ r ∈ Ioi (1 : ℝ), HasDerivAt F
      ((4 * r / σ ^ 2) * Real.exp (-(r ^ 2) / σ ^ 2) * Real.log r
        - 2 * Real.exp (-(r ^ 2) / σ ^ 2) / r) r := by
    intro r hr
    have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
    have hl : HasDerivAt Real.log r⁻¹ r := Real.hasDerivAt_log hr0.ne'
    have h := ((hexpderiv r).mul hl).const_mul (-2)
    exact h.congr_deriv (by ring)
  -- integrability of the two pieces on `(1, ∞)`
  have hmono : ∀ r : ℝ, 1 ≤ r → -(r ^ 2) / σ ^ 2 ≤ -(c * r) := by
    intro r hr
    rw [hc]
    have h1 : r ≤ r ^ 2 := by
      rw [sq]
      exact le_mul_of_one_le_right (by linarith) hr
    calc -(r ^ 2) / σ ^ 2 ≤ -r / σ ^ 2 := by
          exact div_le_div_of_nonneg_right (by linarith) hσ2.le
      _ = -(1 / σ ^ 2 * r) := by ring
  have hlogle : ∀ r : ℝ, 1 ≤ r → Real.log r ≤ r := by
    intro r hr
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < r)
    linarith
  have hcont1 : ContinuousOn (fun r : ℝ => (4 * r / σ ^ 2) * Real.exp (-(r ^ 2) / σ ^ 2) * Real.log r)
      (Ioi 1) := by
    apply ContinuousOn.mul
    · exact (Continuous.continuousOn (by fun_prop))
    · exact Real.continuousOn_log.mono (fun r hr => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact (lt_trans zero_lt_one hr).ne')
  have hcont2 : ContinuousOn (fun r : ℝ => 2 * Real.exp (-(r ^ 2) / σ ^ 2) / r) (Ioi 1) := by
    apply ContinuousOn.div (Continuous.continuousOn (by fun_prop)) continuousOn_id
    intro r hr
    exact (lt_trans zero_lt_one hr).ne'
  have hI1 : IntegrableOn
      (fun r : ℝ => (4 * r / σ ^ 2) * Real.exp (-(r ^ 2) / σ ^ 2) * Real.log r) (Ioi 1) := by
    have hmaj : IntegrableOn (fun r : ℝ => (4 / σ ^ 2) * (r ^ 2 * Real.exp (-(c * r)))) (Ioi 1) :=
      ((integrableOn_pow_mul_exp_neg_mul_Ioi' hcpos 2).mono_set
        (Set.Ioi_subset_Ioi zero_le_one)).const_mul _
    refine hmaj.mono' (hcont1.aestronglyMeasurable measurableSet_Ioi) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun r hr => ?_)
    have hr1 : (1 : ℝ) ≤ r := le_of_lt hr
    have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
    have hlog0 : 0 ≤ Real.log r := Real.log_nonneg hr1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (4 * r / σ ^ 2) * Real.exp (-(r ^ 2) / σ ^ 2) * Real.log r
        ≤ (4 * r / σ ^ 2) * Real.exp (-(c * r)) * r := by
          gcongr
          · exact hmono r hr1
          · exact hlogle r hr1
      _ = (4 / σ ^ 2) * (r ^ 2 * Real.exp (-(c * r))) := by ring
  have hI2 : IntegrableOn (fun r : ℝ => 2 * Real.exp (-(r ^ 2) / σ ^ 2) / r) (Ioi 1) := by
    have hmaj : IntegrableOn (fun r : ℝ => 2 * Real.exp (-c * r)) (Ioi 1) :=
      (exp_neg_integrableOn_Ioi 1 hcpos).const_mul _
    refine hmaj.mono' (hcont2.aestronglyMeasurable measurableSet_Ioi) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun r hr => ?_)
    have hr1 : (1 : ℝ) ≤ r := le_of_lt hr
    have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc 2 * Real.exp (-(r ^ 2) / σ ^ 2) / r ≤ 2 * Real.exp (-(c * r)) / 1 := by
          gcongr
          exact hmono r hr1
      _ = 2 * Real.exp (-c * r) := by ring_nf
  have hI3 : IntegrableOn (fun r : ℝ =>
      (4 * r / σ ^ 2) * Real.exp (-(r ^ 2) / σ ^ 2) * Real.log r
        - 2 * Real.exp (-(r ^ 2) / σ ^ 2) / r) (Ioi 1) := hI1.sub hI2
  -- boundary behaviour of `F`
  have hFcont : ContinuousWithinAt F (Ici 1) 1 := by
    apply ContinuousAt.continuousWithinAt
    exact continuousAt_const.mul
      ((Continuous.continuousAt (by fun_prop)).mul (Real.continuousAt_log one_ne_zero))
  have hFtend : Tendsto F atTop (𝓝 0) := by
    have hpow : Tendsto (fun r : ℝ => (c * r) ^ 1 * Real.exp (-(c * r))) atTop (𝓝 0) :=
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
        (tendsto_id.const_mul_atTop hcpos)
    have hpow' : Tendsto (fun r : ℝ => (2 / c) * ((c * r) ^ 1 * Real.exp (-(c * r)))) atTop (𝓝 0) := by
      simpa using hpow.const_mul (2 / c)
    refine squeeze_zero_norm' ?_ hpow'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hr0 : (0 : ℝ) < r := by linarith
    have hlog0 : 0 ≤ Real.log r := Real.log_nonneg hr
    rw [hF, Real.norm_eq_abs]
    simp only [pow_one]
    rw [abs_of_nonpos (by
      have := Real.exp_pos (-(r ^ 2) / σ ^ 2)
      nlinarith)]
    calc -(-2 * (Real.exp (-(r ^ 2) / σ ^ 2) * Real.log r))
        = 2 * Real.exp (-(r ^ 2) / σ ^ 2) * Real.log r := by ring
      _ ≤ 2 * Real.exp (-(c * r)) * r := by
          gcongr
          · exact hmono r hr
          · exact hlogle r hr
      _ = 2 / c * (c * r * Real.exp (-(c * r))) := by
          field_simp
  have hparts : (∫ r in Ioi (1 : ℝ),
      ((4 * r / σ ^ 2) * Real.exp (-(r ^ 2) / σ ^ 2) * Real.log r
        - 2 * Real.exp (-(r ^ 2) / σ ^ 2) / r)) = 0 := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto hFcont hFderiv hI3 hFtend]
    simp [hF]
  have hsplit : (∫ r in Ioi (1 : ℝ), (4 * r / σ ^ 2) * Real.exp (-(r ^ 2) / σ ^ 2) * Real.log r)
      = ∫ r in Ioi (1 : ℝ), 2 * Real.exp (-(r ^ 2) / σ ^ 2) / r := by
    have h := integral_add hI3 hI2
    have hfun : (fun r : ℝ => ((4 * r / σ ^ 2) * Real.exp (-(r ^ 2) / σ ^ 2) * Real.log r
        - 2 * Real.exp (-(r ^ 2) / σ ^ 2) / r) + 2 * Real.exp (-(r ^ 2) / σ ^ 2) / r)
        = fun r : ℝ => (4 * r / σ ^ 2) * Real.exp (-(r ^ 2) / σ ^ 2) * Real.log r := by
      funext r
      ring
    rw [hfun] at h
    rw [h, hparts, zero_add]
  rw [hsplit]
  -- ## Step 4: the substitution `u = r²/σ²`
  have hφ : ∀ r : ℝ, HasDerivAt (fun r : ℝ => c * r ^ 2) (c * (2 * r)) r := by
    intro r
    have h := (hasDerivAt_pow 2 r).const_mul c
    simpa using h
  have himage : (fun r : ℝ => c * r ^ 2) '' Ioi (1 : ℝ) = Ioi c := by
    ext u
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hr1 : (1 : ℝ) < r := hr
      show c < c * r ^ 2
      have h2 : 1 < r ^ 2 := by nlinarith
      calc c = c * 1 := (mul_one c).symm
        _ < c * r ^ 2 := by gcongr
    · intro hu
      have hu' : c < u := hu
      refine ⟨Real.sqrt (u / c), ?_, ?_⟩
      · show (1 : ℝ) < Real.sqrt (u / c)
        rw [Real.lt_sqrt (by norm_num), one_pow, lt_div_iff₀ hcpos]
        linarith
      · show c * Real.sqrt (u / c) ^ 2 = u
        rw [Real.sq_sqrt (div_nonneg (by linarith) hcpos.le)]
        field_simp
  have hinj : Set.InjOn (fun r : ℝ => c * r ^ 2) (Ioi (1 : ℝ)) := by
    intro x hx y hy hxy
    have hx0 : (0 : ℝ) ≤ x := le_of_lt (lt_trans zero_lt_one hx)
    have hy0 : (0 : ℝ) ≤ y := le_of_lt (lt_trans zero_lt_one hy)
    have h : x ^ 2 = y ^ 2 := by
      have := hxy
      simp only at this
      exact mul_left_cancel₀ hcpos.ne' this
    exact (pow_left_inj₀ hx0 hy0 (by norm_num)).mp h
  have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun r _ => (hφ r).hasDerivWithinAt) hinj (fun u : ℝ => Real.exp (-u) / u)
  rw [himage] at hcov
  unfold expIntegralE1
  rw [hcov]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
  simp only [smul_eq_mul]
  rw [abs_of_pos (by positivity), hexpc r]
  field_simp

end

end RHTower
