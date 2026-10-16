import GaloisForLFunctions.RHTower.CHMDChebyshevDiscrepancyDerivativeTransportLaw

/-!
# CHMD: a uniform bound on the space derivative of the Klein–Gordon prime kernel

The function form of the Chebyshev-discrepancy transport law reads
`chmdPrimeWave y = chmdPoleWave y + 2K_y(0) − poleShadow y − ∫_0^∞ ∂_sK_y(s) Δ(s) ds`, with the
`√`-weighted Chebyshev discrepancy `Δ(s) = Σ_{log n < s} Λ(n)/√n − 2e^{s/2}`.  The light-cone
estimates for `∂_sK_y` carry the factor `e^{π|y|} e^{y²/2}`.  This module removes that factor: the
space derivative is bounded uniformly in both the Klein–Gordon time `y` and the position `s`.

1. **Fourier form** (`kernelDerivFourier`, `hasDerivAt_chmdPrimeKernel_fourier`,
   `kernelDeriv_eq_kernelDerivFourier`): differentiating
   `K_y(s) = (1/π) ∫ cos(y√(r²+2)) sech²(r/2) cos(rs) dr` under the integral (dominated by
   `|r| sech²(r/2)`) gives `∂_sK_y(s) = −(1/π) ∫ cos(y√(r²+2)) sech²(r/2) r sin(rs) dr`, which
   coincides with the light-cone derivative `kernelDeriv`.  It is odd in `s`
   (`kernelDeriv_neg`, `kernelDeriv_zero`).
2. **First absolute moment** (`integral_abs_mul_sechSqHalf`): `∫ |r| sech²(r/2) dr = 8 log 2`, from
   the primitive `G(r) = 4r eʳ/(1+eʳ) − 4 log(1+eʳ)` of `r sech²(r/2)`, with `G(0) = −4 log 2` and
   `G(r) = −4re^{−r}/(e^{−r}+1) − 4 log(1+e^{−r}) → 0`.
3. **Uniform bound** (`abs_kernelDeriv_le`): `|∂_sK_y(s)| ≤ 8 log 2/π` for all `y, s`; hence the
   prime kernels form a uniformly Lipschitz family (`abs_chmdPrimeKernel_sub_le`).
4. **Window estimate for the discrepancy pairing**
   (`abs_setIntegral_kernelDeriv_mul_discrepancy_le`): for every `y` and `L`,
   `|∫_{(0,L]} ∂_sK_y Δ| ≤ (8 log 2/π) ∫_{(0,L]} |Δ|`, with `Δ` measurable and bounded on finite
   windows (`integrableOn_chebyshevDiscrepancy`).
-/

open MeasureTheory Set Filter Topology
open scoped Real

namespace RHTower.CHMDChebyshevTransport

open RHTower.CHMDLightCone GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Section 1: the Fourier form of the space derivative -/

/-- The Klein–Gordon symbol weight `A_y(r) = cos(y√(r²+2)) sech²(r/2)` of the prime kernel. -/
def kgSymbolWeight (y r : ℝ) : ℝ := Real.cos (y * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r

theorem continuous_kgSymbolWeight (y : ℝ) : Continuous (kgSymbolWeight y) :=
  (Real.continuous_cos.comp (continuous_const.mul
    (Real.continuous_sqrt.comp ((continuous_pow 2).add continuous_const)))).mul continuous_sechSqHalf

theorem abs_kgSymbolWeight_le (y r : ℝ) : |kgSymbolWeight y r| ≤ sechSqHalf r := by
  unfold kgSymbolWeight
  rw [abs_mul, abs_of_pos (sechSqHalf_pos r)]
  exact mul_le_of_le_one_left (sechSqHalf_pos r).le (Real.abs_cos_le_one _)

/-- **Fourier form of the space derivative of the prime kernel**:
`−(1/π) ∫ cos(y√(r²+2)) sech²(r/2) r sin(rs) dr`. -/
def kernelDerivFourier (y s : ℝ) : ℝ :=
  -(1 / π) * ∫ r : ℝ, kgSymbolWeight y r * (r * Real.sin (r * s))

theorem chmdPrimeKernel_eq_kgSymbolWeight (y s : ℝ) :
    chmdPrimeKernel y s = 1 / π * ∫ r : ℝ, kgSymbolWeight y r * Real.cos (r * s) := rfl

/-- Differentiation of the prime kernel under its Fourier integral. -/
theorem hasDerivAt_chmdPrimeKernel_fourier (y s : ℝ) :
    HasDerivAt (fun s => chmdPrimeKernel y s) (kernelDerivFourier y s) s := by
  have hAc := continuous_kgSymbolWeight y
  set F : ℝ → ℝ → ℝ := fun x r => kgSymbolWeight y r * Real.cos (r * x) with hF
  set F' : ℝ → ℝ → ℝ := fun x r => kgSymbolWeight y r * (-(r * Real.sin (r * x))) with hF'
  have hFint : Integrable (F s) := by
    refine integrable_sechSqHalf.mono' (hAc.mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun r => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _) |>.trans
      (abs_kgSymbolWeight_le y r)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (𝕜 := ℝ)
    (F := F) (x₀ := s) (s := Metric.ball s 1) (bound := fun r => |r| * sechSqHalf r)
    (Metric.ball_mem_nhds s one_pos)
    (Eventually.of_forall fun x => (hAc.mul (by fun_prop)).aestronglyMeasurable)
    hFint (F' := F') (hAc.mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun r x _ => by
      simp only [hF', Real.norm_eq_abs, abs_mul, abs_neg]
      have h1 := abs_kgSymbolWeight_le y r
      have h2 : |Real.sin (r * x)| ≤ 1 := Real.abs_sin_le_one _
      calc |kgSymbolWeight y r| * (|r| * |Real.sin (r * x)|) ≤ sechSqHalf r * (|r| * 1) :=
            mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg r))
              (by positivity) (sechSqHalf_pos r).le
        _ = |r| * sechSqHalf r := by ring)
    integrable_abs_mul_sechSqHalf
    (Eventually.of_forall fun r x _ => by
      simp only [hF, hF']
      have h := (((hasDerivAt_id' x).const_mul r).cos).const_mul (kgSymbolWeight y r)
      refine h.congr_deriv ?_
      ring)
  have h := key.2.const_mul (1 / π)
  have hfun : (fun s => chmdPrimeKernel y s) = fun x => 1 / π * ∫ r, F x r := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  unfold kernelDerivFourier
  rw [show (∫ r, F' s r) = -∫ r : ℝ, kgSymbolWeight y r * (r * Real.sin (r * s)) by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [hF']
    ring]
  ring

/-- The light-cone space derivative coincides with the Fourier form. -/
theorem kernelDeriv_eq_kernelDerivFourier (y s : ℝ) : kernelDeriv y s = kernelDerivFourier y s :=
  (hasDerivAt_chmdPrimeKernel_right y s).unique (hasDerivAt_chmdPrimeKernel_fourier y s)

/-- The space derivative is odd in the space variable. -/
theorem kernelDeriv_neg (y s : ℝ) : kernelDeriv y (-s) = -kernelDeriv y s := by
  rw [kernelDeriv_eq_kernelDerivFourier, kernelDeriv_eq_kernelDerivFourier]
  unfold kernelDerivFourier
  rw [show (∫ r : ℝ, kgSymbolWeight y r * (r * Real.sin (r * -s))) =
      -∫ r : ℝ, kgSymbolWeight y r * (r * Real.sin (r * s)) by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [mul_neg, Real.sin_neg]]
  ring

theorem kernelDeriv_zero (y : ℝ) : kernelDeriv y 0 = 0 := by
  have h := kernelDeriv_neg y 0
  rw [neg_zero] at h
  linarith

/-- The Fourier form is bounded by the first absolute moment of `sech²(r/2)`, uniformly in `y`, `s`. -/
theorem abs_kernelDerivFourier_le (y s : ℝ) :
    |kernelDerivFourier y s| ≤ 1 / π * ∫ r : ℝ, |r| * sechSqHalf r := by
  unfold kernelDerivFourier
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / π)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h := norm_integral_le_of_norm_le (μ := volume)
    (f := fun r => kgSymbolWeight y r * (r * Real.sin (r * s))) integrable_abs_mul_sechSqHalf
    (Eventually.of_forall fun r => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have h1 := abs_kgSymbolWeight_le y r
      have h2 : |Real.sin (r * s)| ≤ 1 := Real.abs_sin_le_one _
      calc |kgSymbolWeight y r| * (|r| * |Real.sin (r * s)|) ≤ sechSqHalf r * (|r| * 1) :=
            mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg r))
              (by positivity) (sechSqHalf_pos r).le
        _ = |r| * sechSqHalf r := by ring)
  rwa [Real.norm_eq_abs] at h

/-! ## Section 2: the first absolute moment `∫ |r| sech²(r/2) dr = 8 log 2` -/

/-- An antiderivative of `r sech²(r/2)`: `G(r) = 4r eʳ/(1+eʳ) − 4 log(1+eʳ)`. -/
def sechMomentPrimitive (r : ℝ) : ℝ :=
  4 * r * Real.exp r / (1 + Real.exp r) - 4 * Real.log (1 + Real.exp r)

theorem hasDerivAt_sechMomentPrimitive (r : ℝ) :
    HasDerivAt sechMomentPrimitive (r * sechSqHalf r) r := by
  have hpos : 0 < 1 + Real.exp r := by positivity
  have hnum : HasDerivAt (fun r : ℝ => 4 * r * Real.exp r)
      (4 * 1 * Real.exp r + 4 * r * Real.exp r) r := by
    have := ((hasDerivAt_id' r).const_mul 4).mul (Real.hasDerivAt_exp r)
    exact this.congr_deriv (by ring)
  have hden : HasDerivAt (fun r : ℝ => 1 + Real.exp r) (Real.exp r) r := by
    simpa using (Real.hasDerivAt_exp r).const_add 1
  have hq := hnum.div hden hpos.ne'
  have hl := (hden.log hpos.ne').const_mul 4
  have h := hq.sub hl
  unfold sechMomentPrimitive
  refine h.congr_deriv ?_
  unfold sechSqHalf
  field_simp
  ring

theorem continuous_sechMomentPrimitive : Continuous sechMomentPrimitive := by
  unfold sechMomentPrimitive
  have hpos : ∀ r : ℝ, 1 + Real.exp r ≠ 0 := fun r => by positivity
  exact ((continuous_const.mul continuous_id).mul Real.continuous_exp).div
    (continuous_const.add Real.continuous_exp) hpos |>.sub
    (continuous_const.mul ((continuous_const.add Real.continuous_exp).log hpos))

theorem sechMomentPrimitive_zero : sechMomentPrimitive 0 = -(4 * Real.log 2) := by
  unfold sechMomentPrimitive
  norm_num

theorem sechMomentPrimitive_eq (r : ℝ) :
    sechMomentPrimitive r =
      -(4 * (r * Real.exp (-r)) / (Real.exp (-r) + 1)) - 4 * Real.log (1 + Real.exp (-r)) := by
  unfold sechMomentPrimitive
  have he : Real.exp r * Real.exp (-r) = 1 := by rw [← Real.exp_add]; simp
  have hlog : Real.log (1 + Real.exp r) = r + Real.log (1 + Real.exp (-r)) := by
    have : 1 + Real.exp r = Real.exp r * (1 + Real.exp (-r)) := by linear_combination -he
    rw [this, Real.log_mul (Real.exp_pos r).ne' (by positivity), Real.log_exp]
  rw [hlog]
  have h1 : 0 < 1 + Real.exp r := by positivity
  have h2 : 0 < Real.exp (-r) + 1 := by positivity
  field_simp
  have hx : Real.exp (-r) = (Real.exp r)⁻¹ := Real.exp_neg r
  rw [hx]
  field_simp
  ring

theorem tendsto_sechMomentPrimitive_atTop : Tendsto sechMomentPrimitive atTop (𝓝 0) := by
  have he : Tendsto (fun r : ℝ => Real.exp (-r)) atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  have hre : Tendsto (fun r : ℝ => r * Real.exp (-r)) atTop (𝓝 0) := by
    have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    simpa using this
  have h1 : Tendsto (fun r : ℝ => 4 * (r * Real.exp (-r)) / (Real.exp (-r) + 1)) atTop (𝓝 0) := by
    have := (hre.const_mul 4).div (he.add_const 1) (by norm_num)
    rw [show (4 : ℝ) * 0 / (0 + 1) = 0 by norm_num] at this
    exact this
  have h2 : Tendsto (fun r : ℝ => Real.log (1 + Real.exp (-r))) atTop (𝓝 0) := by
    have := (he.const_add 1).log (by norm_num)
    simpa using this
  have h := h1.neg.sub (h2.const_mul 4)
  simp only [neg_zero, mul_zero, sub_zero] at h
  exact h.congr fun r => (sechMomentPrimitive_eq r).symm

/-- `∫_0^∞ r sech²(r/2) dr = 4 log 2`. -/
theorem integral_Ioi_mul_sechSqHalf : ∫ r in Ioi (0 : ℝ), r * sechSqHalf r = 4 * Real.log 2 := by
  have hint : IntegrableOn (fun r => r * sechSqHalf r) (Ioi (0 : ℝ)) := by
    refine integrable_abs_mul_sechSqHalf.integrableOn.congr_fun (fun r hr => ?_) measurableSet_Ioi
    simp only
    rw [abs_of_pos hr]
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := (0 : ℝ)) (m := 0)
    continuous_sechMomentPrimitive.continuousWithinAt
    (fun x _ => hasDerivAt_sechMomentPrimitive x) hint tendsto_sechMomentPrimitive_atTop
  rw [h, sechMomentPrimitive_zero]
  ring

/-- **First absolute moment of the sech² weight**: `∫ |r| sech²(r/2) dr = 8 log 2`. -/
theorem integral_abs_mul_sechSqHalf : ∫ r : ℝ, |r| * sechSqHalf r = 8 * Real.log 2 := by
  have h := integral_comp_abs (f := fun r => r * sechSqHalf r)
  have hcongr : (∫ r : ℝ, |r| * sechSqHalf r) = ∫ r : ℝ, |r| * sechSqHalf |r| := by
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only
    rcases le_or_gt 0 r with hr | hr
    · rw [abs_of_nonneg hr]
    · rw [abs_of_neg hr, sechSqHalf_neg]
  rw [hcongr, h, integral_Ioi_mul_sechSqHalf]
  ring

/-! ## Section 3: the uniform bound and its consequences -/

/-- **Uniform bound on the space derivative of the prime kernel**:
`|∂_s K_y(s)| ≤ 8 log 2 / π` for all times `y` and positions `s`. -/
theorem abs_kernelDeriv_le (y s : ℝ) : |kernelDeriv y s| ≤ 8 * Real.log 2 / π := by
  rw [kernelDeriv_eq_kernelDerivFourier]
  have h := abs_kernelDerivFourier_le y s
  rw [integral_abs_mul_sechSqHalf] at h
  calc |kernelDerivFourier y s| ≤ 1 / π * (8 * Real.log 2) := h
    _ = 8 * Real.log 2 / π := by ring

/-- **Uniform Lipschitz bound for the Klein–Gordon prime kernel**:
`|K_y(s) − K_y(s')| ≤ (8 log 2/π)|s − s'|` for all `y`, `s`, `s'`. -/
theorem abs_chmdPrimeKernel_sub_le (y s s' : ℝ) :
    |chmdPrimeKernel y s - chmdPrimeKernel y s'| ≤ 8 * Real.log 2 / π * |s - s'| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ)
    (f := fun s => chmdPrimeKernel y s) (f' := kernelDeriv y) (s := univ) (x := s') (y := s)
    (C := 8 * Real.log 2 / π)
    (fun x _ => (hasDerivAt_chmdPrimeKernel_right y x).hasDerivWithinAt)
    (fun x _ => by rw [Real.norm_eq_abs]; exact abs_kernelDeriv_le y x)
    convex_univ (mem_univ _) (mem_univ _)
  simpa [Real.norm_eq_abs] using h

theorem measurable_chebyshevDiscrepancy : Measurable chebyshevDiscrepancy := by
  unfold chebyshevDiscrepancy
  exact measurable_chebyshevStep.sub (by fun_prop)

/-- The Chebyshev discrepancy is bounded on every finite window. -/
theorem abs_chebyshevDiscrepancy_le {L s : ℝ} (hs : s ∈ Ioc (0 : ℝ) L) :
    |chebyshevDiscrepancy s| ≤ (2 * Real.log 4 + 18) * Real.exp (L / 2) := by
  unfold chebyshevDiscrepancy
  have hs0 : 0 ≤ s := hs.1.le
  have h1 := chebyshevStep_le hs0
  have h2 := chebyshevStep_nonneg s
  have he : Real.exp (s / 2) ≤ Real.exp (L / 2) := Real.exp_le_exp.mpr (by linarith [hs.2])
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]
  constructor <;> nlinarith [Real.exp_pos (s / 2)]

theorem integrableOn_chebyshevDiscrepancy (L : ℝ) :
    IntegrableOn chebyshevDiscrepancy (Ioc (0 : ℝ) L) :=
  Measure.integrableOn_of_bounded (M := (2 * Real.log 4 + 18) * Real.exp (L / 2))
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    measurable_chebyshevDiscrepancy.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs => by
      rw [Real.norm_eq_abs]; exact abs_chebyshevDiscrepancy_le hs))

/-- **Window estimate for the Step-3 pairing**, uniform in the Klein–Gordon time:
`|∫_{(0,L]} ∂_sK_y(s) Δ(s) ds| ≤ (8 log 2/π) ∫_{(0,L]} |Δ(s)| ds` for every `y`. -/
theorem abs_setIntegral_kernelDeriv_mul_discrepancy_le (y L : ℝ) :
    |∫ s in Ioc (0 : ℝ) L, kernelDeriv y s * chebyshevDiscrepancy s| ≤
      8 * Real.log 2 / π * ∫ s in Ioc (0 : ℝ) L, |chebyshevDiscrepancy s| := by
  have hint : IntegrableOn (fun s => 8 * Real.log 2 / π * |chebyshevDiscrepancy s|) (Ioc (0 : ℝ) L) :=
    (integrableOn_chebyshevDiscrepancy L).abs.const_mul _
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioc (0 : ℝ) L))
    (f := fun s => kernelDeriv y s * chebyshevDiscrepancy s) hint
    (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_kernelDeriv_le y s) (abs_nonneg _))
  rw [Real.norm_eq_abs, integral_const_mul] at h
  exact h

end

end RHTower.CHMDChebyshevTransport
