import GaloisForLFunctions.RHTower.Suzuki.SuzukiPolarRemainderLipschitz
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The finite-aperture polar convolution and its boundary-logarithmic rate

Suzuki's polar block acts on a finite aperture by

`(K_a u) x = ∫_{-a}^{a} r'' (x - y) u y dy`.

Because `r''` is bounded and Lipschitz on `[-(2a+1), 2a+1]`, the image of an integrable profile is
bounded and Lipschitz on the closed collar `|x| ≤ a + 1`, with constants proportional to the `L¹`
norm of the profile; Cauchy–Schwarz converts that into the `L²` bound of the source card.

In the boundary-logarithmic chart `x = x₀ + ε e^{-L}` the Lipschitz property becomes an exponential
rate: the trace converges to its endpoint value at speed `e^{-L}`, and its derivative — which
exists almost everywhere, and is set to zero elsewhere by the `deriv` convention — obeys the same
bound at every `L > 0`.  Consequently `e^{σL} G'` is square integrable for every `σ < 1`: the polar
term is Gamma-subcritical forcing, and cannot sustain an inverse-log-flat mode.
-/

open Set MeasureTheory intervalIntegral Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Suzuki's finite-aperture polar convolution operator. -/
def suzukiPolarConvolution (a : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in (-a)..a, suzukiWeilRemainderKernel (x - y) * u y

/-- Uniform bound of `r''` on the collar `|t| ≤ 2a + 1`. -/
def suzukiPolarSup (a : ℝ) : ℝ :=
  2 * Real.exp ((2 * a + 1) / 2) + 3 / 4 * Real.exp (2 * (2 * a + 1))

/-- Lipschitz constant of `r''` on the collar `|t| ≤ 2a + 1`. -/
def suzukiPolarLip (a : ℝ) : ℝ :=
  Real.exp ((2 * a + 1) / 2) + 5 * Real.exp (4 * (2 * a + 1))

theorem suzukiPolarSup_nonneg (a : ℝ) : 0 ≤ suzukiPolarSup a := by
  unfold suzukiPolarSup
  positivity

theorem suzukiPolarLip_nonneg (a : ℝ) : 0 ≤ suzukiPolarLip a := by
  unfold suzukiPolarLip
  positivity

private theorem kernel_shift_continuous (x : ℝ) :
    Continuous fun y : ℝ => suzukiWeilRemainderKernel (x - y) :=
  continuous_suzukiWeilRemainderKernel.comp (continuous_const.sub continuous_id)

private theorem intervalIntegrable_kernel_mul {a x : ℝ} {u : ℝ → ℝ}
    (hu : IntervalIntegrable u volume (-a) a) :
    IntervalIntegrable (fun y => suzukiWeilRemainderKernel (x - y) * u y) volume (-a) a :=
  hu.continuousOn_mul (kernel_shift_continuous x).continuousOn

/-- **The image of an integrable profile is bounded on the collar** — the sup half of `(4)`. -/
theorem abs_suzukiPolarConvolution_le {a x : ℝ} (ha : 0 ≤ a) (hx : |x| ≤ a + 1) {u : ℝ → ℝ}
    (hu : IntervalIntegrable u volume (-a) a) :
    |suzukiPolarConvolution a u x| ≤ suzukiPolarSup a * ∫ y in (-a)..a, |u y| := by
  have hab : -a ≤ a := by linarith
  have hint := intervalIntegrable_kernel_mul (a := a) (x := x) hu
  have hbound : ∀ y ∈ Icc (-a) a,
      |suzukiWeilRemainderKernel (x - y) * u y| ≤ suzukiPolarSup a * |u y| := by
    intro y hy
    have hxy : |x - y| ≤ 2 * a + 1 := by
      have h1 := abs_le.mp hx
      have h2 := hy.1
      have h3 := hy.2
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2]
    have hk : |suzukiWeilRemainderKernel (x - y)| ≤ suzukiPolarSup a :=
      abs_suzukiWeilRemainderKernel_le hxy
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hk (abs_nonneg _)
  calc |suzukiPolarConvolution a u x|
      ≤ ∫ y in (-a)..a, |suzukiWeilRemainderKernel (x - y) * u y| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ y in (-a)..a, suzukiPolarSup a * |u y| :=
        intervalIntegral.integral_mono_on hab hint.abs (hu.abs.const_mul _) hbound
    _ = suzukiPolarSup a * ∫ y in (-a)..a, |u y| := intervalIntegral.integral_const_mul _ _

/-- **The image of an integrable profile is Lipschitz on the collar** — the Lipschitz half of
`(4)`, with the literal constant of the kernel. -/
theorem abs_suzukiPolarConvolution_sub_le {a x x' : ℝ} (ha : 0 ≤ a) (hx : |x| ≤ a + 1)
    (hx' : |x'| ≤ a + 1) {u : ℝ → ℝ} (hu : IntervalIntegrable u volume (-a) a) :
    |suzukiPolarConvolution a u x - suzukiPolarConvolution a u x'|
      ≤ suzukiPolarLip a * |x - x'| * ∫ y in (-a)..a, |u y| := by
  have hab : -a ≤ a := by linarith
  have hint := intervalIntegrable_kernel_mul (a := a) (x := x) hu
  have hint' := intervalIntegrable_kernel_mul (a := a) (x := x') hu
  have hdiff : suzukiPolarConvolution a u x - suzukiPolarConvolution a u x'
      = ∫ y in (-a)..a, (suzukiWeilRemainderKernel (x - y) * u y
          - suzukiWeilRemainderKernel (x' - y) * u y) := by
    rw [intervalIntegral.integral_sub hint hint']
    rfl
  have hbound : ∀ y ∈ Icc (-a) a,
      |suzukiWeilRemainderKernel (x - y) * u y - suzukiWeilRemainderKernel (x' - y) * u y|
        ≤ suzukiPolarLip a * |x - x'| * |u y| := by
    intro y hy
    have h1 := abs_le.mp hx
    have h1' := abs_le.mp hx'
    have hxy : |x - y| ≤ 2 * a + 1 := by
      rw [abs_le]
      constructor <;> linarith [hy.1, hy.2, h1.1, h1.2]
    have hxy' : |x' - y| ≤ 2 * a + 1 := by
      rw [abs_le]
      constructor <;> linarith [hy.1, hy.2, h1'.1, h1'.2]
    have hk := abs_suzukiWeilRemainderKernel_sub_le hxy hxy'
    have hsame : (x - y) - (x' - y) = x - x' := by ring
    rw [hsame] at hk
    have hfac : suzukiWeilRemainderKernel (x - y) * u y - suzukiWeilRemainderKernel (x' - y) * u y
        = (suzukiWeilRemainderKernel (x - y) - suzukiWeilRemainderKernel (x' - y)) * u y := by
      ring
    rw [hfac, abs_mul]
    exact mul_le_mul_of_nonneg_right hk (abs_nonneg _)
  rw [hdiff]
  calc |∫ y in (-a)..a, (suzukiWeilRemainderKernel (x - y) * u y
          - suzukiWeilRemainderKernel (x' - y) * u y)|
      ≤ ∫ y in (-a)..a, |suzukiWeilRemainderKernel (x - y) * u y
          - suzukiWeilRemainderKernel (x' - y) * u y| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ y in (-a)..a, suzukiPolarLip a * |x - x'| * |u y| :=
        intervalIntegral.integral_mono_on hab (hint.sub hint').abs
          (hu.abs.const_mul _) hbound
    _ = suzukiPolarLip a * |x - x'| * ∫ y in (-a)..a, |u y| :=
        intervalIntegral.integral_const_mul _ _

/-- **Cauchy–Schwarz on the aperture** — `(18)` in squared form. -/
theorem sq_integral_abs_le {a : ℝ} (ha : 0 ≤ a) {u : ℝ → ℝ}
    (hu : IntervalIntegrable u volume (-a) a)
    (hu2 : IntervalIntegrable (fun y => u y ^ 2) volume (-a) a) :
    (∫ y in (-a)..a, |u y|) ^ 2 ≤ 2 * a * ∫ y in (-a)..a, u y ^ 2 := by
  have hab : -a ≤ a := by linarith
  have hu' : IntegrableOn u (Ioc (-a) a) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hu
  have hu2' : IntegrableOn (fun y => u y ^ 2) (Ioc (-a) a) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hu2
  have hmeas : volume (Ioc (-a) a) = ENNReal.ofReal (2 * a) := by
    rw [Real.volume_Ioc]
    congr 1
    ring
  have hfin : volume (Ioc (-a) a) ≠ ⊤ := by
    rw [hmeas]
    exact ENNReal.ofReal_ne_top
  have hone : Integrable (fun _ : ℝ => (1:ℝ)) (volume.restrict (Ioc (-a) a)) :=
    continuous_const.integrableOn_Ioc
  have habs2 : Integrable (fun y => |u y| ^ 2) (volume.restrict (Ioc (-a) a)) := by
    have : (fun y => |u y| ^ 2) = fun y => u y ^ 2 := by
      funext y
      exact sq_abs (u y)
    rw [this]
    exact hu2'
  have hmain := sq_integral_mul_le (μ := volume.restrict (Ioc (-a) a))
    (f := fun _ : ℝ => (1:ℝ)) (g := fun y => |u y|)
    aestronglyMeasurable_const
    (by simpa [Real.norm_eq_abs] using hu'.aestronglyMeasurable.norm)
    (by simpa only [one_pow] using hone) habs2
  have hsimp1 : (∫ y in Ioc (-a) a, (1:ℝ) * |u y|) = ∫ y in Ioc (-a) a, |u y| := by
    simp
  have hsimp2 : (∫ _y in Ioc (-a) a, (1:ℝ) ^ 2) = 2 * a := by
    simp only [one_pow, MeasureTheory.setIntegral_const, smul_eq_mul, mul_one,
      MeasureTheory.measureReal_def, hmeas]
    rw [ENNReal.toReal_ofReal (by linarith)]
  have hsimp3 : (∫ y in Ioc (-a) a, |u y| ^ 2) = ∫ y in Ioc (-a) a, u y ^ 2 := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    exact sq_abs (u y)
  rw [hsimp1, hsimp2, hsimp3] at hmain
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  exact hmain

/-- The boundary-logarithmic trace of the polar source at an interior point. -/
def suzukiPolarBoundaryTrace (a : ℝ) (u : ℝ → ℝ) (x₀ ε : ℝ) (L : ℝ) : ℝ :=
  suzukiPolarConvolution a u (x₀ + ε * Real.exp (-L))

/-- **`(6)`: the boundary trace approaches its endpoint value at speed `e^{-L}`.** -/
theorem abs_suzukiPolarBoundaryTrace_sub_le {a x₀ ε L : ℝ} (ha : 0 ≤ a) (hx₀ : |x₀| ≤ a)
    (hε : |ε| ≤ 1) (hL : 0 ≤ L) {u : ℝ → ℝ} (hu : IntervalIntegrable u volume (-a) a) :
    |suzukiPolarBoundaryTrace a u x₀ ε L - suzukiPolarConvolution a u x₀|
      ≤ suzukiPolarLip a * (∫ y in (-a)..a, |u y|) * Real.exp (-L) := by
  have hexp : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hexppos : 0 < Real.exp (-L) := Real.exp_pos _
  have hshift : |ε * Real.exp (-L)| ≤ 1 := by
    rw [abs_mul, abs_of_pos hexppos]
    nlinarith [abs_nonneg ε]
  have hx : |x₀ + ε * Real.exp (-L)| ≤ a + 1 := by
    calc |x₀ + ε * Real.exp (-L)| ≤ |x₀| + |ε * Real.exp (-L)| := abs_add_le _ _
      _ ≤ a + 1 := by linarith
  have hx' : |x₀| ≤ a + 1 := by linarith
  have hbase := abs_suzukiPolarConvolution_sub_le (a := a) (x := x₀ + ε * Real.exp (-L))
    (x' := x₀) ha hx hx' hu
  have hdist : |x₀ + ε * Real.exp (-L) - x₀| ≤ Real.exp (-L) := by
    rw [show x₀ + ε * Real.exp (-L) - x₀ = ε * Real.exp (-L) by ring, abs_mul,
      abs_of_pos hexppos]
    nlinarith [abs_nonneg ε]
  have hInt : 0 ≤ ∫ y in (-a)..a, |u y| := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro y _
    exact abs_nonneg _
  refine hbase.trans ?_
  have hstep : suzukiPolarLip a * |x₀ + ε * Real.exp (-L) - x₀|
      ≤ suzukiPolarLip a * Real.exp (-L) :=
    mul_le_mul_of_nonneg_left hdist (suzukiPolarLip_nonneg a)
  nlinarith [hInt, suzukiPolarLip_nonneg a]

/-- Slope comparison: a function dominated by a differentiable one near a point has derivative
bounded by the same factor times that derivative. -/
private theorem abs_deriv_le_of_slope_comparison {f g : ℝ → ℝ} {x C g' : ℝ} (hC : 0 ≤ C)
    (hg : HasDerivAt g g' x)
    (hcomp : ∀ᶠ y in 𝓝[≠] x, |f y - f x| ≤ C * |g y - g x|) :
    |deriv f x| ≤ C * |g'| := by
  by_cases hf : DifferentiableAt ℝ f x
  · have hfd : HasDerivAt f (deriv f x) x := hf.hasDerivAt
    have hslopef : Tendsto (fun y => |slope f x y|) (𝓝[≠] x) (𝓝 |deriv f x|) :=
      (hasDerivAt_iff_tendsto_slope.mp hfd).abs
    have hslopeg : Tendsto (fun y => C * |slope g x y|) (𝓝[≠] x) (𝓝 (C * |g'|)) :=
      ((hasDerivAt_iff_tendsto_slope.mp hg).abs).const_mul C
    refine le_of_tendsto_of_tendsto hslopef hslopeg ?_
    filter_upwards [hcomp, self_mem_nhdsWithin] with y hy hyne
    have hyx : y - x ≠ 0 := sub_ne_zero.mpr hyne
    rw [slope_def_field, slope_def_field, div_eq_mul_inv, div_eq_mul_inv, abs_mul, abs_mul,
      ← mul_assoc]
    have hsub1 : f y - f x = f y - f x := rfl
    have : |f y - f x| * |(y - x)⁻¹| ≤ C * |g y - g x| * |(y - x)⁻¹| :=
      mul_le_mul_of_nonneg_right hy (abs_nonneg _)
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  · rw [deriv_zero_of_not_differentiableAt hf]
    simpa using mul_nonneg hC (abs_nonneg g')

/-- **`(7)`: the boundary-trace derivative decays at the same exponential rate.**  At points of
non-differentiability `deriv` is zero, so the bound is unconditional. -/
theorem abs_deriv_suzukiPolarBoundaryTrace_le {a x₀ ε L : ℝ} (ha : 0 ≤ a) (hx₀ : |x₀| ≤ a)
    (hε : |ε| ≤ 1) (hL : 0 < L) {u : ℝ → ℝ} (hu : IntervalIntegrable u volume (-a) a) :
    |deriv (suzukiPolarBoundaryTrace a u x₀ ε) L|
      ≤ suzukiPolarLip a * (∫ y in (-a)..a, |u y|) * Real.exp (-L) := by
  have hInt : 0 ≤ ∫ y in (-a)..a, |u y| := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro y _
    exact abs_nonneg _
  set C : ℝ := suzukiPolarLip a * ∫ y in (-a)..a, |u y| with hC
  have hCnn : 0 ≤ C := mul_nonneg (suzukiPolarLip_nonneg a) hInt
  have hg : HasDerivAt (fun M : ℝ => Real.exp (-M)) (-Real.exp (-L)) L := by
    have h1 : HasDerivAt (fun M : ℝ => -M) (-1) L := hasDerivAt_neg L
    simpa using h1.exp
  have hcomp : ∀ᶠ y in 𝓝[≠] L,
      |suzukiPolarBoundaryTrace a u x₀ ε y - suzukiPolarBoundaryTrace a u x₀ ε L|
        ≤ C * |Real.exp (-y) - Real.exp (-L)| := by
    have hnhds : Ioi (0:ℝ) ∈ 𝓝[≠] L :=
      nhdsWithin_le_nhds (Ioi_mem_nhds hL)
    filter_upwards [hnhds] with y hy
    have hy0 : 0 < y := hy
    have hey : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have heL : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hxy : |x₀ + ε * Real.exp (-y)| ≤ a + 1 := by
      have h1 : |ε * Real.exp (-y)| ≤ 1 := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        nlinarith [abs_nonneg ε, Real.exp_pos (-y)]
      calc |x₀ + ε * Real.exp (-y)| ≤ |x₀| + |ε * Real.exp (-y)| := abs_add_le _ _
        _ ≤ a + 1 := by linarith
    have hxL : |x₀ + ε * Real.exp (-L)| ≤ a + 1 := by
      have h1 : |ε * Real.exp (-L)| ≤ 1 := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        nlinarith [abs_nonneg ε, Real.exp_pos (-L)]
      calc |x₀ + ε * Real.exp (-L)| ≤ |x₀| + |ε * Real.exp (-L)| := abs_add_le _ _
        _ ≤ a + 1 := by linarith
    have hbase := abs_suzukiPolarConvolution_sub_le (a := a) (x := x₀ + ε * Real.exp (-y))
      (x' := x₀ + ε * Real.exp (-L)) ha hxy hxL hu
    have hdist : |x₀ + ε * Real.exp (-y) - (x₀ + ε * Real.exp (-L))|
        ≤ |Real.exp (-y) - Real.exp (-L)| := by
      rw [show x₀ + ε * Real.exp (-y) - (x₀ + ε * Real.exp (-L))
          = ε * (Real.exp (-y) - Real.exp (-L)) by ring, abs_mul]
      nlinarith [abs_nonneg (Real.exp (-y) - Real.exp (-L)), abs_nonneg ε]
    refine hbase.trans ?_
    have hstep : suzukiPolarLip a * |x₀ + ε * Real.exp (-y) - (x₀ + ε * Real.exp (-L))|
        ≤ suzukiPolarLip a * |Real.exp (-y) - Real.exp (-L)| :=
      mul_le_mul_of_nonneg_left hdist (suzukiPolarLip_nonneg a)
    rw [hC]
    nlinarith [hInt, suzukiPolarLip_nonneg a, abs_nonneg (Real.exp (-y) - Real.exp (-L))]
  have hmain := abs_deriv_le_of_slope_comparison (f := suzukiPolarBoundaryTrace a u x₀ ε)
    (g := fun M : ℝ => Real.exp (-M)) (x := L) (C := C) (g' := -Real.exp (-L)) hCnn hg hcomp
  rw [abs_neg, abs_of_pos (Real.exp_pos _)] at hmain
  rw [hC] at hmain
  linarith [hmain]

/-- **`(8)`: the polar source is Gamma-subcritical.**  For every exponent below one, the weighted
boundary-trace derivative is square integrable on every ray `[L₀, ∞)` with `L₀ > 0`. -/
theorem integrableOn_sq_expMul_deriv_suzukiPolarBoundaryTrace {a x₀ ε σ L₀ : ℝ} (ha : 0 ≤ a)
    (hx₀ : |x₀| ≤ a) (hε : |ε| ≤ 1) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hL₀ : 0 < L₀) {u : ℝ → ℝ}
    (hu : IntervalIntegrable u volume (-a) a) :
    IntegrableOn
      (fun L => (Real.exp (σ * L) * deriv (suzukiPolarBoundaryTrace a u x₀ ε) L) ^ 2)
      (Ioi L₀) volume := by
  have hInt : 0 ≤ ∫ y in (-a)..a, |u y| := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro y _
    exact abs_nonneg _
  set C : ℝ := suzukiPolarLip a * ∫ y in (-a)..a, |u y| with hC
  have hCnn : 0 ≤ C := mul_nonneg (suzukiPolarLip_nonneg a) hInt
  have hmajor : IntegrableOn (fun L : ℝ => C ^ 2 * Real.exp (-(2 * (1 - σ)) * L))
      (Ioi L₀) volume :=
    (integrableOn_exp_mul_Ioi (by linarith) L₀).const_mul (C ^ 2)
  have hmeas : AEStronglyMeasurable
      (fun L => (Real.exp (σ * L) * deriv (suzukiPolarBoundaryTrace a u x₀ ε) L) ^ 2)
      (volume.restrict (Ioi L₀)) := by
    apply Measurable.aestronglyMeasurable
    exact (((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      (measurable_deriv _)).pow_const 2)
  refine Integrable.mono' hmajor hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
  have hLpos : 0 < L := lt_trans hL₀ hL
  have hd := abs_deriv_suzukiPolarBoundaryTrace_le (a := a) (x₀ := x₀) (ε := ε) (L := L)
    ha hx₀ hε hLpos hu
  rw [← hC] at hd
  have hexp : Real.exp (σ * L) * Real.exp (-L) = Real.exp (-(1 - σ) * L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsq : (Real.exp (σ * L) * deriv (suzukiPolarBoundaryTrace a u x₀ ε) L) ^ 2
      ≤ (C * Real.exp (-(1 - σ) * L)) ^ 2 := by
    have habs : |Real.exp (σ * L) * deriv (suzukiPolarBoundaryTrace a u x₀ ε) L|
        ≤ C * Real.exp (-(1 - σ) * L) := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _), ← hexp]
      have : Real.exp (σ * L) * |deriv (suzukiPolarBoundaryTrace a u x₀ ε) L|
          ≤ Real.exp (σ * L) * (C * Real.exp (-L)) :=
        mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le
      nlinarith [Real.exp_pos (σ * L), Real.exp_pos (-L)]
    have hnn : 0 ≤ C * Real.exp (-(1 - σ) * L) := by positivity
    nlinarith [abs_nonneg (Real.exp (σ * L) * deriv (suzukiPolarBoundaryTrace a u x₀ ε) L),
      sq_abs (Real.exp (σ * L) * deriv (suzukiPolarBoundaryTrace a u x₀ ε) L)]
  have hpow : (C * Real.exp (-(1 - σ) * L)) ^ 2 = C ^ 2 * Real.exp (-(2 * (1 - σ)) * L) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [hpow] at hsq
  exact hsq

end

end RHTower
