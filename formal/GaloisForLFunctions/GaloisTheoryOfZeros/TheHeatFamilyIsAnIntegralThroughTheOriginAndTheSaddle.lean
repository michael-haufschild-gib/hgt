import GaloisForLFunctions.GaloisTheoryOfZeros.TheHeatCoverOfTheZeros
import GaloisForLFunctions.RHTower.RiemannKernelComplexStrip

/-!
# The heat family is an integral through the origin and along a horizontal line of the strip

Riemann's kernel `Φ` is holomorphic and even on the strip `|Im x| < π/4` and decays there like
`e^{−a e^{2 Re x}}`. So the contour of `H_τ(z) = ∫ Φ(x) e^{τx² + izx} dx` may be moved inside the
strip, for every complex time `τ`.

* `kernelHalf`, `complexHeat_eq_kernelHalf_add`: with `h(τ, z) = ∫_0^∞ Φ(x) e^{τx²+izx} dx`,
  `H_τ(z) = h(τ, z) + h(τ, −z)`.
* `exists_norm_stripIntegrand_le`: on a closed substrip, to the right of the imaginary axis,
  `|Φ(x) e^{τx²+izx}| ≤ M e^{−Re x}`: the double exponential decay of `Φ` beats the Gaussian.
* `kernelHalf_eq_corner`: for `0 ≤ η < π/4`,
  `h(τ, z) = i ∫_0^η Φ(iv) e^{−τv² − zv} dv + ∫_0^∞ Φ(s+iη) e^{τ(s+iη)² + iz(s+iη)} ds`
  (Cauchy on the rectangles `[0, N] × [0, η]`).
* `complexHeat_eq_corner`: the heat family is the sum of the two segment integrals (`bulkHalf`) and
  the two line integrals (`lineHalf`).

When `τ` is close to the imaginary direction, the segment through the origin carries the
stationary point `x = 0` of `e^{τx²}`, and the line at the height `η` passes through the saddle of
`τx² − πe^{2x}`.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower RHTower.DeBruijn RHTower.KernelStrip
open scoped Real Interval

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-- The integrand `Φ(x) e^{τx² + izx}` on the strip. -/
def stripIntegrand (τ z x : ℂ) : ℂ := kernelC x * cexp (τ * x ^ 2 + I * z * x)

theorem stripIntegrand_ofReal (τ z : ℂ) (x : ℝ) :
    stripIntegrand τ z x = (riemannKernelReal x : ℂ) * cexp (τ * (x : ℂ) ^ 2 + I * z * x) := by
  rw [stripIntegrand, kernelC_ofReal, riemannPhiKernel_eq_ofReal]

/-! ## The half transform -/

/-- The half transform `h(τ, z) = ∫_0^∞ Φ(x) e^{τx² + izx} dx`. -/
def kernelHalf (τ z : ℂ) : ℂ := ∫ s in Ioi (0 : ℝ), stripIntegrand τ z s

/-- `H_τ(z) = h(τ, z) + h(τ, −z)`, by the evenness of `Φ`. -/
theorem complexHeat_eq_kernelHalf_add (τ z : ℂ) :
    complexHeat τ z = kernelHalf τ z + kernelHalf τ (-z) := by
  set g : ℝ → ℂ := fun x => (riemannKernelReal x : ℂ) * cexp (τ * (x : ℂ) ^ 2 + I * z * x)
    with hg
  have hgi : Integrable g := by
    have h := integrable_complexWeight_mul_pow_mul_exp τ 0 z
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [hg, complexWeight, pow_zero, mul_one]
    rw [mul_assoc, ← Complex.exp_add]
  have hsplit : (∫ x, g x) = (∫ x in Iic (0 : ℝ), g x) + ∫ x in Ioi (0 : ℝ), g x := by
    have h := integral_add_compl (measurableSet_Iic (a := (0 : ℝ))) hgi
    rw [compl_Iic] at h
    exact h.symm
  have hneg : (∫ x in Iic (0 : ℝ), g x) = ∫ x in Ioi (0 : ℝ), g (-x) := by
    have h := integral_comp_neg_Ioi (0 : ℝ) g
    rw [neg_zero] at h
    exact h.symm
  rw [complexHeat, hsplit, hneg, kernelHalf, kernelHalf, add_comm]
  congr 1
  · exact setIntegral_congr_fun measurableSet_Ioi fun x _ => (stripIntegrand_ofReal τ z x).symm
  · refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [hg, stripIntegrand_ofReal, riemannKernel_superExp.even x, Complex.ofReal_neg]
    congr 2
    ring

/-! ## The double exponential beats the Gaussian -/

/-- `A s² + B s ≤ a e^{2s} + C` for `s ≥ 0`, with `C` explicit. -/
theorem quadratic_le_exp_add {a A B : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (hB : 0 ≤ B) {s : ℝ}
    (hs : 0 ≤ s) :
    A * s ^ 2 + B * s ≤ a * Real.exp (2 * s) +
      (A * (3 * (A + B) / (4 * a) + 1) ^ 2 + B * (3 * (A + B) / (4 * a) + 1)) := by
  set S : ℝ := 3 * (A + B) / (4 * a) + 1 with hS
  have hS1 : 1 ≤ S := by
    have : 0 ≤ 3 * (A + B) / (4 * a) := by positivity
    linarith
  have hexp : 4 / 3 * s ^ 3 ≤ Real.exp (2 * s) := by
    have h := Real.pow_div_factorial_le_exp (2 * s) (by linarith) 3
    have e : (2 * s) ^ 3 / ((Nat.factorial 3 : ℕ) : ℝ) = 4 / 3 * s ^ 3 := by
      rw [show ((Nat.factorial 3 : ℕ) : ℝ) = 6 by norm_num [Nat.factorial]]
      ring
    rwa [e] at h
  have h0 : 0 ≤ a * Real.exp (2 * s) := by positivity
  rcases le_total s S with h | h
  · have h1 : A * s ^ 2 ≤ A * S ^ 2 := by gcongr
    have h2 : B * s ≤ B * S := by gcongr
    linarith
  · have hs1 : 1 ≤ s := hS1.trans h
    have h1 : (A + B) * s ^ 2 ≤ a * (4 / 3 * s ^ 3) := by
      have h3 : 3 * (A + B) / (4 * a) ≤ s := by linarith
      rw [div_le_iff₀ (by positivity)] at h3
      have h4 := mul_le_mul_of_nonneg_right h3 (sq_nonneg s)
      nlinarith
    have h2 : B * s ≤ B * s ^ 2 := by
      have : s ≤ s ^ 2 := by nlinarith
      gcongr
    have h3 : a * (4 / 3 * s ^ 3) ≤ a * Real.exp (2 * s) := by gcongr
    have h4 : 0 ≤ A * S ^ 2 + B * S := by positivity
    linarith

/-- On a closed substrip, to the right of the imaginary axis, the integrand `Φ(x)e^{τx²+izx}` is
at most a multiple of `e^{−Re x}`. -/
theorem exists_norm_stripIntegrand_le (τ z : ℂ) {c : ℝ} (hc : c < π / 4) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℂ, 0 ≤ x.re → |x.im| ≤ c →
      ‖stripIntegrand τ z x‖ ≤ M * Real.exp (-x.re) := by
  have hπ := Real.pi_pos
  by_cases hc0 : c < 0
  · exact ⟨0, le_rfl, fun x _ hx => absurd ((abs_nonneg _).trans hx) (not_le.mpr hc0)⟩
  push Not at hc0
  have hκ : 0 < Real.cos (2 * c) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  set a : ℝ := π * Real.cos (2 * c) / 2 with ha
  have ha0 : 0 < a := by positivity
  have hea : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  set K : ℝ := termConst riemannCuspPoly a / (1 - Real.exp (-a)) with hK
  have hK0 : 0 ≤ K := by
    have h1 := termConst_nonneg riemannCuspPoly ha0
    have h2 : 0 < 1 - Real.exp (-a) := by linarith
    positivity
  set A : ℝ := ‖τ‖ with hA
  set B : ℝ := ‖z‖ + 3 / 2 with hB
  set C : ℝ := A * (3 * (A + B) / (4 * a) + 1) ^ 2 + B * (3 * (A + B) / (4 * a) + 1) with hC
  have hc1 : c < 1 := by
    have := Real.pi_lt_d2
    linarith
  refine ⟨K * Real.exp (A + ‖z‖ + C), by positivity, fun x hre him => ?_⟩
  have h1 : ‖kernelC x‖ ≤ K * (Real.exp (x.re / 2) * Real.exp (-(a * Real.exp (2 * x.re)))) :=
    norm_cseries_le_of_re_nonneg riemannCuspPoly hc him hre
  -- the Gaussian and the oscillating factor
  have hnx : ‖x‖ ≤ x.re + 1 := by
    refine (Complex.norm_le_abs_re_add_abs_im x).trans ?_
    rw [abs_of_nonneg hre]
    linarith
  have hnx2 : ‖x‖ ^ 2 ≤ x.re ^ 2 + 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have h2 : x.im * x.im ≤ 1 := by
      have h3 := abs_le.mp (him.trans hc1.le)
      nlinarith
    nlinarith
  have h2 : ‖cexp (τ * x ^ 2 + I * z * x)‖ ≤
      Real.exp (A * (x.re ^ 2 + 1) + ‖z‖ * (x.re + 1)) := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    rw [Complex.add_re]
    have h3 : (τ * x ^ 2).re ≤ A * (x.re ^ 2 + 1) := by
      refine (Complex.re_le_norm _).trans ?_
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left hnx2 (norm_nonneg _)
    have h4 : (I * z * x).re ≤ ‖z‖ * (x.re + 1) := by
      refine (Complex.re_le_norm _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
      exact mul_le_mul_of_nonneg_left hnx (norm_nonneg _)
    linarith
  have hq := quadratic_le_exp_add ha0 (norm_nonneg τ) (by positivity : (0 : ℝ) ≤ B) hre
  rw [stripIntegrand, norm_mul]
  calc ‖kernelC x‖ * ‖cexp (τ * x ^ 2 + I * z * x)‖
      ≤ K * (Real.exp (x.re / 2) * Real.exp (-(a * Real.exp (2 * x.re)))) *
          Real.exp (A * (x.re ^ 2 + 1) + ‖z‖ * (x.re + 1)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = K * Real.exp (x.re / 2 + -(a * Real.exp (2 * x.re)) +
          (A * (x.re ^ 2 + 1) + ‖z‖ * (x.re + 1))) := by
        rw [Real.exp_add, Real.exp_add]; ring
    _ ≤ K * Real.exp (A + ‖z‖ + C + -x.re) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK0
        simp only [hB] at hq
        linarith
    _ = K * Real.exp (A + ‖z‖ + C) * Real.exp (-x.re) := by
        rw [Real.exp_add]; ring

/-- The integrand is continuous along the horizontal lines of the strip. -/
theorem continuous_stripIntegrand_line (τ z : ℂ) {h : ℝ} (hh : |h| < π / 4) :
    Continuous fun s : ℝ => stripIntegrand τ z (s + h * I) := by
  have hk : Continuous fun s : ℝ => kernelC (s + h * I) := by
    refine continuous_iff_continuousAt.2 fun s => ?_
    have him : ((s : ℂ) + h * I).im = h := by simp
    have hd : DifferentiableAt ℂ kernelC ((s : ℂ) + h * I) :=
      differentiableAt_kernelC (by rw [him]; exact hh)
    exact hd.continuousAt.comp (f := fun s : ℝ => (s : ℂ) + h * I) (by fun_prop)
  unfold stripIntegrand
  fun_prop

/-! ## The corner -/

/-- **Corner shift.** The half line `[0, ∞)` may be moved to the height `η < π/4` of the strip,
at the cost of the segment `[0, iη]`. -/
theorem integral_Ioi_stripIntegrand_eq_corner (τ z : ℂ) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η < π / 4) :
    ∫ s in Ioi (0 : ℝ), stripIntegrand τ z s =
      (∫ s in Ioi (0 : ℝ), stripIntegrand τ z (s + η * I)) +
        I * ∫ v in (0 : ℝ)..η, stripIntegrand τ z (v * I) := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_stripIntegrand_le τ z hη
  set f : ℂ → ℂ := stripIntegrand τ z with hf
  -- holomorphic at every point of the strip
  have hfd : ∀ x : ℂ, |x.im| < π / 4 → DifferentiableAt ℂ f x := by
    intro x hx
    have h1 := differentiableAt_kernelC hx
    have h2 : DifferentiableAt ℂ (fun x : ℂ => cexp (τ * x ^ 2 + I * z * x)) x := by fun_prop
    exact h1.mul h2
  have hre : ∀ s h : ℝ, ((s : ℂ) + h * I).re = s := fun s h => by simp
  have him : ∀ s h : ℝ, ((s : ℂ) + h * I).im = h := fun s h => by simp
  -- the horizontal rays of height at most `η`
  have hint : ∀ h : ℝ, 0 ≤ h → h ≤ η → IntegrableOn (fun s : ℝ => f (s + h * I)) (Ioi 0) := by
    intro h h0 h1
    have hdom : IntegrableOn (fun s : ℝ => M * Real.exp (-s)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul M
    refine Integrable.mono' hdom (continuous_stripIntegrand_line τ z
      (by rw [abs_of_nonneg h0]; linarith)).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
    have h2 := hM (s + h * I) (by rw [hre]; exact (mem_Ioi.mp hs).le)
      (by rw [him, abs_of_nonneg h0]; exact h1)
    rwa [hre] at h2
  have hint0 : IntegrableOn (fun s : ℝ => f s) (Ioi 0) := by
    have h := hint 0 le_rfl hη0
    simpa using h
  -- Cauchy's theorem on the rectangle with corners `0` and `N + iη`
  have hrect : ∀ N : ℝ, (∫ x in (0 : ℝ)..N, f x) =
      (∫ x in (0 : ℝ)..N, f (x + η * I)) - I * (∫ y in (0 : ℝ)..η, f (N + y * I)) +
        I * ∫ y in (0 : ℝ)..η, f (y * I) := by
    intro N
    have hdiff : DifferentiableOn ℂ f
        ([[(0 : ℂ).re, ((N : ℂ) + η * I).re]] ×ℂ [[(0 : ℂ).im, ((N : ℂ) + η * I).im]]) := by
      intro x hx
      have hx2 : x.im ∈ [[(0 : ℂ).im, ((N : ℂ) + η * I).im]] := (Complex.mem_reProdIm.mp hx).2
      rw [him, Complex.zero_im, uIcc_of_le hη0] at hx2
      refine (hfd x ?_).differentiableWithinAt
      rw [abs_of_nonneg hx2.1]
      exact lt_of_le_of_lt hx2.2 hη
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f (0 : ℂ) (N + η * I)
      hdiff
    rw [hre, him] at h
    simp only [Complex.zero_re, Complex.zero_im, Complex.ofReal_zero, zero_mul, add_zero,
      zero_add, smul_eq_mul] at h
    linear_combination h
  have hL1 : Tendsto (fun N : ℝ => ∫ x in (0 : ℝ)..N, f x) atTop
      (𝓝 (∫ x in Ioi (0 : ℝ), f x)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hint0 tendsto_id
  have hL2 : Tendsto (fun N : ℝ => ∫ x in (0 : ℝ)..N, f (x + η * I)) atTop
      (𝓝 (∫ x in Ioi (0 : ℝ), f (x + η * I))) :=
    intervalIntegral_tendsto_integral_Ioi 0 (hint η hη0 le_rfl) tendsto_id
  -- the far vertical side tends to zero
  have hL3 : Tendsto (fun N : ℝ => I * ∫ y in (0 : ℝ)..η, f (N + y * I)) atTop (𝓝 0) := by
    have hb : ∀ᶠ N : ℝ in atTop, ‖I * ∫ y in (0 : ℝ)..η, f (N + y * I)‖ ≤
        M * Real.exp (-N) * |η - 0| := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
      rw [norm_mul, Complex.norm_I, one_mul]
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
      rw [uIoc_of_le hη0] at hy
      have h2 := hM (N + y * I) (by rw [hre]; exact hN)
        (by rw [him, abs_of_pos hy.1]; exact hy.2)
      rwa [hre] at h2
    have hz : Tendsto (fun N : ℝ => M * Real.exp (-N) * |η - 0|) atTop (𝓝 0) := by
      have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul M).mul_const |η - 0|
      simpa using h2
    exact squeeze_zero_norm' hb hz
  have hR : Tendsto (fun N : ℝ => ∫ x in (0 : ℝ)..N, f x) atTop
      (𝓝 ((∫ x in Ioi (0 : ℝ), f (x + η * I)) - 0 + I * ∫ y in (0 : ℝ)..η, f (y * I))) :=
    ((hL2.sub hL3).add_const _).congr fun N => (hrect N).symm
  have hfin := tendsto_nhds_unique hL1 hR
  rw [sub_zero] at hfin
  exact hfin

/-- The segment `[0, iη]` of the half transform: `i ∫_0^η Φ(iv) e^{−τv² − zv} dv`. -/
def bulkHalf (τ : ℂ) (η : ℝ) (z : ℂ) : ℂ :=
  I * ∫ v in (0 : ℝ)..η, kernelC (v * I) * cexp (-(τ * (v : ℂ) ^ 2) - z * v)

/-- The horizontal line of the half transform:
`∫_0^∞ Φ(s+iη) e^{τ(s+iη)² + iz(s+iη)} ds`. -/
def lineHalf (τ : ℂ) (η : ℝ) (z : ℂ) : ℂ :=
  ∫ s in Ioi (0 : ℝ), stripIntegrand τ z (s + η * I)

/-- **The half transform through the corner `iη`.** -/
theorem kernelHalf_eq_corner (τ z : ℂ) {η : ℝ} (hη0 : 0 ≤ η) (hη : η < π / 4) :
    kernelHalf τ z = bulkHalf τ η z + lineHalf τ η z := by
  rw [kernelHalf, integral_Ioi_stripIntegrand_eq_corner τ z hη0 hη, bulkHalf, lineHalf,
    add_comm (∫ s in Ioi (0 : ℝ), stripIntegrand τ z (s + η * I))]
  congr 2
  refine intervalIntegral.integral_congr fun v _ => ?_
  simp only [stripIntegrand]
  congr 2
  linear_combination (τ * (v : ℂ) ^ 2 + z * v) * Complex.I_sq

/-- **The heat family through the origin and the line of height `η`.** For every complex time
`τ` and `0 ≤ η < π/4`, `H_τ(z)` is the sum of the two segment integrals and the two line
integrals. -/
theorem complexHeat_eq_corner (τ z : ℂ) {η : ℝ} (hη0 : 0 ≤ η) (hη : η < π / 4) :
    complexHeat τ z =
      bulkHalf τ η z + bulkHalf τ η (-z) + (lineHalf τ η z + lineHalf τ η (-z)) := by
  rw [complexHeat_eq_kernelHalf_add, kernelHalf_eq_corner τ z hη0 hη,
    kernelHalf_eq_corner τ (-z) hη0 hη]
  ring

end

end GaloisForLFunctions.GaloisTheoryOfZeros
