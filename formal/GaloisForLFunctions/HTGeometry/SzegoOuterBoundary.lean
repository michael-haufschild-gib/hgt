import GaloisForLFunctions.HTGeometry.PoissonFatou
import GaloisForLFunctions.HTGeometry.SzegoOuterFunction

/-!
# Boundary modulus of the Szegő outer function

The squared modulus of the Szegő outer function on the disk is the Poisson integral of the log
weight: `‖D(r e^{iφ})‖² = exp((2π)⁻¹∫₀²π P_r(θ-φ) log w(θ) dθ)`.  Combined with Fatou's theorem
(`tendsto_poissonConv_ae`) this gives the boundary identity `|D|² = w` a.e. — the analytic input to
the `≤` half of the first Szegő limit theorem.

The bridge is that the real part of the (negated) Herglotz–Riesz kernel evaluated at an interior
point `r e^{iφ}` and a boundary point `e^{iθ}` is exactly the angular Poisson kernel `P_r(θ-φ)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Real MeasureTheory Complex intervalIntegral Filter Topology
open scoped Real

/-- Squared distance between an interior point `r e^{iφ}` and a boundary point `e^{iθ}` of the unit
circle: `‖r e^{iφ} - e^{iθ}‖² = r² - 2r cos(θ-φ) + 1`. -/
theorem norm_sub_circleMap_sq (r φ θ : ℝ) :
    ‖circleMap 0 r φ - circleMap 0 1 θ‖ ^ 2 = r ^ 2 - 2 * r * Real.cos (θ - φ) + 1 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, circleMap, Complex.mul_re, Complex.mul_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_add, one_mul, zero_mul, sub_zero]
  rw [Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq φ, Real.sin_sq_add_cos_sq θ]

/-- The negated real part of the Herglotz–Riesz kernel at interior point `r e^{iφ}` and boundary
point `e^{iθ}` is the angular Poisson kernel: `-Re(herglotz 0 e^{iθ} (r e^{iφ})) = P_r(θ-φ)`. -/
theorem neg_re_herglotz_eq_poissonKer {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (φ θ : ℝ) :
    -(herglotzRieszKernel 0 (circleMap 0 1 θ) (circleMap 0 r φ)).re = poissonKer r (θ - φ) := by
  have habs : |r| < 1 := by rw [abs_of_nonneg hr0]; exact hr1
  have hre : (herglotzRieszKernel 0 (circleMap 0 1 θ) (circleMap 0 r φ)).re
      = poissonKernel 0 (circleMap 0 1 θ) (circleMap 0 r φ) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]; rfl
  rw [hre, poissonKernel_def]
  simp only [sub_zero]
  rw [norm_circleMap_zero, norm_circleMap_zero, abs_of_nonneg hr0,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1), norm_sub_circleMap_sq, poissonKer]
  have hden : 1 - 2 * r * Real.cos (θ - φ) + r ^ 2 ≠ 0 := (poissonKer_denom_pos habs (θ - φ)).ne'
  rw [← neg_div]
  congr 1 <;> ring

/-- Interval integrability of the real→complex coercion of an interval-integrable function. -/
theorem intervalIntegrable_ofReal {f : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun θ => (f θ : ℂ)) volume a b := by
  constructor <;>
  · apply MeasureTheory.Integrable.ofReal
    first | exact hf.1 | exact hf.2

/-- **The squared modulus of the Szegő outer function on the disk is the Poisson integral of the
log weight**: `‖D(r e^{iφ})‖² = exp((2π)⁻¹∫₀²π P_r(θ-φ) log w(θ) dθ)`. -/
theorem normSq_szegoOuter_circleMap {w : ℝ → ℝ}
    (hlog : IntervalIntegrable (fun θ => Real.log (w θ)) volume 0 (2 * π))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (φ : ℝ) :
    ‖szegoOuter w (circleMap 0 r φ)‖ ^ 2
      = Real.exp ((1 / (2 * π)) *
          ∫ θ in (0:ℝ)..(2 * π), poissonKer r (θ - φ) * Real.log (w θ)) := by
  set z : ℂ := circleMap 0 r φ with hz
  have hznorm : ‖z‖ = r := by rw [hz, norm_circleMap_zero, abs_of_nonneg hr0]
  -- denominator never zero
  have hdenom : ∀ θ : ℝ, z - circleMap 0 1 θ ≠ 0 := by
    intro θ hcontra
    rw [sub_eq_zero] at hcontra
    have : ‖z‖ = ‖circleMap 0 1 θ‖ := by rw [hcontra]
    rw [hznorm, norm_circleMap_zero, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1)] at this
    linarith
  -- θ ↦ herglotz 0 (e^{iθ}) z is continuous
  have hcont : Continuous (fun θ : ℝ => herglotzRieszKernel 0 (circleMap 0 1 θ) z) := by
    have heq : (fun θ : ℝ => herglotzRieszKernel 0 (circleMap 0 1 θ) z)
        = fun θ => (z + circleMap 0 1 θ) / (z - circleMap 0 1 θ) := by
      funext θ; simp only [herglotzRieszKernel_def, sub_zero]
    rw [heq]
    exact Continuous.div (by fun_prop) (by fun_prop) hdenom
  -- the complex integrand
  set F : ℝ → ℂ := fun θ => -herglotzRieszKernel 0 (circleMap 0 1 θ) z * (Real.log (w θ) : ℂ)
    with hFdef
  have hFint : IntervalIntegrable F volume 0 (2 * π) :=
    (intervalIntegrable_ofReal hlog).continuousOn_mul hcont.neg.continuousOn
  -- real part of the integrand is the Poisson-weighted log
  have hFre : ∀ θ, (F θ).re = poissonKer r (θ - φ) * Real.log (w θ) := by
    intro θ
    rw [hFdef]
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    rw [show -(herglotzRieszKernel 0 (circleMap 0 1 θ) z).re
        = poissonKer r (θ - φ) from neg_re_herglotz_eq_poissonKer hr0 hr1 φ θ]
  -- pull re through the integral
  have hInt_re : (∫ θ in (0:ℝ)..(2 * π), F θ).re
      = ∫ θ in (0:ℝ)..(2 * π), poissonKer r (θ - φ) * Real.log (w θ) := by
    have h1 : (∫ θ in (0:ℝ)..(2 * π), F θ).re = ∫ θ in (0:ℝ)..(2 * π), (F θ).re := by
      rw [← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hFint]
      simp only [Complex.reCLM_apply]
    rw [h1]
    exact intervalIntegral.integral_congr (fun θ _ => hFre θ)
  -- assemble
  have hcoef : (1 / (4 * π) : ℂ) = ((1 / (4 * π) : ℝ) : ℂ) := by push_cast; ring
  have hζre : ((1 / (4 * π) : ℂ) *
      ∫ θ in (0:ℝ)..(2 * π), -herglotzRieszKernel 0 (circleMap 0 1 θ) z * (Real.log (w θ) : ℂ)).re
      = (1 / (4 * π)) * ∫ θ in (0:ℝ)..(2 * π), poissonKer r (θ - φ) * Real.log (w θ) := by
    rw [hcoef, Complex.re_ofReal_mul, hInt_re]
  have hnorm : ‖szegoOuter w z‖
      = Real.exp ((1 / (4 * π)) * ∫ θ in (0:ℝ)..(2 * π), poissonKer r (θ - φ) * Real.log (w θ)) := by
    rw [szegoOuter, Complex.norm_exp, hζre]
  have h2a : (1 / (4 * π)) * (∫ θ in (0:ℝ)..(2 * π), poissonKer r (θ - φ) * Real.log (w θ))
      + (1 / (4 * π)) * (∫ θ in (0:ℝ)..(2 * π), poissonKer r (θ - φ) * Real.log (w θ))
      = (1 / (2 * π)) * ∫ θ in (0:ℝ)..(2 * π), poissonKer r (θ - φ) * Real.log (w θ) := by
    have hπ : π ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  rw [hnorm, pow_two, ← Real.exp_add, h2a]

/-- Periodic shift: `∫₀²π P_r(θ-φ) g(θ) dθ = ∫_{-π}^π P_r(t) g(φ+t) dt` for `g` `2π`-periodic. -/
theorem poissonConv_shift {g : ℝ → ℝ} (hper : Function.Periodic g (2 * π)) (r φ : ℝ) :
    (∫ θ in (0:ℝ)..(2 * π), poissonKer r (θ - φ) * g θ)
      = ∫ t in (-π)..π, poissonKer r t * g (φ + t) := by
  have hgper : Function.Periodic (fun t => g (φ + t)) (2 * π) := by
    intro t; simp only; rw [← add_assoc]; exact hper (φ + t)
  have hper2 : Function.Periodic (fun t => poissonKer r t * g (φ + t)) (2 * π) :=
    (poissonKer_periodic r).mul hgper
  -- substitute θ = φ + t
  have hsub : (∫ θ in (0:ℝ)..(2 * π), poissonKer r (θ - φ) * g θ)
      = ∫ t in (-φ)..(2 * π - φ), poissonKer r t * g (φ + t) := by
    have h := intervalIntegral.integral_comp_add_left
      (fun θ => poissonKer r (θ - φ) * g θ) φ (a := -φ) (b := 2 * π - φ)
    rw [show φ + -φ = (0:ℝ) by ring, show φ + (2 * π - φ) = 2 * π by ring] at h
    rw [← h]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    show poissonKer r (φ + t - φ) * g (φ + t) = poissonKer r t * g (φ + t)
    rw [show φ + t - φ = t by ring]
  have hshift := hper2.intervalIntegral_add_eq (-φ) (-π)
  rw [show -φ + 2 * π = 2 * π - φ by ring, show -π + 2 * π = π by ring] at hshift
  rw [hsub, hshift]

/-- `‖D(r e^{iφ})‖²` as the Poisson convolution of `log w` in Fatou-ready form. -/
theorem normSq_szegoOuter_eq_poissonConv {w : ℝ → ℝ}
    (hlog : IntervalIntegrable (fun θ => Real.log (w θ)) volume 0 (2 * π))
    (hper : Function.Periodic (fun θ => Real.log (w θ)) (2 * π))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (φ : ℝ) :
    ‖szegoOuter w (circleMap 0 r φ)‖ ^ 2
      = Real.exp ((2 * π)⁻¹ * ∫ t in (-π)..π, poissonKer r t * Real.log (w (φ + t))) := by
  rw [normSq_szegoOuter_circleMap hlog hr0 hr1 φ, poissonConv_shift hper r φ]
  congr 1
  rw [one_div]

/-- **Boundary identity `|D|² = w` a.e. (radial form).**  For a positive weight whose log is
integrable and `2π`-periodic, the squared modulus of the Szegő outer function converges radially to
`w` almost everywhere. -/
theorem tendsto_normSq_szegoOuter_ae {w : ℝ → ℝ}
    (hlogLI : LocallyIntegrable (fun θ => Real.log (w θ)) volume)
    (hlog : IntervalIntegrable (fun θ => Real.log (w θ)) volume 0 (2 * π))
    (hper : Function.Periodic (fun θ => Real.log (w θ)) (2 * π))
    (hwpos : ∀ φ, 0 < w φ) :
    ∀ᵐ φ, Tendsto (fun r => ‖szegoOuter w (circleMap 0 r φ)‖ ^ 2) (𝓝[<] 1) (𝓝 (w φ)) := by
  filter_upwards [tendsto_poissonConv_ae hlogLI] with φ hφ
  -- ‖D‖² = exp(Poisson conv);  Poisson conv → log w φ;  exp cont ⟹ ‖D‖² → w φ
  have hexp : Tendsto
      (fun r => Real.exp ((2 * π)⁻¹ * ∫ t in (-π)..π, poissonKer r t * Real.log (w (φ + t))))
      (𝓝[<] 1) (𝓝 (w φ)) := by
    have hcomp := (Real.continuous_exp.tendsto (Real.log (w φ))).comp hφ
    rw [Real.exp_log (hwpos φ)] at hcomp
    exact hcomp
  refine hexp.congr' ?_
  have h0r : ∀ᶠ r in 𝓝[<] (1:ℝ), (0:ℝ) ≤ r :=
    ((isOpen_Ioi.eventually_mem (by norm_num : (0:ℝ) < 1)).filter_mono nhdsWithin_le_nhds).mono
      (fun r hr => hr.le)
  filter_upwards [self_mem_nhdsWithin, h0r] with r hr hr0
  exact (normSq_szegoOuter_eq_poissonConv hlog hper hr0 (Set.mem_Iio.1 hr) φ).symm

end GaloisForLFunctions.HTGeometry
