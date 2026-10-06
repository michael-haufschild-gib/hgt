import GaloisForLFunctions.RHTower.ZetaCarrier
import GaloisForLFunctions.HTGeometry.BarnesMellinRepresentation
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The functional-equation factor against a Gaussian weight

For `T > 0` let `g_T(s) = exp((s − ½)²/T²)` and let `k_T(u) = (T/2√π) e^{−T²u²/4}` be the centred
Gaussian density of variance `2/T²`.  For `y > 0`, on the line `Re s = −½`,

`∫ χ(−½+it) y^{−½+it} g_T(−½+it) dt = 2π y J_T(y)`,  where `J_T(y) = ∫ 2cos(2πy eᵘ) e^{u/2} k_T(u) du`

(`integral_zetaChi_mul_cpow_mul_gaussWeight`).  With `w = 1 − s`,
`χ(s) = Γ(w) [(−2πi)^{−w} + (2πi)^{−w}]`.  For `Re a > 0`, `Γ(w) a^{−w} = ∫₀^∞ e^{−ax} x^{w−1} dx`, and
the `t`-integral of `x^w g_T` is the log-normal density in `x`.  Both sides are continuous in `a` up to
`Re a = 0`, because `|Γ(3/2 + iv)| = |½ + iv| √(π / cosh πv)`.

For `T ≥ 1` the kernel satisfies:
* `|J_T(y)| ≤ C` (`exists_abs_leftKernel_le`);
* `|J_T(y) − 2cos(2πy) e^{−4π²y²/T²}| ≤ C (y/T² + 1/T)` (`exists_abs_leftKernel_sub_le`);
* `|J_T(y)| ≤ C T²/y²` (`exists_abs_leftKernel_le_sq`), by two integrations by parts in `u`.
-/

open Complex MeasureTheory Filter Topology Set

namespace RHTower.GaussZeroSum

noncomputable section

/-- The Gaussian weight `g_T(s) = exp((s − ½)²/T²)`. -/
def gaussWeight (T : ℝ) (s : ℂ) : ℂ := cexp ((s - 1 / 2) ^ 2 / (T : ℂ) ^ 2)

/-- The centred Gaussian density `k_T(u) = (T/2√π) e^{−T²u²/4}` of variance `2/T²`. -/
def gaussDensity (T u : ℝ) : ℝ := T / (2 * Real.sqrt Real.pi) * Real.exp (-(T ^ 2 * u ^ 2 / 4))

/-- The left kernel `J_T(y) = ∫ 2cos(2πy eᵘ) e^{u/2} k_T(u) du`. -/
def leftKernel (T y : ℝ) : ℝ :=
  ∫ u : ℝ, 2 * Real.cos (2 * Real.pi * y * Real.exp u) * Real.exp (u / 2) * gaussDensity T u

theorem gaussDensity_nonneg {T : ℝ} (hT : 0 ≤ T) (u : ℝ) : 0 ≤ gaussDensity T u := by
  unfold gaussDensity
  positivity

theorem continuous_gaussDensity (T : ℝ) : Continuous (gaussDensity T) := by
  unfold gaussDensity
  fun_prop

/-! ## Gaussian moments -/

/-- `|x|^m e^{−x²/16} ≤ m! e⁴`. -/
theorem pow_abs_mul_exp_neg_sq_le (m : ℕ) (x : ℝ) :
    |x| ^ m * Real.exp (-(x ^ 2 / 16)) ≤ m.factorial * Real.exp 4 := by
  have h1 : |x| ^ m ≤ m.factorial * Real.exp |x| := by
    have := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) m
    have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
    rw [div_le_iff₀ hf] at this
    linarith
  have h2 : Real.exp |x| * Real.exp (-(x ^ 2 / 16)) ≤ Real.exp 4 := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_abs x, sq_nonneg (|x| - 8)]
  calc |x| ^ m * Real.exp (-(x ^ 2 / 16))
      ≤ (m.factorial * Real.exp |x|) * Real.exp (-(x ^ 2 / 16)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = m.factorial * (Real.exp |x| * Real.exp (-(x ^ 2 / 16))) := by ring
    _ ≤ m.factorial * Real.exp 4 :=
        mul_le_mul_of_nonneg_left h2 (by exact_mod_cast (Nat.factorial_pos m).le)

/-- Pointwise moment bound: for `T ≥ 1`,
`|u|^m e^{c|u|} k_T(u) ≤ T^{−m} m! e^{4 + 4c²} · (T/2√π) e^{−T²u²/8}`. -/
theorem moment_integrand_le (m : ℕ) {c T : ℝ} (hT : 1 ≤ T) (u : ℝ) :
    |u| ^ m * Real.exp (c * |u|) * gaussDensity T u ≤
      (m.factorial * Real.exp (4 + 4 * c ^ 2) / T ^ m) *
        (T / (2 * Real.sqrt Real.pi) * Real.exp (-(T ^ 2 * u ^ 2 / 8))) := by
  have hT0 : 0 < T := by linarith
  have hpow : |u| ^ m = |T * u| ^ m / T ^ m := by
    rw [abs_mul, abs_of_pos hT0, mul_pow]
    field_simp
  have hA := pow_abs_mul_exp_neg_sq_le m (T * u)
  have hB : Real.exp (c * |u|) * Real.exp (-(T ^ 2 * u ^ 2 / 16)) ≤ Real.exp (4 * c ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hT2 : 1 ≤ T ^ 2 := by nlinarith
    have hu2 : u ^ 2 ≤ T ^ 2 * u ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hT2 (sq_nonneg u)]
    nlinarith [sq_abs u, sq_nonneg (|u| - 8 * c), abs_nonneg u]
  have hsplit : Real.exp (-(T ^ 2 * u ^ 2 / 4)) =
      Real.exp (-((T * u) ^ 2 / 16)) * Real.exp (-(T ^ 2 * u ^ 2 / 16)) *
        Real.exp (-(T ^ 2 * u ^ 2 / 8)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hconst : 0 ≤ T / (2 * Real.sqrt Real.pi) := by positivity
  unfold gaussDensity
  rw [hsplit, hpow]
  have hTm : 0 < T ^ m := pow_pos hT0 m
  have key : |T * u| ^ m * Real.exp (-((T * u) ^ 2 / 16)) *
      (Real.exp (c * |u|) * Real.exp (-(T ^ 2 * u ^ 2 / 16))) ≤
      (m.factorial * Real.exp 4) * Real.exp (4 * c ^ 2) :=
    mul_le_mul hA hB (by positivity) (by positivity)
  have hexp : Real.exp (4 + 4 * c ^ 2) = Real.exp 4 * Real.exp (4 * c ^ 2) := Real.exp_add _ _
  rw [hexp]
  calc |T * u| ^ m / T ^ m * Real.exp (c * |u|) *
        (T / (2 * Real.sqrt Real.pi) * (Real.exp (-((T * u) ^ 2 / 16)) *
          Real.exp (-(T ^ 2 * u ^ 2 / 16)) * Real.exp (-(T ^ 2 * u ^ 2 / 8))))
      = (|T * u| ^ m * Real.exp (-((T * u) ^ 2 / 16)) *
          (Real.exp (c * |u|) * Real.exp (-(T ^ 2 * u ^ 2 / 16)))) / T ^ m *
          (T / (2 * Real.sqrt Real.pi) * Real.exp (-(T ^ 2 * u ^ 2 / 8))) := by ring
    _ ≤ ((m.factorial * Real.exp 4) * Real.exp (4 * c ^ 2)) / T ^ m *
          (T / (2 * Real.sqrt Real.pi) * Real.exp (-(T ^ 2 * u ^ 2 / 8))) := by
        gcongr
    _ = _ := by ring

theorem integrable_gaussian_eighth {T : ℝ} (hT : 0 < T) :
    Integrable (fun u : ℝ => T / (2 * Real.sqrt Real.pi) * Real.exp (-(T ^ 2 * u ^ 2 / 8))) := by
  have h := (integrable_exp_neg_mul_sq (b := T ^ 2 / 8) (by positivity)).const_mul
    (T / (2 * Real.sqrt Real.pi))
  refine h.congr (Eventually.of_forall fun u => ?_)
  simp only
  congr 2
  ring

theorem integral_gaussian_eighth {T : ℝ} (hT : 0 < T) :
    ∫ u : ℝ, T / (2 * Real.sqrt Real.pi) * Real.exp (-(T ^ 2 * u ^ 2 / 8)) = Real.sqrt 2 := by
  rw [integral_const_mul]
  have h := integral_gaussian (T ^ 2 / 8)
  have he : (fun x : ℝ => Real.exp (-(T ^ 2 / 8) * x ^ 2)) =
      fun u => Real.exp (-(T ^ 2 * u ^ 2 / 8)) := by
    funext u; congr 1; ring
  rw [he] at h
  rw [h]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hs : Real.sqrt (Real.pi / (T ^ 2 / 8)) = Real.sqrt 2 * (2 * Real.sqrt Real.pi) / T := by
    rw [show Real.pi / (T ^ 2 / 8) = (2 * (2 * Real.sqrt Real.pi) / T) ^ 2 / 2 by
      field_simp
      rw [Real.sq_sqrt hpi.le]
      ring]
    rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq (by positivity)]
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hs]
  field_simp

theorem continuous_moment_integrand (m : ℕ) (c T : ℝ) :
    Continuous (fun u : ℝ => |u| ^ m * Real.exp (c * |u|) * gaussDensity T u) := by
  have := continuous_gaussDensity T
  fun_prop

theorem integrable_moment_integrand (m : ℕ) {c T : ℝ} (hT : 1 ≤ T) :
    Integrable (fun u : ℝ => |u| ^ m * Real.exp (c * |u|) * gaussDensity T u) := by
  have hT0 : 0 < T := by linarith
  refine ((integrable_gaussian_eighth hT0).const_mul
    (m.factorial * Real.exp (4 + 4 * c ^ 2) / T ^ m)).mono'
    (continuous_moment_integrand m c T).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    have := gaussDensity_nonneg hT0.le u
    positivity)]
  exact moment_integrand_le m hT u

/-- **Gaussian moments**: `∫ |u|^m e^{c|u|} k_T(u) du ≤ √2 m! e^{4+4c²} / T^m` for `T ≥ 1`. -/
theorem integral_moment_le (m : ℕ) {c T : ℝ} (hT : 1 ≤ T) :
    ∫ u : ℝ, |u| ^ m * Real.exp (c * |u|) * gaussDensity T u ≤
      Real.sqrt 2 * m.factorial * Real.exp (4 + 4 * c ^ 2) / T ^ m := by
  have hT0 : 0 < T := by linarith
  calc ∫ u : ℝ, |u| ^ m * Real.exp (c * |u|) * gaussDensity T u
      ≤ ∫ u : ℝ, (m.factorial * Real.exp (4 + 4 * c ^ 2) / T ^ m) *
          (T / (2 * Real.sqrt Real.pi) * Real.exp (-(T ^ 2 * u ^ 2 / 8))) :=
        integral_mono (integrable_moment_integrand m hT)
          ((integrable_gaussian_eighth hT0).const_mul _) (moment_integrand_le m hT)
    _ = (m.factorial * Real.exp (4 + 4 * c ^ 2) / T ^ m) * Real.sqrt 2 := by
        rw [integral_const_mul, integral_gaussian_eighth hT0]
    _ = _ := by ring

/-! ## Bounds for the left kernel -/

theorem continuous_leftKernel_integrand (T y : ℝ) :
    Continuous (fun u : ℝ =>
      2 * Real.cos (2 * Real.pi * y * Real.exp u) * Real.exp (u / 2) * gaussDensity T u) := by
  have := continuous_gaussDensity T
  fun_prop

theorem abs_exp_half_le (u : ℝ) : Real.exp (u / 2) ≤ Real.exp ((1 / 2) * |u|) := by
  apply Real.exp_le_exp.mpr
  have := le_abs_self u
  linarith

theorem integrable_leftKernel_integrand {T : ℝ} (hT : 1 ≤ T) (y : ℝ) :
    Integrable (fun u : ℝ =>
      2 * Real.cos (2 * Real.pi * y * Real.exp u) * Real.exp (u / 2) * gaussDensity T u) := by
  have hT0 : 0 < T := by linarith
  refine ((integrable_moment_integrand 0 (c := 1 / 2) hT).const_mul 2).mono'
    (continuous_leftKernel_integrand T y).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  have hk := gaussDensity_nonneg hT0.le u
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hk, abs_two,
    abs_of_pos (Real.exp_pos _)]
  simp only [pow_zero, one_mul]
  have hc := Real.abs_cos_le_one (2 * Real.pi * y * Real.exp u)
  have he := abs_exp_half_le u
  calc 2 * |Real.cos (2 * Real.pi * y * Real.exp u)| * Real.exp (u / 2) * gaussDensity T u
      ≤ 2 * 1 * Real.exp ((1 / 2) * |u|) * gaussDensity T u := by gcongr
    _ = _ := by ring

/-- **Uniform bound**: `|J_T(y)| ≤ 2√2 e⁵` for `T ≥ 1`. -/
theorem abs_leftKernel_le {T : ℝ} (hT : 1 ≤ T) (y : ℝ) :
    |leftKernel T y| ≤ 2 * Real.sqrt 2 * Real.exp 5 := by
  have hT0 : 0 < T := by linarith
  unfold leftKernel
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le
    ((integrable_moment_integrand 0 (c := 1 / 2) hT).const_mul 2)
    (Eventually.of_forall fun u => ?_)).trans ?_
  · have hk := gaussDensity_nonneg hT0.le u
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hk, abs_two,
      abs_of_pos (Real.exp_pos _)]
    simp only [pow_zero, one_mul]
    have hc := Real.abs_cos_le_one (2 * Real.pi * y * Real.exp u)
    have he := abs_exp_half_le u
    calc 2 * |Real.cos (2 * Real.pi * y * Real.exp u)| * Real.exp (u / 2) * gaussDensity T u
        ≤ 2 * 1 * Real.exp ((1 / 2) * |u|) * gaussDensity T u := by gcongr
      _ = _ := by ring
  · rw [integral_const_mul]
    have h := integral_moment_le 0 (c := 1 / 2) hT
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one, one_mul] at h ⊢
    have h5 : Real.exp (4 + 4 * (1 / 2 : ℝ) ^ 2) = Real.exp 5 := by norm_num
    rw [h5] at h
    linarith

/-! ## Linear combinations of moments -/

theorem continuous_quadratic_moment (A B C c T : ℝ) :
    Continuous (fun u : ℝ => (A + B * |u| + C * u ^ 2) * Real.exp (c * |u|) * gaussDensity T u) := by
  have := continuous_gaussDensity T
  fun_prop

theorem integrable_quadratic_moment (A B C c : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    Integrable (fun u : ℝ => (A + B * |u| + C * u ^ 2) * Real.exp (c * |u|) * gaussDensity T u) := by
  have h0 := (integrable_moment_integrand 0 (c := c) hT).const_mul A
  have h1 := (integrable_moment_integrand 1 (c := c) hT).const_mul B
  have h2 := (integrable_moment_integrand 2 (c := c) hT).const_mul C
  refine ((h0.add h1).add h2).congr (Eventually.of_forall fun u => ?_)
  simp only [Pi.add_apply, pow_zero, pow_one, sq_abs]
  ring

/-- `∫ (A + B|u| + Cu²) e^{c|u|} k_T ≤ √2 e^{4+4c²} (A + B/T + 2C/T²)` for `A, B, C ≥ 0`. -/
theorem integral_quadratic_moment_le {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (c : ℝ)
    {T : ℝ} (hT : 1 ≤ T) :
    ∫ u : ℝ, (A + B * |u| + C * u ^ 2) * Real.exp (c * |u|) * gaussDensity T u ≤
      Real.sqrt 2 * Real.exp (4 + 4 * c ^ 2) * (A + B / T + 2 * C / T ^ 2) := by
  have h0 := integrable_moment_integrand 0 (c := c) hT
  have h1 := integrable_moment_integrand 1 (c := c) hT
  have h2 := integrable_moment_integrand 2 (c := c) hT
  have e : (fun u : ℝ => (A + B * |u| + C * u ^ 2) * Real.exp (c * |u|) * gaussDensity T u) =
      fun u => A * (|u| ^ 0 * Real.exp (c * |u|) * gaussDensity T u) +
        B * (|u| ^ 1 * Real.exp (c * |u|) * gaussDensity T u) +
        C * (|u| ^ 2 * Real.exp (c * |u|) * gaussDensity T u) := by
    funext u
    simp only [pow_zero, pow_one, sq_abs]
    ring
  have hadd1 := integral_add ((h0.const_mul A).add (h1.const_mul B)) (h2.const_mul C)
  have hadd2 := integral_add (h0.const_mul A) (h1.const_mul B)
  simp only [Pi.add_apply] at hadd1 hadd2
  rw [e, hadd1, hadd2, integral_const_mul, integral_const_mul, integral_const_mul]
  have m0 := integral_moment_le 0 (c := c) hT
  have m1 := integral_moment_le 1 (c := c) hT
  have m2 := integral_moment_le 2 (c := c) hT
  simp only [Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two, Nat.cast_one,
    Nat.cast_ofNat, pow_zero, pow_one, div_one, mul_one] at m0 m1 m2
  have hE : 0 ≤ Real.sqrt 2 * Real.exp (4 + 4 * c ^ 2) := by positivity
  calc A * (∫ u : ℝ, |u| ^ 0 * Real.exp (c * |u|) * gaussDensity T u) +
        B * (∫ u : ℝ, |u| ^ 1 * Real.exp (c * |u|) * gaussDensity T u) +
        C * (∫ u : ℝ, |u| ^ 2 * Real.exp (c * |u|) * gaussDensity T u)
      ≤ A * (Real.sqrt 2 * Real.exp (4 + 4 * c ^ 2)) +
        B * (Real.sqrt 2 * Real.exp (4 + 4 * c ^ 2) / T) +
        C * (Real.sqrt 2 * 2 * Real.exp (4 + 4 * c ^ 2) / T ^ 2) := by
        simp only [pow_zero, pow_one, one_mul] at m0 m1 m2 ⊢
        gcongr
    _ = _ := by ring

/-! ## The Gaussian approximation of the kernel -/

/-- `∫ cos(α + βu) k_T(u) du = cos α · e^{−β²/T²}`. -/
theorem integral_cos_affine_mul_gaussDensity {T : ℝ} (hT : 0 < T) (α β : ℝ) :
    ∫ u : ℝ, Real.cos (α + β * u) * gaussDensity T u =
      Real.cos α * Real.exp (-(β ^ 2 / T ^ 2)) := by
  set b : ℂ := ((T ^ 2 / 4 : ℝ) : ℂ) with hbdef
  have hb : 0 < b.re := by rw [hbdef, Complex.ofReal_re]; positivity
  set c₀ : ℝ := T / (2 * Real.sqrt Real.pi) with hc₀
  set F : ℝ → ℂ := fun u => cexp ((α : ℂ) * I) * (c₀ : ℂ) *
    (cexp (I * (β : ℂ) * u) * cexp (-b * u ^ 2)) with hFdef
  have hFint : Integrable F := by
    have hg := (integrable_exp_neg_mul_sq (b := T ^ 2 / 4) (by positivity))
    refine (hg.const_mul c₀).mono' (by unfold F; fun_prop)
      (Eventually.of_forall fun u => ?_)
    have h1 : ((α : ℂ) * I).re = 0 := by simp
    have h2 : (I * (β : ℂ) * (u : ℂ)).re = 0 := by simp
    have h3 : (-b * (u : ℂ) ^ 2).re = -(T ^ 2 / 4) * u ^ 2 := by
      rw [hbdef]; simp [← Complex.ofReal_pow]
    have hc0 : 0 ≤ c₀ := by positivity
    have hn : ‖F u‖ = c₀ * Real.exp (-(T ^ 2 / 4) * u ^ 2) := by
      simp only [hFdef, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, h1, h2,
        h3, Real.exp_zero, one_mul, abs_of_nonneg hc0]
    exact hn.le
  have hre : ∀ u : ℝ, Real.cos (α + β * u) * gaussDensity T u = (F u).re := by
    intro u
    have e1 : cexp ((α : ℂ) * I) * cexp (I * (β : ℂ) * u) = cexp (((α + β * u : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have e2 : cexp (-b * (u : ℂ) ^ 2) = ((Real.exp (-(T ^ 2 * u ^ 2 / 4)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp, hbdef]; congr 1; push_cast; ring
    have e3 : F u = cexp (((α + β * u : ℝ) : ℂ) * I) *
        ((c₀ * Real.exp (-(T ^ 2 * u ^ 2 / 4)) : ℝ) : ℂ) := by
      simp only [hFdef]
      rw [e2, ← e1]
      push_cast
      ring_nf
    rw [e3, Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re]
    simp only [gaussDensity, hc₀]
  simp_rw [hre]
  rw [show (∫ u : ℝ, (F u).re) = RCLike.re (∫ u : ℝ, F u) from integral_re hFint,
    RCLike.re_to_complex]
  have hint : ∫ u : ℝ, F u = cexp ((α : ℂ) * I) * (c₀ : ℂ) *
      ((Real.pi / b) ^ (1 / 2 : ℂ) * cexp (-(β : ℂ) ^ 2 / (4 * b))) := by
    simp only [hFdef]
    rw [integral_const_mul, fourierIntegral_gaussian hb]
  rw [hint]
  have hsq : ((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) = ((2 * Real.sqrt Real.pi / T : ℝ) : ℂ) := by
    rw [hbdef, ← Complex.ofReal_div]
    have hx : (0 : ℝ) ≤ Real.pi / (T ^ 2 / 4) := by positivity
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hx,
      ← Real.sqrt_eq_rpow]
    congr 1
    rw [show Real.pi / (T ^ 2 / 4) = (2 * Real.sqrt Real.pi / T) ^ 2 by
      field_simp; rw [Real.sq_sqrt Real.pi_pos.le]; ring]
    exact Real.sqrt_sq (by positivity)
  have hexp : cexp (-(β : ℂ) ^ 2 / (4 * b)) = ((Real.exp (-(β ^ 2 / T ^ 2)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp, hbdef]
    congr 1
    push_cast
    field_simp
  rw [hsq, hexp]
  have hc : (c₀ : ℂ) * ((2 * Real.sqrt Real.pi / T : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hc₀]
    have : T / (2 * Real.sqrt Real.pi) * (2 * Real.sqrt Real.pi / T) = 1 := by
      have : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
      field_simp
    rw [this, Complex.ofReal_one]
  calc (cexp ((α : ℂ) * I) * (c₀ : ℂ) *
        (((2 * Real.sqrt Real.pi / T : ℝ) : ℂ) * ((Real.exp (-(β ^ 2 / T ^ 2)) : ℝ) : ℂ))).re
      = (cexp ((α : ℂ) * I) * ((Real.exp (-(β ^ 2 / T ^ 2)) : ℝ) : ℂ)).re := by
        rw [show cexp ((α : ℂ) * I) * (c₀ : ℂ) *
            (((2 * Real.sqrt Real.pi / T : ℝ) : ℂ) * ((Real.exp (-(β ^ 2 / T ^ 2)) : ℝ) : ℂ)) =
            cexp ((α : ℂ) * I) * ((c₀ : ℂ) * ((2 * Real.sqrt Real.pi / T : ℝ) : ℂ)) *
              ((Real.exp (-(β ^ 2 / T ^ 2)) : ℝ) : ℂ) by ring, hc, mul_one]
    _ = _ := by rw [Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re]

theorem abs_exp_sub_one_sub_le (u : ℝ) :
    |Real.exp u - 1 - u| ≤ 3 * u ^ 2 * Real.exp |u| := by
  rcases le_or_gt |u| 1 with hu | hu
  · have h := Real.abs_exp_sub_one_sub_id_le hu
    have : u ^ 2 ≤ 3 * u ^ 2 * Real.exp |u| := by
      have := Real.one_le_exp (abs_nonneg u)
      nlinarith [sq_nonneg u]
    linarith
  · have he : Real.exp u ≤ Real.exp |u| := Real.exp_le_exp.mpr (le_abs_self u)
    have h1 : 1 + |u| ≤ Real.exp |u| := by linarith [Real.add_one_le_exp |u|]
    have hu2 : 1 ≤ u ^ 2 := by nlinarith [sq_abs u]
    have hpos := Real.exp_pos |u|
    calc |Real.exp u - 1 - u| ≤ Real.exp u + 1 + |u| := by
          rw [abs_le]; constructor <;>
            nlinarith [Real.exp_pos u, abs_nonneg u, le_abs_self u, neg_abs_le u]
      _ ≤ 3 * Real.exp |u| := by linarith
      _ ≤ 3 * u ^ 2 * Real.exp |u| := by nlinarith

theorem abs_exp_half_sub_one_le (u : ℝ) :
    |Real.exp (u / 2) - 1| ≤ 3 * |u| * Real.exp |u| := by
  rcases le_or_gt |u / 2| 1 with hu | hu
  · have h := Real.abs_exp_sub_one_le hu
    rw [abs_div, abs_two] at h
    have := Real.one_le_exp (abs_nonneg u)
    nlinarith [abs_nonneg u]
  · rw [abs_div, abs_two] at hu
    have he : Real.exp (u / 2) ≤ Real.exp |u| :=
      Real.exp_le_exp.mpr (by linarith [le_abs_self u, abs_nonneg u])
    have hpos := Real.exp_pos |u|
    calc |Real.exp (u / 2) - 1| ≤ Real.exp (u / 2) + 1 := by
          rw [abs_le]; constructor <;> nlinarith [Real.exp_pos (u / 2)]
      _ ≤ 2 * Real.exp |u| := by linarith [Real.one_le_exp (abs_nonneg u)]
      _ ≤ 3 * |u| * Real.exp |u| := by nlinarith

/-- Pointwise comparison with the linearized phase. -/
theorem abs_leftKernel_integrand_sub_le (y u : ℝ) (hy : 0 ≤ y) :
    |Real.cos (2 * Real.pi * y * Real.exp u) * Real.exp (u / 2) -
        Real.cos (2 * Real.pi * y + 2 * Real.pi * y * u)| ≤
      (6 * Real.pi * y * u ^ 2 + 3 * |u|) * Real.exp ((3 / 2) * |u|) := by
  have h1 := Real.abs_cos_sub_cos_le (2 * Real.pi * y * Real.exp u)
    (2 * Real.pi * y + 2 * Real.pi * y * u)
  have h2 : |2 * Real.pi * y * Real.exp u - (2 * Real.pi * y + 2 * Real.pi * y * u)| =
      2 * Real.pi * y * |Real.exp u - 1 - u| := by
    rw [show 2 * Real.pi * y * Real.exp u - (2 * Real.pi * y + 2 * Real.pi * y * u) =
      (2 * Real.pi * y) * (Real.exp u - 1 - u) by ring, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi * y)]
  have h3 := abs_exp_sub_one_sub_le u
  have h4 := abs_exp_half_sub_one_le u
  have h5 : Real.exp (u / 2) ≤ Real.exp ((1 / 2) * |u|) := abs_exp_half_le u
  have h6 : Real.exp |u| * Real.exp ((1 / 2) * |u|) = Real.exp ((3 / 2) * |u|) := by
    rw [← Real.exp_add]; congr 1; ring
  have h7 : Real.exp |u| ≤ Real.exp ((3 / 2) * |u|) :=
    Real.exp_le_exp.mpr (by linarith [abs_nonneg u])
  have hc := Real.abs_cos_le_one (2 * Real.pi * y + 2 * Real.pi * y * u)
  have hsplit : Real.cos (2 * Real.pi * y * Real.exp u) * Real.exp (u / 2) -
      Real.cos (2 * Real.pi * y + 2 * Real.pi * y * u) =
      (Real.cos (2 * Real.pi * y * Real.exp u) -
        Real.cos (2 * Real.pi * y + 2 * Real.pi * y * u)) * Real.exp (u / 2) +
      Real.cos (2 * Real.pi * y + 2 * Real.pi * y * u) * (Real.exp (u / 2) - 1) := by ring
  rw [hsplit]
  have hpy : 0 ≤ 2 * Real.pi * y := by positivity
  calc _ ≤ |Real.cos (2 * Real.pi * y * Real.exp u) -
          Real.cos (2 * Real.pi * y + 2 * Real.pi * y * u)| * Real.exp (u / 2) +
        |Real.cos (2 * Real.pi * y + 2 * Real.pi * y * u)| * |Real.exp (u / 2) - 1| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos (u / 2))]
    _ ≤ (2 * Real.pi * y * (3 * u ^ 2 * Real.exp |u|)) * Real.exp ((1 / 2) * |u|) +
        1 * (3 * |u| * Real.exp ((3 / 2) * |u|)) := by
        gcongr
        · exact h1.trans (h2.trans_le (mul_le_mul_of_nonneg_left h3 hpy))
        · exact h4.trans (by gcongr)
    _ = (6 * Real.pi * y * u ^ 2 + 3 * |u|) * Real.exp ((3 / 2) * |u|) := by
        rw [show (2 * Real.pi * y * (3 * u ^ 2 * Real.exp |u|)) * Real.exp ((1 / 2) * |u|) =
          6 * Real.pi * y * u ^ 2 * (Real.exp |u| * Real.exp ((1 / 2) * |u|)) by ring, h6]
        ring

/-- **The Gaussian approximation**: for `T ≥ 1` and `y ≥ 0`,
`|J_T(y) − 2cos(2πy) e^{−4π²y²/T²}| ≤ C (y/T² + 1/T)`. -/
theorem exists_abs_leftKernel_sub_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → ∀ y : ℝ, 0 ≤ y →
      |leftKernel T y - 2 * Real.cos (2 * Real.pi * y) *
        Real.exp (-(4 * Real.pi ^ 2 * y ^ 2 / T ^ 2))| ≤ C * (y / T ^ 2 + 1 / T) := by
  set K : ℝ := Real.sqrt 2 * Real.exp (4 + 4 * (3 / 2) ^ 2) with hK
  refine ⟨24 * Real.pi * K + 6 * K, by positivity, fun T hT y hy => ?_⟩
  have hT0 : 0 < T := by linarith
  have hmain := integral_cos_affine_mul_gaussDensity hT0 (2 * Real.pi * y) (2 * Real.pi * y)
  have hmain' : ∫ u : ℝ, 2 * Real.cos (2 * Real.pi * y + 2 * Real.pi * y * u) * gaussDensity T u =
      2 * Real.cos (2 * Real.pi * y) * Real.exp (-(4 * Real.pi ^ 2 * y ^ 2 / T ^ 2)) := by
    have e : (fun u : ℝ => 2 * Real.cos (2 * Real.pi * y + 2 * Real.pi * y * u) *
        gaussDensity T u) = fun u => 2 * (Real.cos (2 * Real.pi * y + 2 * Real.pi * y * u) *
          gaussDensity T u) := by funext u; ring
    rw [e, integral_const_mul, hmain]
    have : (2 * Real.pi * y) ^ 2 / T ^ 2 = 4 * Real.pi ^ 2 * y ^ 2 / T ^ 2 := by ring
    rw [this]; ring
  have hint2 : Integrable (fun u : ℝ =>
      2 * Real.cos (2 * Real.pi * y + 2 * Real.pi * y * u) * gaussDensity T u) := by
    refine ((integrable_moment_integrand 0 (c := 0) hT).const_mul 2).mono'
      (by have := continuous_gaussDensity T; fun_prop) (Eventually.of_forall fun u => ?_)
    have hk := gaussDensity_nonneg hT0.le u
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_two, abs_of_nonneg hk]
    simp only [pow_zero, zero_mul, Real.exp_zero, one_mul, mul_one]
    have := Real.abs_cos_le_one (2 * Real.pi * y + 2 * Real.pi * y * u)
    nlinarith
  unfold leftKernel
  rw [← hmain', ← integral_sub (integrable_leftKernel_integrand hT y) hint2, ← Real.norm_eq_abs]
  have hbound := integral_quadratic_moment_le (A := 0) (B := 6) (C := 12 * Real.pi * y)
    le_rfl (by norm_num) (by positivity) (3 / 2) hT
  refine (norm_integral_le_of_norm_le (integrable_quadratic_moment 0 6 (12 * Real.pi * y) (3 / 2) hT)
    (Eventually.of_forall fun u => ?_)).trans ?_
  · have hk := gaussDensity_nonneg hT0.le u
    have hp := abs_leftKernel_integrand_sub_le y u hy
    rw [Real.norm_eq_abs, show 2 * Real.cos (2 * Real.pi * y * Real.exp u) * Real.exp (u / 2) *
        gaussDensity T u - 2 * Real.cos (2 * Real.pi * y + 2 * Real.pi * y * u) * gaussDensity T u =
        2 * gaussDensity T u * (Real.cos (2 * Real.pi * y * Real.exp u) * Real.exp (u / 2) -
          Real.cos (2 * Real.pi * y + 2 * Real.pi * y * u)) by ring, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * gaussDensity T u)]
    calc 2 * gaussDensity T u * |Real.cos (2 * Real.pi * y * Real.exp u) * Real.exp (u / 2) -
          Real.cos (2 * Real.pi * y + 2 * Real.pi * y * u)|
        ≤ 2 * gaussDensity T u *
          ((6 * Real.pi * y * u ^ 2 + 3 * |u|) * Real.exp ((3 / 2) * |u|)) := by gcongr
      _ = _ := by ring
  · refine hbound.trans ?_
    rw [← hK]
    have hT2 : T ≤ T ^ 2 := by nlinarith
    have hy0 : 0 ≤ y / T ^ 2 := by positivity
    have hKp : 0 ≤ K := by positivity
    have e : K * (0 + 6 / T + 2 * (12 * Real.pi * y) / T ^ 2) =
        24 * Real.pi * K * (y / T ^ 2) + 6 * K * (1 / T) := by ring
    rw [e]
    have hT1 : 0 ≤ 1 / T := by positivity
    nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 24 * Real.pi) hKp) hT1,
      mul_nonneg (by positivity : (0 : ℝ) ≤ 6 * K) hy0]

/-! ## Decay of the kernel: two integrations by parts -/

theorem hasDerivAt_gaussDensity (T u : ℝ) :
    HasDerivAt (gaussDensity T) (-(T ^ 2 * u / 2) * gaussDensity T u) u := by
  have hin : HasDerivAt (fun x : ℝ => -(T ^ 2 * x ^ 2 / 4)) (-(T ^ 2 * u / 2)) u := by
    have h := (((hasDerivAt_pow 2 u).const_mul (T ^ 2)).div_const 4).neg
    refine h.congr_deriv ?_
    push_cast
    ring
  have h2 := ((Real.hasDerivAt_exp _).comp u hin).const_mul (T / (2 * Real.sqrt Real.pi))
  refine h2.congr_deriv ?_
  unfold gaussDensity
  ring

theorem hasDerivAt_exp_neg_half (u : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (-(u / 2))) (Real.exp (-(u / 2)) * (-(1 / 2))) u := by
  have hin : HasDerivAt (fun x : ℝ => -(x / 2)) (-(1 / 2)) u :=
    ((hasDerivAt_id u).div_const 2).neg
  exact (Real.hasDerivAt_exp _).comp u hin

theorem hasDerivAt_exp_neg_three_half (u : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (-(3 * u / 2))) (Real.exp (-(3 * u / 2)) * (-(3 / 2))) u := by
  have hin : HasDerivAt (fun x : ℝ => -(3 * x / 2)) (-(3 / 2)) u := by
    have h := (((hasDerivAt_id u).const_mul 3).div_const 2).neg
    refine h.congr_deriv ?_
    ring
  exact (Real.hasDerivAt_exp _).comp u hin

theorem hasDerivAt_linear_factor (T u : ℝ) :
    HasDerivAt (fun u : ℝ => -(1 / 2) - T ^ 2 * u / 2) (-(T ^ 2 / 2)) u := by
  have h := (((hasDerivAt_id u).const_mul (T ^ 2)).div_const 2).const_sub (-(1 / 2))
  refine h.congr_deriv ?_
  ring

/-- `h₀(u) = e^{−u/2} k_T(u)`. -/
def kerH0 (T u : ℝ) : ℝ := Real.exp (-(u / 2)) * gaussDensity T u

/-- `h₀' = e^{−u/2} (−½ − T²u/2) k_T`. -/
def kerA1 (T u : ℝ) : ℝ := Real.exp (-(u / 2)) * (-(1 / 2) - T ^ 2 * u / 2) * gaussDensity T u

/-- `h₁(u) = e^{−3u/2} (−½ − T²u/2) k_T(u)`. -/
def kerH1 (T u : ℝ) : ℝ :=
  Real.exp (-(3 * u / 2)) * (-(1 / 2) - T ^ 2 * u / 2) * gaussDensity T u

/-- `h₁' = e^{−3u/2} (¾ − T²/2 + T²u + T⁴u²/4) k_T`. -/
def kerA2 (T u : ℝ) : ℝ :=
  Real.exp (-(3 * u / 2)) * (3 / 4 - T ^ 2 / 2 + T ^ 2 * u + T ^ 4 * u ^ 2 / 4) * gaussDensity T u

theorem hasDerivAt_kerH0 (T u : ℝ) : HasDerivAt (kerH0 T) (kerA1 T u) u := by
  have h := (hasDerivAt_exp_neg_half u).mul (hasDerivAt_gaussDensity T u)
  refine h.congr_deriv ?_
  unfold kerA1
  ring

theorem hasDerivAt_kerH1 (T u : ℝ) : HasDerivAt (kerH1 T) (kerA2 T u) u := by
  have h := ((hasDerivAt_exp_neg_three_half u).mul (hasDerivAt_linear_factor T u)).mul
    (hasDerivAt_gaussDensity T u)
  refine h.congr_deriv ?_
  unfold kerA2
  simp only [Pi.mul_apply]
  ring

/-- The phase `e^{2πi y eᵘ}`. -/
def kerPhase (y u : ℝ) : ℂ := cexp (((2 * Real.pi * y * Real.exp u : ℝ) : ℂ) * I)

theorem norm_kerPhase (y u : ℝ) : ‖kerPhase y u‖ = 1 := by
  unfold kerPhase
  rw [Complex.norm_exp_ofReal_mul_I]

theorem continuous_kerPhase (y : ℝ) : Continuous (kerPhase y) := by
  unfold kerPhase
  fun_prop

theorem hasDerivAt_kerPhase (y u : ℝ) :
    HasDerivAt (kerPhase y) (((2 * Real.pi * y * Real.exp u : ℝ) : ℂ) * I * kerPhase y u) u := by
  have h : HasDerivAt (fun u : ℝ => ((2 * Real.pi * y * Real.exp u : ℝ) : ℂ) * I)
      (((2 * Real.pi * y * Real.exp u : ℝ) : ℂ) * I) u :=
    ((Real.hasDerivAt_exp u).const_mul (2 * Real.pi * y)).ofReal_comp.mul_const I
  refine h.cexp.congr_deriv ?_
  unfold kerPhase
  ring

theorem kerPhase_re (y u : ℝ) : (kerPhase y u).re = Real.cos (2 * Real.pi * y * Real.exp u) := by
  unfold kerPhase
  exact Complex.exp_ofReal_mul_I_re _

theorem integrable_of_norm_le_quadratic {T : ℝ} (hT : 1 ≤ T) {F : ℝ → ℂ} (hF : Continuous F)
    (A B C c : ℝ) (h : ∀ u, ‖F u‖ ≤ (A + B * |u| + C * u ^ 2) * Real.exp (c * |u|) * gaussDensity T u) :
    Integrable F :=
  (integrable_quadratic_moment A B C c hT).mono' hF.aestronglyMeasurable (Eventually.of_forall h)

theorem exp_neg_half_le (u : ℝ) : Real.exp (-(u / 2)) ≤ Real.exp ((1 / 2) * |u|) :=
  Real.exp_le_exp.mpr (by linarith [neg_abs_le u])

theorem exp_neg_three_half_le (u : ℝ) : Real.exp (-(3 * u / 2)) ≤ Real.exp ((3 / 2) * |u|) :=
  Real.exp_le_exp.mpr (by linarith [neg_abs_le u])

theorem abs_linear_le (T u : ℝ) : |-(1 / 2) - T ^ 2 * u / 2| ≤ 1 / 2 + T ^ 2 / 2 * |u| := by
  have h1 : |T ^ 2 * u / 2| = T ^ 2 / 2 * |u| := by
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg T), abs_two]; ring
  calc |-(1 / 2) - T ^ 2 * u / 2| ≤ |-(1 / 2 : ℝ)| + |T ^ 2 * u / 2| := abs_sub _ _
    _ = _ := by rw [h1]; norm_num

theorem abs_quadratic_le (T u : ℝ) :
    |3 / 4 - T ^ 2 / 2 + T ^ 2 * u + T ^ 4 * u ^ 2 / 4| ≤
      (3 / 4 + T ^ 2 / 2) + T ^ 2 * |u| + T ^ 4 / 4 * u ^ 2 := by
  have h1 : |T ^ 2 * u| = T ^ 2 * |u| := by rw [abs_mul, abs_of_nonneg (sq_nonneg T)]
  have h2 : |T ^ 4 * u ^ 2 / 4| = T ^ 4 / 4 * u ^ 2 := by
    rw [abs_of_nonneg (by positivity)]; ring
  have h3 : |3 / 4 - T ^ 2 / 2| ≤ 3 / 4 + T ^ 2 / 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg T]
  calc _ ≤ |3 / 4 - T ^ 2 / 2| + |T ^ 2 * u| + |T ^ 4 * u ^ 2 / 4| := abs_add_three _ _ _
    _ ≤ _ := by rw [h1, h2]; linarith

theorem norm_kerH0_le {T : ℝ} (hT : 0 ≤ T) (u : ℝ) :
    ‖((kerH0 T u : ℝ) : ℂ)‖ ≤ (1 + 0 * |u| + 0 * u ^ 2) * Real.exp ((1 / 2) * |u|) *
      gaussDensity T u := by
  have hk := gaussDensity_nonneg hT u
  rw [Complex.norm_real, Real.norm_eq_abs, kerH0, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg hk]
  have := exp_neg_half_le u
  nlinarith

theorem norm_kerA1_le {T : ℝ} (hT : 0 ≤ T) (u : ℝ) :
    ‖((kerA1 T u : ℝ) : ℂ)‖ ≤ (1 / 2 + T ^ 2 / 2 * |u| + 0 * u ^ 2) * Real.exp ((1 / 2) * |u|) *
      gaussDensity T u := by
  have hk := gaussDensity_nonneg hT u
  rw [Complex.norm_real, Real.norm_eq_abs, kerA1, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg hk]
  have h1 := exp_neg_half_le u
  have h2 := abs_linear_le T u
  calc Real.exp (-(u / 2)) * |-(1 / 2) - T ^ 2 * u / 2| * gaussDensity T u
      ≤ Real.exp ((1 / 2) * |u|) * (1 / 2 + T ^ 2 / 2 * |u|) * gaussDensity T u := by gcongr
    _ = _ := by ring

theorem norm_kerH1_le {T : ℝ} (hT : 0 ≤ T) (u : ℝ) :
    ‖((kerH1 T u : ℝ) : ℂ)‖ ≤ (1 / 2 + T ^ 2 / 2 * |u| + 0 * u ^ 2) * Real.exp ((3 / 2) * |u|) *
      gaussDensity T u := by
  have hk := gaussDensity_nonneg hT u
  rw [Complex.norm_real, Real.norm_eq_abs, kerH1, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg hk]
  have h1 := exp_neg_three_half_le u
  have h2 := abs_linear_le T u
  calc Real.exp (-(3 * u / 2)) * |-(1 / 2) - T ^ 2 * u / 2| * gaussDensity T u
      ≤ Real.exp ((3 / 2) * |u|) * (1 / 2 + T ^ 2 / 2 * |u|) * gaussDensity T u := by gcongr
    _ = _ := by ring

theorem norm_kerA2_le {T : ℝ} (hT : 0 ≤ T) (u : ℝ) :
    ‖((kerA2 T u : ℝ) : ℂ)‖ ≤ ((3 / 4 + T ^ 2 / 2) + T ^ 2 * |u| + T ^ 4 / 4 * u ^ 2) *
      Real.exp ((3 / 2) * |u|) * gaussDensity T u := by
  have hk := gaussDensity_nonneg hT u
  rw [Complex.norm_real, Real.norm_eq_abs, kerA2, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg hk]
  have h1 := exp_neg_three_half_le u
  have h2 := abs_quadratic_le T u
  calc Real.exp (-(3 * u / 2)) * |3 / 4 - T ^ 2 / 2 + T ^ 2 * u + T ^ 4 * u ^ 2 / 4| *
        gaussDensity T u
      ≤ Real.exp ((3 / 2) * |u|) * ((3 / 4 + T ^ 2 / 2) + T ^ 2 * |u| + T ^ 4 / 4 * u ^ 2) *
          gaussDensity T u := by gcongr
    _ = _ := by ring

theorem continuous_kerH0 (T : ℝ) : Continuous (kerH0 T) := by
  unfold kerH0; have := continuous_gaussDensity T; fun_prop

theorem continuous_kerA1 (T : ℝ) : Continuous (kerA1 T) := by
  unfold kerA1; have := continuous_gaussDensity T; fun_prop

theorem continuous_kerH1 (T : ℝ) : Continuous (kerH1 T) := by
  unfold kerH1; have := continuous_gaussDensity T; fun_prop

theorem continuous_kerA2 (T : ℝ) : Continuous (kerA2 T) := by
  unfold kerA2; have := continuous_gaussDensity T; fun_prop

/-- The phase derivative is `2πi y eᵘ` times the phase; `|2πy eᵘ| ≤ 2π|y| e^{|u|}`. -/
theorem norm_phase_deriv_mul_le (y u : ℝ) (r : ℝ) :
    ‖((r : ℝ) : ℂ) * (((2 * Real.pi * y * Real.exp u : ℝ) : ℂ) * I * kerPhase y u)‖ =
      |r| * (2 * Real.pi * |y| * Real.exp u) := by
  rw [norm_mul, norm_mul, norm_mul, norm_kerPhase, Complex.norm_I, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_pos (Real.exp_pos u), abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  ring

/-- **First integration by parts**: `2πiy ∫ e^{u/2} k_T · φ = −∫ h₀' · φ`. -/
theorem integral_ibp_first {T : ℝ} (hT : 1 ≤ T) (y : ℝ) :
    ((2 * Real.pi * y : ℝ) : ℂ) * I *
        ∫ u : ℝ, ((Real.exp (u / 2) * gaussDensity T u : ℝ) : ℂ) * kerPhase y u =
      -∫ u : ℝ, ((kerA1 T u : ℝ) : ℂ) * kerPhase y u := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun u => ((kerH0 T u : ℝ) : ℂ)) (v := kerPhase y)
    (u' := fun u => ((kerA1 T u : ℝ) : ℂ))
    (v' := fun u => ((2 * Real.pi * y * Real.exp u : ℝ) : ℂ) * I * kerPhase y u)
    (fun u _ => (hasDerivAt_kerH0 T u).ofReal_comp) (fun u _ => hasDerivAt_kerPhase y u)
    (integrable_of_norm_le_quadratic hT
      (by have := continuous_kerH0 T; have := continuous_kerPhase y; fun_prop)
      (2 * Real.pi * |y|) 0 0 (1 / 2) fun u => by
        simp only [Pi.mul_apply]
        rw [norm_phase_deriv_mul_le, kerH0, abs_mul, abs_of_pos (Real.exp_pos _),
          abs_of_nonneg (gaussDensity_nonneg hT0 u)]
        have he : Real.exp (-(u / 2)) * Real.exp u = Real.exp (u / 2) := by
          rw [← Real.exp_add]; congr 1; ring
        have h1 := abs_exp_half_le u
        have hk := gaussDensity_nonneg hT0 u
        calc Real.exp (-(u / 2)) * gaussDensity T u * (2 * Real.pi * |y| * Real.exp u)
            = 2 * Real.pi * |y| * (Real.exp (u / 2) * gaussDensity T u) := by rw [← he]; ring
          _ ≤ 2 * Real.pi * |y| * (Real.exp ((1 / 2) * |u|) * gaussDensity T u) := by gcongr
          _ = _ := by ring)
    (integrable_of_norm_le_quadratic hT
      (by have := continuous_kerA1 T; have := continuous_kerPhase y; fun_prop)
      (1 / 2) (T ^ 2 / 2) 0 (1 / 2) fun u => by
        simp only [Pi.mul_apply]
        rw [norm_mul, norm_kerPhase, mul_one]
        exact norm_kerA1_le hT0 u)
    (integrable_of_norm_le_quadratic hT
      (by have := continuous_kerH0 T; have := continuous_kerPhase y; fun_prop)
      1 0 0 (1 / 2) fun u => by
        simp only [Pi.mul_apply]
        rw [norm_mul, norm_kerPhase, mul_one]
        exact norm_kerH0_le hT0 u)
  rw [← hibp, ← integral_const_mul]
  congr 1
  funext u
  have he : Real.exp (-(u / 2)) * Real.exp u = Real.exp (u / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [kerH0]
  rw [← he]
  push_cast
  ring

/-- **Second integration by parts**: `2πiy ∫ h₀' · φ = −∫ h₁' · φ`. -/
theorem integral_ibp_second {T : ℝ} (hT : 1 ≤ T) (y : ℝ) :
    ((2 * Real.pi * y : ℝ) : ℂ) * I * ∫ u : ℝ, ((kerA1 T u : ℝ) : ℂ) * kerPhase y u =
      -∫ u : ℝ, ((kerA2 T u : ℝ) : ℂ) * kerPhase y u := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun u => ((kerH1 T u : ℝ) : ℂ)) (v := kerPhase y)
    (u' := fun u => ((kerA2 T u : ℝ) : ℂ))
    (v' := fun u => ((2 * Real.pi * y * Real.exp u : ℝ) : ℂ) * I * kerPhase y u)
    (fun u _ => (hasDerivAt_kerH1 T u).ofReal_comp) (fun u _ => hasDerivAt_kerPhase y u)
    (integrable_of_norm_le_quadratic hT
      (by have := continuous_kerH1 T; have := continuous_kerPhase y; fun_prop)
      (2 * Real.pi * |y| * (1 / 2)) (2 * Real.pi * |y| * (T ^ 2 / 2)) 0 (1 / 2) fun u => by
        simp only [Pi.mul_apply]
        rw [norm_phase_deriv_mul_le, kerH1, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
          abs_of_nonneg (gaussDensity_nonneg hT0 u)]
        have he : Real.exp (-(3 * u / 2)) * Real.exp u = Real.exp (-(u / 2)) := by
          rw [← Real.exp_add]; congr 1; ring
        have h1 := exp_neg_half_le u
        have h2 := abs_linear_le T u
        have hk := gaussDensity_nonneg hT0 u
        have hy : 0 ≤ 2 * Real.pi * |y| := by positivity
        calc Real.exp (-(3 * u / 2)) * |-(1 / 2) - T ^ 2 * u / 2| * gaussDensity T u *
              (2 * Real.pi * |y| * Real.exp u)
            = 2 * Real.pi * |y| * (Real.exp (-(u / 2)) * |-(1 / 2) - T ^ 2 * u / 2| *
                gaussDensity T u) := by rw [← he]; ring
          _ ≤ 2 * Real.pi * |y| * (Real.exp ((1 / 2) * |u|) * (1 / 2 + T ^ 2 / 2 * |u|) *
                gaussDensity T u) := by gcongr
          _ = _ := by ring)
    (integrable_of_norm_le_quadratic hT
      (by have := continuous_kerA2 T; have := continuous_kerPhase y; fun_prop)
      (3 / 4 + T ^ 2 / 2) (T ^ 2) (T ^ 4 / 4) (3 / 2) fun u => by
        simp only [Pi.mul_apply]
        rw [norm_mul, norm_kerPhase, mul_one]
        exact norm_kerA2_le hT0 u)
    (integrable_of_norm_le_quadratic hT
      (by have := continuous_kerH1 T; have := continuous_kerPhase y; fun_prop)
      (1 / 2) (T ^ 2 / 2) 0 (3 / 2) fun u => by
        simp only [Pi.mul_apply]
        rw [norm_mul, norm_kerPhase, mul_one]
        exact norm_kerH1_le hT0 u)
  rw [← hibp, ← integral_const_mul]
  congr 1
  funext u
  have he : Real.exp (-(3 * u / 2)) * Real.exp u = Real.exp (-(u / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [kerH1, kerA1]
  rw [← he]
  push_cast
  ring

/-- `J_T(y) = 2 Re ∫ e^{u/2} k_T(u) e^{2πiy eᵘ} du`. -/
theorem leftKernel_eq_re (T y : ℝ) (hT : 1 ≤ T) :
    leftKernel T y =
      2 * (∫ u : ℝ, ((Real.exp (u / 2) * gaussDensity T u : ℝ) : ℂ) * kerPhase y u).re := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hint : Integrable (fun u : ℝ => ((Real.exp (u / 2) * gaussDensity T u : ℝ) : ℂ) *
      kerPhase y u) := by
    refine integrable_of_norm_le_quadratic hT
      (by have := continuous_gaussDensity T; have := continuous_kerPhase y; fun_prop)
      1 0 0 (1 / 2) fun u => ?_
    rw [norm_mul, norm_kerPhase, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _), abs_of_nonneg (gaussDensity_nonneg hT0 u)]
    have := abs_exp_half_le u
    have hk := gaussDensity_nonneg hT0 u
    nlinarith
  rw [show (∫ u : ℝ, ((Real.exp (u / 2) * gaussDensity T u : ℝ) : ℂ) * kerPhase y u).re =
    ∫ u : ℝ, (((Real.exp (u / 2) * gaussDensity T u : ℝ) : ℂ) * kerPhase y u).re from
      (integral_re hint).symm, ← integral_const_mul]
  unfold leftKernel
  congr 1
  funext u
  rw [Complex.re_ofReal_mul, kerPhase_re]
  ring

/-- **Decay of the kernel**: `|J_T(y)| ≤ C T²/y²` for `T ≥ 1`, `y > 0`. -/
theorem exists_abs_leftKernel_le_sq :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → ∀ y : ℝ, 0 < y → |leftKernel T y| ≤ C * T ^ 2 / y ^ 2 := by
  set K : ℝ := Real.sqrt 2 * Real.exp (4 + 4 * (3 / 2) ^ 2) with hK
  refine ⟨2 * K * (11 / 4) / (4 * Real.pi ^ 2), by positivity, fun T hT y hy => ?_⟩
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hI1 := integral_ibp_first hT y
  have hI2 := integral_ibp_second hT y
  set P : ℂ := ∫ u : ℝ, ((Real.exp (u / 2) * gaussDensity T u : ℝ) : ℂ) * kerPhase y u with hP
  set Q : ℂ := ∫ u : ℝ, ((kerA2 T u : ℝ) : ℂ) * kerPhase y u with hQ
  have hc : ((2 * Real.pi * y : ℝ) : ℂ) * I ≠ 0 := by
    apply mul_ne_zero _ Complex.I_ne_zero
    exact_mod_cast (by positivity : (2 * Real.pi * y) ≠ 0)
  have hPQ : (((2 * Real.pi * y : ℝ) : ℂ) * I) ^ 2 * P = Q := by
    rw [sq, mul_assoc, hI1, mul_neg, hI2, neg_neg]
  have hnormc : ‖((2 * Real.pi * y : ℝ) : ℂ) * I‖ = 2 * Real.pi * y := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  have hPnorm : ‖P‖ = ‖Q‖ / (2 * Real.pi * y) ^ 2 := by
    rw [← hPQ, norm_mul, norm_pow, hnormc]
    field_simp
  have hQle : ‖Q‖ ≤ K * ((3 / 4 + T ^ 2 / 2) + T ^ 2 / T + 2 * (T ^ 4 / 4) / T ^ 2) := by
    refine (norm_integral_le_of_norm_le (integrable_quadratic_moment (3 / 4 + T ^ 2 / 2) (T ^ 2)
      (T ^ 4 / 4) (3 / 2) hT) (Eventually.of_forall fun u => ?_)).trans ?_
    · rw [norm_mul, norm_kerPhase, mul_one]
      exact norm_kerA2_le hT0 u
    · have := integral_quadratic_moment_le (A := 3 / 4 + T ^ 2 / 2) (B := T ^ 2) (C := T ^ 4 / 4)
        (by positivity) (by positivity) (by positivity) (3 / 2) hT
      rw [hK]
      linarith
  have hsimp : (3 / 4 + T ^ 2 / 2) + T ^ 2 / T + 2 * (T ^ 4 / 4) / T ^ 2 ≤ 11 / 4 * T ^ 2 := by
    have hTpos : 0 < T := by linarith
    have e1 : T ^ 2 / T = T := by field_simp
    have e2 : 2 * (T ^ 4 / 4) / T ^ 2 = T ^ 2 / 2 := by field_simp; ring
    rw [e1, e2]
    nlinarith
  rw [leftKernel_eq_re T y hT, ← hP, abs_mul, abs_two]
  have hre : |P.re| ≤ ‖P‖ := Complex.abs_re_le_norm P
  have hKp : 0 ≤ K := by positivity
  have hQ' : ‖Q‖ ≤ K * (11 / 4 * T ^ 2) := hQle.trans (mul_le_mul_of_nonneg_left hsimp hKp)
  have hy2 : 0 < (2 * Real.pi * y) ^ 2 := by positivity
  calc 2 * |P.re| ≤ 2 * ‖P‖ := by linarith
    _ = 2 * (‖Q‖ / (2 * Real.pi * y) ^ 2) := by rw [hPnorm]
    _ ≤ 2 * (K * (11 / 4 * T ^ 2) / (2 * Real.pi * y) ^ 2) := by gcongr
    _ = 2 * K * (11 / 4) / (4 * Real.pi ^ 2) * T ^ 2 / y ^ 2 := by
        field_simp
        ring

/-! ## The exact left-line identity -/

/-- The point `−½ + it` of the left line. -/
abbrev leftPt (t : ℝ) : ℂ := (-1 / 2 : ℂ) + (t : ℂ) * I

/-- Its reflection `w = 1 − (−½ + it) = 3/2 − it`. -/
abbrev leftDual (t : ℝ) : ℂ := (3 / 2 : ℂ) - (t : ℂ) * I

theorem one_sub_leftPt (t : ℝ) : 1 - leftPt t = leftDual t := by
  simp only [leftPt, leftDual]; ring

theorem leftDual_re (t : ℝ) : (leftDual t).re = 3 / 2 := by simp [leftDual]

theorem leftDual_im (t : ℝ) : (leftDual t).im = -t := by simp [leftDual]

/-- `(r·z)^{−w} = r^{−w} z^{−w}` for `r > 0`, written through the logarithm. -/
theorem cpow_neg_ofReal_mul (r : ℝ) (hr : 0 < r) {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    ((r : ℂ) * z) ^ (-w) = cexp (-w * Real.log r) * cexp (Complex.log z * (-w)) := by
  have hrz : (r : ℂ) * z ≠ 0 := mul_ne_zero (by exact_mod_cast hr.ne') hz
  rw [Complex.cpow_def_of_ne_zero hrz, Complex.log_ofReal_mul hr hz, ← Complex.exp_add]
  congr 1
  ring

/-- **The Gamma form of `χ` on the left line**: for `y > 0`,
`χ(−½+it) y^{−½+it} = y Γ(w) [(−2πiy)^{−w} + (2πiy)^{−w}]`, `w = 3/2 − it`. -/
theorem zetaChi_mul_cpow_eq (t : ℝ) {y : ℝ} (hy : 0 < y) :
    zetaChi (leftPt t) * (y : ℂ) ^ leftPt t =
      (y : ℂ) * (Complex.Gamma (leftDual t) *
        ((((2 * Real.pi * y : ℝ) : ℂ) * (-I)) ^ (-leftDual t) +
          (((2 * Real.pi * y : ℝ) : ℂ) * I) ^ (-leftDual t))) := by
  set w := leftDual t with hw
  have hpos : 0 < 2 * Real.pi * y := by positivity
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  -- `χ(s) = Γℝ(w)/Γℝ(1 − w) = Γℂ(w) cos(πw/2)`
  have hchi : zetaChi (leftPt t) = Complex.Gammaℂ w * Complex.cos (Real.pi * w / 2) := by
    unfold zetaChi
    have h1 : 1 - leftPt t = w := one_sub_leftPt t
    have h2 : leftPt t = 1 - w := by rw [← h1]; ring
    rw [h1, h2]
    apply Complex.Gammaℝ_div_Gammaℝ_one_sub
    intro n hn
    have := congrArg Complex.re hn
    rw [hw, leftDual_re] at this
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  -- `y^{−½+it} = y · y^{−w}`
  have hys : (y : ℂ) ^ leftPt t = (y : ℂ) * (y : ℂ) ^ (-w) := by
    have h2 : leftPt t = 1 - w := by rw [hw, ← one_sub_leftPt t]; ring
    rw [h2, Complex.cpow_sub _ _ hy0, Complex.cpow_one, Complex.cpow_neg, div_eq_mul_inv]
  have hm : (((2 * Real.pi * y : ℝ) : ℂ) * (-I)) ^ (-w) =
      cexp (-w * Real.log (2 * Real.pi * y)) * cexp (Real.pi / 2 * I * w) := by
    rw [cpow_neg_ofReal_mul _ hpos (by simp) w, Complex.log_neg_I]
    congr 1
    ring_nf
  have hp : (((2 * Real.pi * y : ℝ) : ℂ) * I) ^ (-w) =
      cexp (-w * Real.log (2 * Real.pi * y)) * cexp (-(Real.pi / 2 * I * w)) := by
    rw [cpow_neg_ofReal_mul _ hpos Complex.I_ne_zero w, Complex.log_I]
    congr 1
    ring_nf
  have hsplit : cexp (-w * Real.log (2 * Real.pi * y)) =
      (2 * Real.pi : ℂ) ^ (-w) * (y : ℂ) ^ (-w) := by
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    rw [show ((2 * Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.cpow_def_of_ne_zero (by exact_mod_cast h2pi.ne'),
      Complex.cpow_def_of_ne_zero hy0, ← Complex.exp_add, ← Complex.ofReal_log h2pi.le,
      ← Complex.ofReal_log hy.le, Real.log_mul h2pi.ne' hy.ne']
    congr 1
    push_cast
    ring
  rw [hchi, hys, hm, hp, hsplit, Complex.Gammaℂ_def]
  have hcos : 2 * Complex.cos (Real.pi * w / 2) =
      cexp (Real.pi / 2 * I * w) + cexp (-(Real.pi / 2 * I * w)) := by
    rw [Complex.two_cos]
    congr 1 <;> congr 1 <;> ring
  linear_combination (Complex.Gamma w * (2 * Real.pi : ℂ) ^ (-w) * (y : ℂ) ^ (-w) * (y : ℂ)) * hcos

/-- The inverse Mellin transform of `g_T` along `Re w = 3/2` is log-normal:
`∫ x^{3/2−it} g_T(−½+it) dt = √π T e^{L/2 − T²L²/4}`, `L = log x`. -/
theorem integral_cpow_leftDual_mul_gaussWeight {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    ∫ t : ℝ, (x : ℂ) ^ leftDual t * gaussWeight T (leftPt t) =
      ((Real.sqrt Real.pi * T : ℝ) : ℂ) *
        cexp (((Real.log x / 2 - T ^ 2 * Real.log x ^ 2 / 4 : ℝ) : ℂ)) := by
  set L : ℝ := Real.log x with hL
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hint : ∀ t : ℝ, (x : ℂ) ^ leftDual t * gaussWeight T (leftPt t) =
      cexp ((-1 / (T : ℂ) ^ 2) * (t : ℂ) ^ 2 + (-(I * ((L : ℂ) + 2 / (T : ℂ) ^ 2))) * t +
        (1 / (T : ℂ) ^ 2 + 3 / 2 * L)) := by
    intro t
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le,
      gaussWeight, ← Complex.exp_add]
    congr 1
    simp only [leftDual, leftPt]
    linear_combination ((t : ℂ) ^ 2 / (T : ℂ) ^ 2) * Complex.I_sq
  simp_rw [hint]
  have hb : (-1 / (T : ℂ) ^ 2).re < 0 := by
    rw [show (-1 / (T : ℂ) ^ 2) = ((-1 / T ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
    have : 0 < T ^ 2 := by positivity
    exact div_neg_of_neg_of_pos (by norm_num) this
  rw [integral_cexp_quadratic hb]
  have hsq : ((Real.pi : ℂ) / -(-1 / (T : ℂ) ^ 2)) ^ (1 / 2 : ℂ) =
      ((Real.sqrt Real.pi * T : ℝ) : ℂ) := by
    rw [show ((Real.pi : ℂ) / -(-1 / (T : ℂ) ^ 2)) = ((Real.pi * T ^ 2 : ℝ) : ℂ) by
      push_cast; field_simp]
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_mul Real.pi_pos.le,
      Real.sqrt_sq hT.le]
  rw [hsq]
  congr 1
  congr 1
  rw [neg_sq, mul_pow, Complex.I_sq]
  push_cast
  field_simp
  ring

/-- Change of variables `x = eᵘ` on the positive half-line. -/
theorem integral_Ioi_eq_integral_exp_smul' (g : ℝ → ℂ) :
    (∫ x in Ioi (0 : ℝ), g x) = ∫ u : ℝ, Real.exp u • g (Real.exp u) := by
  rw [← Real.range_exp, ← Set.image_univ]
  simpa only [Measure.restrict_univ, abs_of_pos (Real.exp_pos _)] using
    (MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (s := Set.univ) MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn g)

theorem norm_gaussWeight_leftPt (T t : ℝ) :
    ‖gaussWeight T (leftPt t)‖ = Real.exp ((1 - t ^ 2) / T ^ 2) := by
  unfold gaussWeight leftPt
  rw [Complex.norm_exp]
  congr 1
  have e : ((-1 / 2 : ℂ) + (t : ℂ) * I - 1 / 2) ^ 2 =
      ((1 - t ^ 2 : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I := by
    push_cast
    linear_combination ((t : ℂ) ^ 2) * Complex.I_sq
  rw [e, show (T : ℂ) ^ 2 = ((T ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_re]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  ring

theorem integrable_exp_one_sub_sq_div {T : ℝ} (hT : 0 < T) :
    Integrable (fun t : ℝ => Real.exp ((1 - t ^ 2) / T ^ 2)) := by
  have h := (integrable_exp_neg_mul_sq (b := 1 / T ^ 2) (by positivity)).const_mul
    (Real.exp (1 / T ^ 2))
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only
  rw [← Real.exp_add]
  congr 1
  ring

/-- **Euler integral against the Gaussian weight**: for `Re a > 0`,
`∫ Γ(w) a^{−w} g_T(−½+it) dt = 2π ∫ e^{−a eᵘ} e^{u/2} k_T(u) du`, `w = 3/2 − it`. -/
theorem integral_Gamma_mul_cpow_mul_gaussWeight {T : ℝ} (hT : 0 < T) {a : ℂ} (ha : 0 < a.re) :
    ∫ t : ℝ, Complex.Gamma (leftDual t) * a ^ (-leftDual t) * gaussWeight T (leftPt t) =
      2 * Real.pi * ∫ u : ℝ, cexp (-(a * (Real.exp u : ℂ))) *
        ((Real.exp (u / 2) * gaussDensity T u : ℝ) : ℂ) := by
  set F : ℝ → ℝ → ℂ := fun t x =>
    (x : ℂ) ^ (leftDual t - 1) * cexp (-(a * x)) * gaussWeight T (leftPt t) with hF
  -- the Euler integral, pointwise in `t`
  have hEuler : ∀ t : ℝ, Complex.Gamma (leftDual t) * a ^ (-leftDual t) * gaussWeight T (leftPt t) =
      ∫ x in Ioi (0 : ℝ), F t x := by
    intro t
    rw [← GaloisForLFunctions.HTGeometry.integral_cpow_mul_exp_neg_mul_Ioi
      (by rw [leftDual_re]; norm_num) ha, ← integral_mul_const]
  simp_rw [hEuler]
  -- Fubini
  have hint : Integrable (Function.uncurry F) ((volume : Measure ℝ).prod
      ((volume : Measure ℝ).restrict (Ioi 0))) := by
    have hB := (integrable_exp_one_sub_sq_div hT).mul_prod
      (GaloisForLFunctions.HTGeometry.integrableOn_rpow_mul_exp_neg_mul_Ioi (σ := 1 / 2)
        (by norm_num) ha)
    refine hB.mono' ?_ ?_
    · apply Measurable.aestronglyMeasurable
      simp only [hF, Function.uncurry_def, gaussWeight, leftDual, leftPt]
      fun_prop
    · have hpos : ∀ᵐ p ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0))),
          0 < p.2 :=
        Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)
      filter_upwards [hpos] with p hp
      simp only [hF, Function.uncurry_def]
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp, norm_gaussWeight_leftPt,
        Complex.norm_exp]
      have h1 : (leftDual p.1 - 1).re = 1 / 2 := by rw [Complex.sub_re, leftDual_re]; norm_num
      have h2 : (-(a * (p.2 : ℂ))).re = -(a.re * p.2) := by simp
      rw [h1, h2]
      apply le_of_eq
      ring
  rw [integral_integral_swap hint]
  -- the inner Gaussian integral
  have hinner : ∀ x ∈ Ioi (0 : ℝ), ∫ t : ℝ, F t x =
      cexp (-(a * x)) * (x : ℂ)⁻¹ * (((Real.sqrt Real.pi * T : ℝ) : ℂ) *
        cexp (((Real.log x / 2 - T ^ 2 * Real.log x ^ 2 / 4 : ℝ) : ℂ))) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
    rw [← integral_cpow_leftDual_mul_gaussWeight hT hx, ← integral_const_mul]
    congr 1
    funext t
    simp only [hF]
    rw [Complex.cpow_sub _ _ hx0, Complex.cpow_one]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hinner, integral_Ioi_eq_integral_exp_smul',
    ← integral_const_mul]
  congr 1
  funext u
  rw [Real.log_exp]
  have hsqrt : Real.sqrt Real.pi * T = 2 * Real.pi * (T / (2 * Real.sqrt Real.pi)) := by
    have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    field_simp
    rw [Real.sq_sqrt Real.pi_pos.le]
  have hexp : cexp (((u / 2 - T ^ 2 * u ^ 2 / 4 : ℝ) : ℂ)) =
      ((Real.exp (u / 2) * Real.exp (-(T ^ 2 * u ^ 2 / 4)) : ℝ) : ℂ) := by
    rw [← Real.exp_add, Complex.ofReal_exp]
    congr 2
  rw [hexp, hsqrt, Complex.real_smul]
  have he : (Real.exp u : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos u).ne'
  unfold gaussDensity
  push_cast
  field_simp

/-- `|Γ(3/2 − it)| e^{π|t|/2} ≤ (½ + |t|) √(2π)`. -/
theorem norm_Gamma_leftDual_mul_exp_le (t : ℝ) :
    ‖Complex.Gamma (leftDual t)‖ * Real.exp (Real.pi / 2 * |t|) ≤ (1 / 2 + |t|) * Real.sqrt (2 * Real.pi) := by
  have hz : (1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hrec : Complex.Gamma (leftDual t) =
      ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I) * Complex.Gamma ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I) := by
    rw [← Complex.Gamma_add_one _ hz]
    congr 1
    simp only [leftDual]
    push_cast
    ring
  have hsq := GaloisForLFunctions.HTGeometry.norm_Gamma_half_add_I_sq (-t)
  rw [mul_neg, Real.cosh_neg] at hsq
  have hcosh : Real.exp (Real.pi * |t|) / 2 ≤ Real.cosh (Real.pi * t) := by
    rw [Real.cosh_eq]
    have := Real.exp_abs_le (Real.pi * t)
    rw [abs_mul, abs_of_pos Real.pi_pos] at this
    linarith
  have hcpos : 0 < Real.cosh (Real.pi * t) := Real.cosh_pos _
  have hG : ‖Complex.Gamma ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I)‖ ^ 2 *
      Real.exp (Real.pi / 2 * |t|) ^ 2 ≤ 2 * Real.pi := by
    rw [hsq, ← Real.exp_nat_mul]
    push_cast
    rw [show (2 : ℝ) * (Real.pi / 2 * |t|) = Real.pi * |t| by ring, div_mul_eq_mul_div,
      div_le_iff₀ hcpos]
    nlinarith [Real.pi_pos, Real.exp_pos (Real.pi * |t|)]
  have hG' : ‖Complex.Gamma ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I)‖ * Real.exp (Real.pi / 2 * |t|) ≤
      Real.sqrt (2 * Real.pi) := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ ‖Complex.Gamma ((1 / 2 : ℂ) +
      ((-t : ℝ) : ℂ) * I)‖ * Real.exp (Real.pi / 2 * |t|))]
    exact Real.sqrt_le_sqrt (by rw [mul_pow]; exact hG)
  have hn : ‖(1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I‖ ≤ 1 / 2 + |t| := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg]
    norm_num
  rw [hrec, norm_mul, mul_assoc]
  exact mul_le_mul hn hG' (by positivity) (by positivity)

theorem continuous_Gamma_leftDual : Continuous fun t : ℝ => Complex.Gamma (leftDual t) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hd : DifferentiableAt ℂ Complex.Gamma (leftDual t) := by
    apply Complex.differentiableAt_Gamma
    intro m hm
    have := congrArg Complex.re hm
    rw [leftDual_re] at this
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  exact hd.continuousAt.comp (by unfold leftDual; fun_prop)

/-- For `Re z ≥ 0`, `|z^{−w}| ≤ |z|^{−3/2} e^{π|t|/2}` with `w = 3/2 − it`. -/
theorem norm_cpow_neg_leftDual_le {z : ℂ} (hz : 0 ≤ z.re) (t : ℝ) :
    ‖z ^ (-leftDual t)‖ ≤ ‖z‖ ^ (-(3 / 2 : ℝ)) * Real.exp (Real.pi / 2 * |t|) := by
  refine (Complex.norm_cpow_le z _).trans ?_
  have hre : (-leftDual t).re = -(3 / 2) := by rw [Complex.neg_re, leftDual_re]
  have him : (-leftDual t).im = t := by rw [Complex.neg_im, leftDual_im, neg_neg]
  rw [hre, him, div_eq_mul_inv, ← Real.exp_neg]
  gcongr
  have harg := abs_arg_le_pi_div_two_iff.mpr hz
  have := neg_abs_le (z.arg * t)
  rw [abs_mul] at this
  nlinarith [abs_nonneg t, abs_nonneg z.arg]

/-- The left integrand `Γ(w) a^{−w} g_T(−½+it)` is dominated, uniformly in `Re a ≥ 0`, `|a| ≥ r`. -/
theorem norm_Gamma_cpow_gaussWeight_le {T r : ℝ} (hr : 0 < r) {a : ℂ} (ha : 0 ≤ a.re)
    (har : r ≤ ‖a‖) (t : ℝ) :
    ‖Complex.Gamma (leftDual t) * a ^ (-leftDual t) * gaussWeight T (leftPt t)‖ ≤
      r ^ (-(3 / 2 : ℝ)) * ((1 / 2 + |t|) * Real.sqrt (2 * Real.pi)) *
        Real.exp ((1 - t ^ 2) / T ^ 2) := by
  rw [norm_mul, norm_mul, norm_gaussWeight_leftPt]
  have h1 := norm_cpow_neg_leftDual_le ha t
  have h2 := norm_Gamma_leftDual_mul_exp_le t
  have h3 : ‖a‖ ^ (-(3 / 2 : ℝ)) ≤ r ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hr har (by norm_num)
  have hE := Real.exp_pos ((1 - t ^ 2) / T ^ 2)
  calc ‖Complex.Gamma (leftDual t)‖ * ‖a ^ (-leftDual t)‖ * Real.exp ((1 - t ^ 2) / T ^ 2)
      ≤ ‖Complex.Gamma (leftDual t)‖ * (‖a‖ ^ (-(3 / 2 : ℝ)) * Real.exp (Real.pi / 2 * |t|)) *
          Real.exp ((1 - t ^ 2) / T ^ 2) := by gcongr
    _ = ‖a‖ ^ (-(3 / 2 : ℝ)) * (‖Complex.Gamma (leftDual t)‖ * Real.exp (Real.pi / 2 * |t|)) *
          Real.exp ((1 - t ^ 2) / T ^ 2) := by ring
    _ ≤ r ^ (-(3 / 2 : ℝ)) * ((1 / 2 + |t|) * Real.sqrt (2 * Real.pi)) *
          Real.exp ((1 - t ^ 2) / T ^ 2) := by gcongr

theorem integrable_left_bound {T : ℝ} (hT : 0 < T) (r : ℝ) :
    Integrable (fun t : ℝ => r ^ (-(3 / 2 : ℝ)) * ((1 / 2 + |t|) * Real.sqrt (2 * Real.pi)) *
      Real.exp ((1 - t ^ 2) / T ^ 2)) := by
  have h0 := integrable_exp_one_sub_sq_div hT
  have h1 : Integrable (fun t : ℝ => |t| * Real.exp ((1 - t ^ 2) / T ^ 2)) := by
    have h := ((integrable_mul_exp_neg_mul_sq (b := 1 / T ^ 2) (by positivity)).norm).const_mul
      (Real.exp (1 / T ^ 2))
    refine h.congr (Eventually.of_forall fun t => ?_)
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [show (1 - t ^ 2) / T ^ 2 = 1 / T ^ 2 + -(1 / T ^ 2) * t ^ 2 by ring, Real.exp_add]
    ring
  refine ((h0.const_mul (1 / 2)).add h1).const_mul (r ^ (-(3 / 2 : ℝ)) * Real.sqrt (2 * Real.pi))
    |>.congr (Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply]
  ring

theorem continuous_left_integrand (T : ℝ) {a : ℂ} (ha : a ≠ 0) :
    Continuous (fun t : ℝ => Complex.Gamma (leftDual t) * a ^ (-leftDual t) *
      gaussWeight T (leftPt t)) := by
  have h1 := continuous_Gamma_leftDual
  have h2 : Continuous fun t : ℝ => a ^ (-leftDual t) := by
    have : Continuous fun t : ℝ => -leftDual t := by unfold leftDual; fun_prop
    exact this.const_cpow (Or.inl ha)
  have h3 : Continuous fun t : ℝ => gaussWeight T (leftPt t) := by
    unfold gaussWeight leftPt; fun_prop
  exact (h1.mul h2).mul h3

/-- **Boundary values**: the identity of `integral_Gamma_mul_cpow_mul_gaussWeight` persists on
`Re a = 0`, `a ≠ 0`. -/
theorem integral_Gamma_mul_cpow_mul_gaussWeight_of_re_eq_zero {T : ℝ} (hT1 : 1 ≤ T) {a : ℂ}
    (ha : a.re = 0) (ha0 : a ≠ 0) :
    ∫ t : ℝ, Complex.Gamma (leftDual t) * a ^ (-leftDual t) * gaussWeight T (leftPt t) =
      2 * Real.pi * ∫ u : ℝ, cexp (-(a * (Real.exp u : ℂ))) *
        ((Real.exp (u / 2) * gaussDensity T u : ℝ) : ℂ) := by
  have hT : 0 < T := by linarith
  have hr : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have him : a.im ≠ 0 := by
    intro h; apply ha0; exact Complex.ext ha h
  have hslit : a ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inr him)
  -- shifted points `a + ε`
  have hnorm : ∀ ε : ℝ, 0 ≤ ε → ‖a‖ ≤ ‖a + ε‖ := by
    intro ε hε
    rw [Complex.norm_def, Complex.norm_def]
    apply Real.sqrt_le_sqrt
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, ha, add_zero, zero_add]
    nlinarith
  have hre : ∀ ε : ℝ, (a + ε).re = ε := by intro ε; simp [ha]
  have hne : ∀ ε : ℝ, a + ε ≠ 0 := by
    intro ε h
    have := congrArg Complex.im h
    simp at this
    exact him this
  -- the left side is continuous along `ε → 0⁺`
  have hL : Tendsto (fun ε : ℝ => ∫ t : ℝ, Complex.Gamma (leftDual t) * (a + ε) ^ (-leftDual t) *
      gaussWeight T (leftPt t)) (𝓝[>] 0)
      (𝓝 (∫ t : ℝ, Complex.Gamma (leftDual t) * a ^ (-leftDual t) * gaussWeight T (leftPt t))) := by
    refine tendsto_integral_filter_of_dominated_convergence _
      (Eventually.of_forall fun ε => (continuous_left_integrand T (hne ε)).aestronglyMeasurable)
      ?_ (integrable_left_bound hT ‖a‖) ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact Eventually.of_forall fun t =>
        norm_Gamma_cpow_gaussWeight_le hr (by rw [hre]; exact le_of_lt hε) (hnorm ε (le_of_lt hε)) t
    · refine Eventually.of_forall fun t => ?_
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      have hc : ContinuousAt (fun ε : ℝ => Complex.Gamma (leftDual t) * (a + ε) ^ (-leftDual t) *
          gaussWeight T (leftPt t)) 0 := by
        apply ContinuousAt.mul _ continuousAt_const
        apply ContinuousAt.mul continuousAt_const
        have h1 : ContinuousAt (fun ε : ℝ => a + (ε : ℂ)) 0 := by fun_prop
        have h2 : ContinuousAt (fun z : ℂ => z ^ (-leftDual t)) (a + ((0 : ℝ) : ℂ)) := by
          rw [Complex.ofReal_zero, add_zero]
          exact continuousAt_cpow_const hslit
        exact ContinuousAt.comp_of_eq h2 h1 (by simp)
      simpa using hc.tendsto
  -- the right side as well
  have hR : Tendsto (fun ε : ℝ => 2 * Real.pi * ∫ u : ℝ, cexp (-((a + ε) * (Real.exp u : ℂ))) *
      ((Real.exp (u / 2) * gaussDensity T u : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 (2 * Real.pi * ∫ u : ℝ, cexp (-(a * (Real.exp u : ℂ))) *
        ((Real.exp (u / 2) * gaussDensity T u : ℝ) : ℂ))) := by
    have hT0 : (0 : ℝ) ≤ T := hT.le
    refine Tendsto.const_mul _ ?_
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u => Real.exp (u / 2) * gaussDensity T u)
      (Eventually.of_forall fun ε => ?_) ?_ ?_ ?_
    · exact Continuous.aestronglyMeasurable (by
        have := continuous_gaussDensity T
        fun_prop)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      refine Eventually.of_forall fun u => ?_
      rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by have := gaussDensity_nonneg hT0 u; positivity)]
      have : (-((a + ε) * (Real.exp u : ℂ))).re = -(ε * Real.exp u) := by
        rw [Complex.neg_re, Complex.mul_re, hre, Complex.ofReal_re, Complex.ofReal_im]
        ring
      rw [this]
      have hε0 : (0 : ℝ) < ε := hε
      have h1 : Real.exp (-(ε * Real.exp u)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by have := Real.exp_pos u; nlinarith)
      have h2 : 0 ≤ Real.exp (u / 2) * gaussDensity T u := by
        have := gaussDensity_nonneg hT0 u; positivity
      nlinarith
    · refine (integrable_moment_integrand 0 (c := 1 / 2) hT1).mono'
        (by have := continuous_gaussDensity T; fun_prop) (Eventually.of_forall fun u => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by have := gaussDensity_nonneg hT0 u; positivity),
        pow_zero, one_mul]
      exact mul_le_mul_of_nonneg_right (abs_exp_half_le u) (gaussDensity_nonneg hT0 u)
    · refine Eventually.of_forall fun u => ?_
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      have hc : Continuous (fun ε : ℝ => cexp (-((a + ε) * (Real.exp u : ℂ))) *
          ((Real.exp (u / 2) * gaussDensity T u : ℝ) : ℂ)) := by fun_prop
      simpa using hc.tendsto 0
  -- equality for `ε > 0`
  have heq : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (∫ t : ℝ, Complex.Gamma (leftDual t) * (a + ε) ^ (-leftDual t) * gaussWeight T (leftPt t)) =
      2 * Real.pi * ∫ u : ℝ, cexp (-((a + ε) * (Real.exp u : ℂ))) *
        ((Real.exp (u / 2) * gaussDensity T u : ℝ) : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact integral_Gamma_mul_cpow_mul_gaussWeight hT (by rw [hre]; exact hε)
  exact tendsto_nhds_unique (hL.congr' heq) hR

theorem integrable_left_integrand {T : ℝ} (hT : 0 < T) {a : ℂ} (ha : 0 ≤ a.re) (ha0 : a ≠ 0) :
    Integrable (fun t : ℝ => Complex.Gamma (leftDual t) * a ^ (-leftDual t) *
      gaussWeight T (leftPt t)) :=
  (integrable_left_bound hT ‖a‖).mono' (continuous_left_integrand T ha0).aestronglyMeasurable
    (Eventually.of_forall fun t => norm_Gamma_cpow_gaussWeight_le (norm_pos_iff.mpr ha0) ha le_rfl t)

/-- **The exact left-line identity.**  For `T ≥ 1` and `y > 0`,
`∫ χ(−½+it) y^{−½+it} g_T(−½+it) dt = 2π y J_T(y)`. -/
theorem integral_zetaChi_mul_cpow_mul_gaussWeight {T : ℝ} (hT : 1 ≤ T) {y : ℝ} (hy : 0 < y) :
    ∫ t : ℝ, zetaChi (leftPt t) * (y : ℂ) ^ leftPt t * gaussWeight T (leftPt t) =
      2 * Real.pi * y * leftKernel T y := by
  have hT0 : 0 < T := by linarith
  have hpos : 0 < 2 * Real.pi * y := by positivity
  set am : ℂ := ((2 * Real.pi * y : ℝ) : ℂ) * (-I) with ham
  set ap : ℂ := ((2 * Real.pi * y : ℝ) : ℂ) * I with hap
  have hamre : am.re = 0 := by simp [ham]
  have hapre : ap.re = 0 := by simp [hap]
  have ham0 : am ≠ 0 := mul_ne_zero (by exact_mod_cast hpos.ne') (neg_ne_zero.mpr Complex.I_ne_zero)
  have hap0 : ap ≠ 0 := mul_ne_zero (by exact_mod_cast hpos.ne') Complex.I_ne_zero
  have hsplit : (fun t : ℝ => zetaChi (leftPt t) * (y : ℂ) ^ leftPt t * gaussWeight T (leftPt t)) =
      fun t => (y : ℂ) * (Complex.Gamma (leftDual t) * am ^ (-leftDual t) * gaussWeight T (leftPt t) +
        Complex.Gamma (leftDual t) * ap ^ (-leftDual t) * gaussWeight T (leftPt t)) := by
    funext t
    rw [zetaChi_mul_cpow_eq t hy]
    ring
  rw [hsplit, integral_const_mul,
    integral_add (integrable_left_integrand hT0 hamre.ge ham0)
      (integrable_left_integrand hT0 hapre.ge hap0),
    integral_Gamma_mul_cpow_mul_gaussWeight_of_re_eq_zero hT hamre ham0,
    integral_Gamma_mul_cpow_mul_gaussWeight_of_re_eq_zero hT hapre hap0, ← mul_add]
  have hT0' : (0 : ℝ) ≤ T := hT0.le
  have hint : ∀ a : ℂ, a.re = 0 → Integrable (fun u : ℝ => cexp (-(a * (Real.exp u : ℂ))) *
      ((Real.exp (u / 2) * gaussDensity T u : ℝ) : ℂ)) := by
    intro a ha
    refine (integrable_moment_integrand 0 (c := 1 / 2) hT).mono'
      (by have := continuous_gaussDensity T; fun_prop) (Eventually.of_forall fun u => ?_)
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by have := gaussDensity_nonneg hT0' u; positivity), pow_zero, one_mul]
    have : (-(a * (Real.exp u : ℂ))).re = 0 := by
      rw [Complex.neg_re, Complex.mul_re, ha, Complex.ofReal_re, Complex.ofReal_im]; ring
    rw [this, Real.exp_zero, one_mul]
    exact mul_le_mul_of_nonneg_right (abs_exp_half_le u) (gaussDensity_nonneg hT0' u)
  rw [← integral_add (hint am hamre) (hint ap hapre)]
  have hpt : ∀ u : ℝ, cexp (-(am * (Real.exp u : ℂ))) *
      ((Real.exp (u / 2) * gaussDensity T u : ℝ) : ℂ) +
      cexp (-(ap * (Real.exp u : ℂ))) * ((Real.exp (u / 2) * gaussDensity T u : ℝ) : ℂ) =
      ((2 * Real.cos (2 * Real.pi * y * Real.exp u) * Real.exp (u / 2) * gaussDensity T u : ℝ) : ℂ) := by
    intro u
    have h2 := Complex.two_cos ((2 * Real.pi * y * Real.exp u : ℝ) : ℂ)
    have e1 : -(am * (Real.exp u : ℂ)) = ((2 * Real.pi * y * Real.exp u : ℝ) : ℂ) * I := by
      rw [ham]; push_cast; ring
    have e2 : -(ap * (Real.exp u : ℂ)) = -((2 * Real.pi * y * Real.exp u : ℝ) : ℂ) * I := by
      rw [hap]; push_cast; ring
    rw [e1, e2, ← add_mul, ← h2]
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_complex_ofReal]
  unfold leftKernel
  ring

end

end RHTower.GaussZeroSum
