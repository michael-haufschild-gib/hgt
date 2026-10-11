import GaloisForLFunctions.RHTower.XiRealPartDerivativeCurvesCriterion
import GaloisForLFunctions.RHTower.XiCosineShiftHeatStrip
import GaloisForLFunctions.HTGeometry.SechComplexFourierTransform

/-!
# The sech handoff from the cosine producer to `Ξ`

For every depth `h > 0` the producer `A_h = cos(hD)Ξ` determines `Ξ` exactly:

  `Ξ(t) = ∫ κ_h(t − v) A_h(v) dv`,   `κ_h(w) = (1/(2h)) · sech(πw/(2h))`

(`XiC_eq_integral_sech_mul_cosProducer`). The kernel `κ_h` is a positive probability density of
width `≍ h`, and its two-sided Laplace transform is `1/cos(hs)`, the reciprocal of a Laguerre–Pólya
function. So `κ_h` is a Pólya frequency function and `Ξ` is a variation-diminishing smoothing of
`A_h`.

At the horizon depth `h = ½` the producer is `A_½(v) = Re ξ(1 + iv)`. It is Laguerre–Pólya
unconditionally, and on `Re s = 1` the Euler product of `ζ` converges. The identity is therefore an
exact, divisor-preserving handoff from a lossless prime-faithful source on the horizon to `Ξ` on the
critical line, through the nonlocal port `κ_½(w) = sech(πw)`. RH says this port loses no real
zero.

**Proof.** `A_h` is the transform of `Φ(u) cosh(hu)` (`cosTransform_riemannKernel_mul_cosh`). By
Fubini, `∫ κ_h(t − v) e^{ivu} dv = e^{itu} ∫ κ_h(w) e^{−iwu} dw`. The substitution
`w = (2h/π) r` and `∫ e^{−izr}/cosh r dr = π/cosh(πz/2)` (`integral_cexp_div_cosh`) give
`1/cosh(hu)`. The weight `cosh(hu)` cancels, leaving `∫ Φ(u) e^{itu} du = Ξ(t)`.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The sech port of depth `h`: `κ_h(w) = (1/(2h)) / cosh(πw/(2h))`. -/
def sechPort (h w : ℝ) : ℝ := 1 / (2 * h) / Real.cosh (Real.pi * w / (2 * h))

theorem sechPort_pos {h : ℝ} (hh : 0 < h) (w : ℝ) : 0 < sechPort h w := by
  unfold sechPort; have := Real.cosh_pos (Real.pi * w / (2 * h)); positivity

theorem continuous_sechPort (h : ℝ) : Continuous (sechPort h) := by
  unfold sechPort
  exact continuous_const.div (Real.continuous_cosh.comp (by fun_prop))
    (fun w => (Real.cosh_pos _).ne')

theorem inv_cosh_le (x : ℝ) : 1 / Real.cosh x ≤ 2 * (1 + x ^ 2)⁻¹ := by
  have h1 := DeBruijn.one_add_sq_div_two_le_cosh x
  have hc := Real.cosh_pos x
  rw [div_le_iff₀ hc]
  have : 0 < 1 + x ^ 2 := by positivity
  rw [mul_comm, ← mul_assoc]
  field_simp
  nlinarith

theorem integrable_sechPort {h : ℝ} (hh : 0 < h) : Integrable (sechPort h) := by
  have hmaj : Integrable (fun w : ℝ => 1 / (2 * h) * (2 * (1 + (Real.pi / (2 * h) * w) ^ 2)⁻¹)) :=
    ((integrable_inv_one_add_sq.comp_mul_left' (by positivity)).const_mul 2).const_mul _
  refine hmaj.mono' (continuous_sechPort h).aestronglyMeasurable (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (sechPort_pos hh w)]
  unfold sechPort
  rw [div_eq_mul_one_div (1 / (2 * h))]
  gcongr
  rw [show Real.pi / (2 * h) * w = Real.pi * w / (2 * h) by ring]
  exact inv_cosh_le _

/-- **The sech port's Fourier transform:** `∫ κ_h(w) e^{−iwu} dw = 1/cosh(hu)`. -/
theorem integral_sechPort_mul_cexp {h : ℝ} (hh : 0 < h) (u : ℝ) :
    ∫ w : ℝ, (sechPort h w : ℂ) * Complex.exp (-(I * (w : ℂ) * u)) =
      ((1 / Real.cosh (h * u) : ℝ) : ℂ) := by
  set a : ℝ := 2 * h / Real.pi with ha
  have hapos : 0 < a := by positivity
  set G : ℝ → ℂ := fun w => (sechPort h w : ℂ) * Complex.exp (-(I * (w : ℂ) * u)) with hG
  have hsub := Measure.integral_comp_mul_left G a
  have hGa : ∀ r : ℝ, G (a * r) = (1 / (2 * h) : ℂ) *
      (Complex.exp (-(((2 * h * u / Real.pi : ℝ) : ℂ) * (r : ℂ)) * I) / (Real.cosh r : ℂ)) := by
    intro r
    simp only [hG, sechPort]
    have e1 : Real.pi * (a * r) / (2 * h) = r := by
      rw [ha]; field_simp
    rw [e1]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have e3 : -(I * ((a * r : ℝ) : ℂ) * (u : ℂ)) =
        -(((2 * h * u / Real.pi : ℝ) : ℂ) * (r : ℂ)) * I := by
      rw [ha]; push_cast; field_simp
    rw [e3]
    push_cast
    ring
  have hint := integral_cexp_div_cosh (z := ((2 * h * u / Real.pi : ℝ) : ℂ)) (by simp)
  have hcosh : Complex.cosh ((Real.pi : ℂ) * ((2 * h * u / Real.pi : ℝ) : ℂ) / 2) =
      (Real.cosh (h * u) : ℂ) := by
    rw [Complex.ofReal_cosh]; congr 1; push_cast; field_simp
  rw [hcosh] at hint
  have hlhs : ∫ r : ℝ, G (a * r) = (1 / (2 * h) : ℂ) * ((Real.pi : ℂ) / (Real.cosh (h * u) : ℂ)) := by
    simp_rw [hGa]; rw [integral_const_mul, hint]
  rw [hlhs, abs_of_pos (inv_pos.mpr hapos), ha] at hsub
  have hcne : (Real.cosh (h * u) : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos _).ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hh2 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  -- solve for `∫ G`
  have key : ∫ w, G w = ((2 * h / Real.pi : ℝ) : ℂ) *
      ((1 / (2 * h) : ℂ) * ((Real.pi : ℂ) / (Real.cosh (h * u) : ℂ))) := by
    rw [hsub, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
      mul_inv_cancel₀ (by positivity : (2 * h / Real.pi : ℝ) ≠ 0), Complex.ofReal_one, one_mul]
  rw [key]
  push_cast
  field_simp

/-- **The sech handoff.** For every `h > 0` and real `t`,
`Ξ(t) = ∫ κ_h(t − v) A_h(v) dv` with `κ_h(w) = (1/(2h))/cosh(πw/(2h))`. -/
theorem XiC_eq_integral_sech_mul_cosProducer {h : ℝ} (hh : 0 < h) (t : ℝ) :
    XiC t = ∫ v : ℝ, (sechPort h (t - v) : ℂ) * cosProducer h v := by
  set g : ℝ → ℝ := fun x => riemannKernelReal x * Real.cosh (h * x) with hg
  have hgk : DeBruijn.SuperExpKernel g := DeBruijn.riemannKernel_mul_cosh_superExp h
  have hA : ∀ v : ℝ, cosProducer h v = ∫ u : ℝ, (g u : ℂ) * Complex.exp (I * (v : ℂ) * u) := by
    intro v
    rw [cosProducer, ← DeBruijn.cosTransform_riemannKernel_mul_cosh]; rfl
  simp_rw [hA, ← integral_const_mul]
  -- Fubini
  have hint : Integrable (Function.uncurry fun (v u : ℝ) =>
      (sechPort h (t - v) : ℂ) * ((g u : ℂ) * Complex.exp (I * (v : ℂ) * u)))
      (volume.prod volume) := by
    have hprod : Integrable (fun p : ℝ × ℝ => sechPort h (t - p.1) * g p.2) (volume.prod volume) :=
      ((integrable_sechPort hh).comp_sub_left t).mul_prod
        (by simpa using hgk.integrable_mul_exp 0)
    refine hprod.mono' ?_ (Eventually.of_forall fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      exact (Complex.continuous_ofReal.comp ((continuous_sechPort h).comp
        (continuous_const.sub continuous_fst))).mul
        ((Complex.continuous_ofReal.comp (hgk.continuous.comp continuous_snd)).mul (by fun_prop))
    · change ‖(sechPort h (t - p.1) : ℂ) * ((g p.2 : ℂ) * Complex.exp (I * (p.1 : ℂ) * p.2))‖ ≤
        sechPort h (t - p.1) * g p.2
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos (sechPort_pos hh _), abs_of_nonneg (hgk.nonneg _)]
      have : ‖Complex.exp (I * (p.1 : ℂ) * p.2)‖ = 1 := by
        rw [Complex.norm_exp]; simp
      rw [this, mul_one]
  rw [integral_integral_swap hint]
  -- the inner integral
  have hinner : ∀ u : ℝ, ∫ v : ℝ, (sechPort h (t - v) : ℂ) * ((g u : ℂ) *
      Complex.exp (I * (v : ℂ) * u)) = (g u : ℂ) * (Complex.exp (I * (t : ℂ) * u) *
        ((1 / Real.cosh (h * u) : ℝ) : ℂ)) := by
    intro u
    have e : ∀ v : ℝ, (sechPort h (t - v) : ℂ) * ((g u : ℂ) * Complex.exp (I * (v : ℂ) * u)) =
        (g u : ℂ) * Complex.exp (I * (t : ℂ) * u) *
          ((sechPort h (t - v) : ℂ) * Complex.exp (-(I * ((t - v : ℝ) : ℂ) * u))) := by
      intro v
      have : Complex.exp (I * (v : ℂ) * u) = Complex.exp (I * (t : ℂ) * u) *
          Complex.exp (-(I * ((t - v : ℝ) : ℂ) * u)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [this]; ring
    simp_rw [e]
    rw [integral_const_mul]
    rw [integral_sub_left_eq_self (fun w : ℝ => (sechPort h w : ℂ) *
      Complex.exp (-(I * (w : ℂ) * u))) (μ := volume) t]
    rw [integral_sechPort_mul_cexp hh]
    ring
  simp_rw [hinner]
  rw [← DeBruijn.cosTransform_riemannKernel_eq_XiC]
  unfold DeBruijn.cosTransform
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have e : ((1 / Real.cosh (h * u) : ℝ) : ℂ) * (Real.cosh (h * u) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, one_div, inv_mul_cancel₀ (Real.cosh_pos _).ne', Complex.ofReal_one]
  show (riemannKernelReal u : ℂ) * Complex.exp (I * (t : ℂ) * u) =
    ((riemannKernelReal u * Real.cosh (h * u) : ℝ) : ℂ) *
      (Complex.exp (I * (t : ℂ) * u) * ((1 / Real.cosh (h * u) : ℝ) : ℂ))
  rw [Complex.ofReal_mul]
  linear_combination -((riemannKernelReal u : ℂ) * Complex.exp (I * (t : ℂ) * u)) * e

/-- The sech port is a probability density. -/
theorem integral_sechPort {h : ℝ} (hh : 0 < h) : ∫ w : ℝ, sechPort h w = 1 := by
  have h0 := integral_sechPort_mul_cexp hh 0
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one, Real.cosh_zero,
    div_one, Complex.ofReal_one] at h0
  rw [integral_complex_ofReal] at h0
  exact_mod_cast h0

/-- **The horizon handoff.** `Ξ(t) = ∫ sech(π(t − v)) Re ξ(1 + iv) dv`: the critical-line function
is the sech smoothing of the real part of `ξ` on the line `Re s = 1`, where the Euler product
converges. -/
theorem XiC_eq_integral_sech_mul_re_xi_one (t : ℝ) :
    XiC t = ∫ v : ℝ, (sechPort (1 / 2) (t - v) : ℂ) * ((xi (1 + v * I)).re : ℂ) := by
  rw [XiC_eq_integral_sech_mul_cosProducer (by norm_num : (0 : ℝ) < 1 / 2) t]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  rw [cosProducer_ofReal]
  congr 4
  push_cast; ring

end

end RHTower
