import GaloisForLFunctions.GaloisTheoryOfZeros.TheTraceOfAFibreOfTheHeatCover
import GaloisForLFunctions.HTGeometry.DecreasingSineTransformPositivity
import GaloisForLFunctions.RHTower.CHMDOddHarmonicIdentityAndPolarDoobAbsorption

/-!
# The sign branch points lie in the forward half-plane

The sign branch points of the heat cover are the zeros of the centre value
`c(τ) = ∫ Φ(x) e^{τx²} dx`: the times at which pairs `±z` of zeros collide at the centre and the
reflection `z ↦ −z` is the local monodromy. This file locates them.

For `τ = r + ib`, in the variable `u = x²`,

`Im c(τ) = 2 ∫₀^∞ g_r(u) sin(bu) du`, `g_r(u) = Φ(√u) e^{ru} / (2√u)`.

The Riemann kernel is positive and decreasing on `[0, ∞)`. For `r ≤ 0` the weight `g_r` is
therefore strictly decreasing on `(0, ∞)`, and the sine transform of a decreasing function is
positive. So

* `Im c(τ)` has the sign of `Im τ` on the closed backward half-plane `Re τ ≤ 0`
  (`im_centreValue_pos`, `im_centreValue_neg`);
* `c` maps the closed backward half-plane into the slit plane `ℂ ∖ (−∞, 0]`
  (`centreValue_mem_slitPlane`), and `√c` has a single-valued analytic branch there
  (`analyticAt_sqrtCentreValue`): the sign character of the cover is trivial over backward times;
* every sign branch point has `Re τ > 0` (`re_pos_of_centreValue_eq_zero`,
  `IsCollision.re_pos_of_center`);
* over the closed backward half-plane the trace of the fibre is `Σ 1/z² = c'(τ)/c(τ)` without
  exception (`hasSum_inv_sq_zeros_complexHeat_of_re_nonpos`).
-/

open Complex MeasureTheory Filter Topology Set
open RHTower RHTower.DeBruijn GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.EntireZeroDivisor

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## The imaginary part of the centre value -/

theorem integrable_complexWeight (τ : ℂ) : Integrable (complexWeight τ) := by
  have h := integrable_complexWeight_mul_pow_mul_exp τ 0 0
  simpa using h

theorem im_complexWeight (τ : ℂ) (x : ℝ) :
    (complexWeight τ x).im =
      riemannKernelReal x * Real.exp (τ.re * x ^ 2) * Real.sin (τ.im * x ^ 2) := by
  have h1 : (τ * (x : ℂ) ^ 2).re = τ.re * x ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.re_mul_ofReal]
  have h2 : (τ * (x : ℂ) ^ 2).im = τ.im * x ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.im_mul_ofReal]
  rw [complexWeight, Complex.im_ofReal_mul, Complex.exp_im, h1, h2]
  ring

theorem integrable_im_complexWeight (τ : ℂ) :
    Integrable fun x : ℝ =>
      riemannKernelReal x * Real.exp (τ.re * x ^ 2) * Real.sin (τ.im * x ^ 2) := by
  have h := Complex.imCLM.integrable_comp (integrable_complexWeight τ)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [Complex.imCLM_apply, im_complexWeight]

/-- The imaginary part of the centre value is a sine integral over the half-line. -/
theorem im_centreValue (τ : ℂ) :
    (centreValue τ).im = 2 * ∫ x in Ioi (0 : ℝ),
      riemannKernelReal x * Real.exp (τ.re * x ^ 2) * Real.sin (τ.im * x ^ 2) := by
  have h1 : centreValue τ = ∫ x : ℝ, complexWeight τ x := by
    rw [centreValue, complexHeat]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [complexWeight, mul_zero, zero_mul, add_zero]
  rw [h1, ← Complex.imCLM_apply,
    ← ContinuousLinearMap.integral_comp_comm _ (integrable_complexWeight τ),
    ← integral_comp_abs (f := fun x : ℝ =>
      riemannKernelReal x * Real.exp (τ.re * x ^ 2) * Real.sin (τ.im * x ^ 2))]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Complex.imCLM_apply, im_complexWeight, sq_abs,
    RHTower.CHMDPolar.riemannKernelReal_abs]

/-! ## The weight in the squared variable -/

/-- The weight of the centre value in the variable `u = x²`: `Φ(√u) e^{ru} / (2√u)`. -/
def foldedWeight (r u : ℝ) : ℝ :=
  riemannKernelReal (Real.sqrt u) * Real.exp (r * u) / (2 * Real.sqrt u)

/-- **At backward times the weight in the squared variable is strictly decreasing.** The kernel
and `e^{ru}` do not increase and `1/√u` decreases strictly. -/
theorem strictAntiOn_foldedWeight {r : ℝ} (hr : r ≤ 0) :
    StrictAntiOn (foldedWeight r) (Ioi 0) := by
  intro u hu v hv huv
  have hu0 : 0 < u := hu
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.2 hu0
  have hsuv : Real.sqrt u < Real.sqrt v := Real.sqrt_lt_sqrt hu0.le huv
  have hΦ : riemannKernelReal (Real.sqrt v) ≤ riemannKernelReal (Real.sqrt u) :=
    RHTower.CHMDPolar.strictAntiOn_riemannKernelReal_Ici.antitoneOn (mem_Ici.2 hsu.le)
      (mem_Ici.2 (hsu.trans hsuv).le) hsuv.le
  have he : Real.exp (r * v) ≤ Real.exp (r * u) := Real.exp_le_exp.2 (by nlinarith)
  have hnum : riemannKernelReal (Real.sqrt v) * Real.exp (r * v) ≤
      riemannKernelReal (Real.sqrt u) * Real.exp (r * u) :=
    mul_le_mul hΦ he (Real.exp_pos _).le (riemannKernelReal_pos _).le
  have hpos : 0 < riemannKernelReal (Real.sqrt v) * Real.exp (r * v) :=
    mul_pos (riemannKernelReal_pos _) (Real.exp_pos _)
  unfold foldedWeight
  rw [div_lt_div_iff₀ (mul_pos two_pos (hsu.trans hsuv)) (mul_pos two_pos hsu)]
  nlinarith [mul_pos hpos (sub_pos.2 hsuv), mul_nonneg (sub_nonneg.2 hnum) (hsu.trans hsuv).le]

/-- The substitution `u = x²` on the integrand of the imaginary part. -/
private theorem weight_mul_sin_eq (r b : ℝ) {x : ℝ} (hx : 0 < x) :
    riemannKernelReal x * Real.exp (r * x ^ 2) * Real.sin (b * x ^ 2) =
      (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) •
        (foldedWeight r (x ^ (2 : ℝ)) * Real.sin (b * x ^ (2 : ℝ))) := by
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, abs_two, smul_eq_mul,
    foldedWeight, Real.sqrt_sq hx.le]
  field_simp

theorem integrableOn_foldedWeight_mul_sin (τ : ℂ) :
    IntegrableOn (fun u => foldedWeight τ.re u * Real.sin (τ.im * u)) (Ioi 0) := by
  rw [← integrableOn_Ioi_comp_rpow_iff (fun u => foldedWeight τ.re u * Real.sin (τ.im * u))
    (two_ne_zero' ℝ)]
  exact (integrable_im_complexWeight τ).integrableOn.congr_fun
    (fun x hx => weight_mul_sin_eq τ.re τ.im hx) measurableSet_Ioi

theorem integral_Ioi_weight_mul_sin (r b : ℝ) :
    ∫ x in Ioi (0 : ℝ), riemannKernelReal x * Real.exp (r * x ^ 2) * Real.sin (b * x ^ 2) =
      ∫ u in Ioi (0 : ℝ), foldedWeight r u * Real.sin (b * u) := by
  refine Eq.trans ?_ (integral_comp_rpow_Ioi (fun u => foldedWeight r u * Real.sin (b * u))
    (two_ne_zero' ℝ))
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx => weight_mul_sin_eq r b hx

/-! ## The sign of the imaginary part at backward times -/

/-- **At a backward time above the real axis the centre value lies in the upper half-plane.** -/
theorem im_centreValue_pos {τ : ℂ} (hre : τ.re ≤ 0) (him : 0 < τ.im) :
    0 < (centreValue τ).im := by
  rw [im_centreValue, integral_Ioi_weight_mul_sin]
  exact mul_pos two_pos (integral_Ioi_mul_sin_pos_of_strictAntiOn_Ioi
    (strictAntiOn_foldedWeight hre) him (integrableOn_foldedWeight_mul_sin τ))

theorem centreValue_conj (τ : ℂ) :
    centreValue (starRingEnd ℂ τ) = starRingEnd ℂ (centreValue τ) := by
  rw [centreValue, centreValue, complexHeat_conj, map_zero]

/-- At a backward time below the real axis the centre value lies in the lower half-plane. -/
theorem im_centreValue_neg {τ : ℂ} (hre : τ.re ≤ 0) (him : τ.im < 0) :
    (centreValue τ).im < 0 := by
  have h := im_centreValue_pos (τ := starRingEnd ℂ τ) (by simpa using hre) (by simpa using him)
  rw [centreValue_conj, Complex.conj_im] at h
  linarith

/-- **The centre value maps the closed backward half-plane into the slit plane.** -/
theorem centreValue_mem_slitPlane {τ : ℂ} (hre : τ.re ≤ 0) :
    centreValue τ ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  rcases lt_trichotomy τ.im 0 with h | h | h
  · exact Or.inr (im_centreValue_neg hre h).ne
  · left
    have hτ : τ = (τ.re : ℂ) := Complex.ext rfl (by rw [Complex.ofReal_im]; exact h)
    rw [hτ, centreValue, complexHeat_ofReal_center, Complex.ofReal_re]
    exact integral_riemannKernelReal_mul_exp_pos τ.re
  · exact Or.inr (im_centreValue_pos hre h).ne'

theorem centreValue_ne_zero_of_re_nonpos {τ : ℂ} (hre : τ.re ≤ 0) : centreValue τ ≠ 0 :=
  Complex.slitPlane_ne_zero (centreValue_mem_slitPlane hre)

/-! ## The sign branch points -/

/-- **Every zero of the centre value has positive real part.** -/
theorem re_pos_of_centreValue_eq_zero {τ : ℂ} (h : centreValue τ = 0) : 0 < τ.re := by
  by_contra hre
  exact centreValue_ne_zero_of_re_nonpos (not_lt.mp hre) h

/-- **Every collision at the centre happens at a forward time off the real axis.** -/
theorem IsCollision.re_pos_of_center {τ₀ : ℂ} {m : ℕ} (hm : 0 < m)
    (hc : IsCollision τ₀ 0 m) : 0 < τ₀.re ∧ τ₀.im ≠ 0 := by
  have h0 : centreValue τ₀ = 0 := by
    have h := hc.vanish 0 hm
    rwa [iteratedDeriv_zero] at h
  exact ⟨re_pos_of_centreValue_eq_zero h0, im_ne_zero_of_centreValue_eq_zero h0⟩

/-- Over the closed backward half-plane the trace of the fibre is the logarithmic derivative of
the centre value, without exceptional times. -/
theorem hasSum_inv_sq_zeros_complexHeat_of_re_nonpos {τ : ℂ} (hre : τ.re ≤ 0) :
    HasSum (fun q : ZeroCopy (complexHeat τ) => (zeroCopyPoint (complexHeat τ) q ^ 2)⁻¹)
      (logDeriv centreValue τ) :=
  hasSum_inv_sq_zeros_complexHeat (centreValue_ne_zero_of_re_nonpos hre)

/-! ## The sign character over backward times -/

/-- The principal square root of the centre value. -/
def sqrtCentreValue (τ : ℂ) : ℂ := cexp (Complex.log (centreValue τ) / 2)

theorem sqrtCentreValue_sq {τ : ℂ} (h : centreValue τ ≠ 0) :
    sqrtCentreValue τ ^ 2 = centreValue τ := by
  rw [sqrtCentreValue, ← Complex.exp_nat_mul,
    show ((2 : ℕ) : ℂ) * (Complex.log (centreValue τ) / 2) = Complex.log (centreValue τ) by
      push_cast; ring, Complex.exp_log h]

/-- **The sign character is trivial over backward times.** The principal square root of the
centre value is analytic at every time of the closed backward half-plane, so `√c` does not change
sign along a loop of backward times. -/
theorem analyticAt_sqrtCentreValue {τ : ℂ} (hre : τ.re ≤ 0) : AnalyticAt ℂ sqrtCentreValue τ :=
  (((differentiable_centreValue.analyticAt τ).clog (centreValue_mem_slitPlane hre)).div_const).cexp

end

end GaloisForLFunctions.GaloisTheoryOfZeros
