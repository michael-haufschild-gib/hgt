import GaloisForLFunctions.HTGeometry.CaratheodoryKernelPositive
import GaloisForLFunctions.RHTower.XiShiftLoewnerCriticalGenerator
import GaloisForLFunctions.RHTower.ThetaCuspCenterMixedPublishedGrowthPriorArt
import GaloisForLFunctions.RHTower.XiProjectiveReflectionSourceTemperatureSpectrum
import GaloisForLFunctions.RHTower.WeightedLaplaceShift

/-!
# The critical logarithmic-derivative kernel is an Euler-safe Carathéodory kernel minus its
Cauchy loss

In the centred coordinate `X(W) = ξ(1/2 + W)` and `L = X'/X`, fix a safe offset `a > 1/2` and put

```
K_a (W, V) = (L W + conj (L V)) / (W + conj V - 2 a),
C_a (W, V) = 2 a / (W + conj V),
K_0 (W, V) = (L W + conj (L V)) / (W + conj V).
```

On the Euler-safe half plane `Re W > a` the logarithmic derivative has strictly positive real part,
so `K_a` is an unconditional positive Carathéodory kernel; `C_a` is the positive Cauchy kernel of
the same half plane, realized as a Laplace Gram, with unit-bounded diagonal `a / Re W < 1`.  The
exact factorization `K_a (1 - C_a) = K_0` turns positivity of the RH-deciding kernel `K_0` into the
Schur domination `K_a ∘ C_a ≤ K_a`, and both sides of that domination are separately positive
without any hypothesis on the zeros.

The domination is genuinely multi-node: for the positive-real function `w ↦ 1/(w - a)` the same
subtraction produces a two-node matrix of strictly negative determinant.
-/

noncomputable section

open Complex Set MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate ComplexOrder

namespace RHTower

/-! ### The centred logarithmic derivative has positive real part -/

theorem xiCent_eq_XiC (W : ℂ) : xiCent W = XiC (-Complex.I * W) := by
  rw [xiCent, XiC]
  congr 1
  have h := Complex.I_mul_I
  linear_combination (-W) * h

theorem logDeriv_xiCent_eq (W : ℂ) :
    logDeriv xiCent W = -Complex.I * logDeriv XiC (-Complex.I * W) := by
  have hlin : HasDerivAt (fun z : ℂ => -Complex.I * z) (-Complex.I) W := by
    simpa using (hasDerivAt_id W).const_mul (-Complex.I)
  have hcomp : HasDerivAt xiCent (deriv XiC (-Complex.I * W) * (-Complex.I)) W := by
    have h := (XiC_differentiable (-Complex.I * W)).hasDerivAt.comp W hlin
    have hfun : (XiC ∘ fun z : ℂ => -Complex.I * z) = xiCent := by
      funext z
      exact (xiCent_eq_XiC z).symm
    rwa [hfun] at h
  rw [logDeriv_apply, logDeriv_apply, hcomp.deriv, xiCent_eq_XiC W]
  ring

/-- **Unconditional Euler-safe positivity.**  Beyond the critical half-width the centred
logarithmic derivative maps into the open right half plane. -/
theorem re_logDeriv_xiCent_pos {W : ℂ} (hW : 1 / 2 < W.re) :
    0 < (logDeriv xiCent W).re := by
  set z : ℂ := -Complex.I * W with hz
  have hzim : z.im = -W.re := by
    rw [hz]
    simp [Complex.mul_im]
  have hzIm : z.im < -(1 / 2 : ℝ) := by
    rw [hzim]
    linarith
  have hXi : XiC z ≠ 0 := by
    rw [hz, ← xiCent_eq_XiC]
    exact xiCent_ne_zero_of_half_lt_re hW
  have htrace := xiRelativeResolventTrace_im_pos_of_halfPlaneBound
    (by norm_num : (0 : ℝ) ≤ 1 / 2) xiZeroHalfPlaneBound_half z hzIm
  rw [logDeriv_xiCent_eq W, ← hz, logDeriv_XiC_eq_relativeResolventTrace hXi]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    neg_zero, zero_mul, neg_neg, one_mul, zero_sub, sub_neg_eq_add, zero_add]
  linarith

theorem differentiableAt_logDeriv_xiCent {W : ℂ} (hW : 1 / 2 < W.re) :
    DifferentiableAt ℂ (logDeriv xiCent) W := by
  have hne := xiCent_ne_zero_of_half_lt_re hW
  have hana := xiCent_analytic W (Set.mem_univ W)
  have hfun : logDeriv xiCent = fun z : ℂ => deriv xiCent z / xiCent z := by
    funext z
    exact logDeriv_apply _ _
  rw [hfun]
  exact DifferentiableAt.div hana.deriv.differentiableAt hana.differentiableAt hne

/-! ### The three kernels -/

/-- The Euler-safe Carathéodory kernel `K_a`. -/
def safeCaratheodoryKernel (a : ℝ) (W V : ℂ) : ℂ :=
  (logDeriv xiCent W + conj (logDeriv xiCent V)) / (W + conj V - 2 * (a : ℂ))

/-- The Cauchy loss factor `C_a`. -/
def cauchyLossKernel (a : ℝ) (W V : ℂ) : ℂ := 2 * (a : ℂ) / (W + conj V)

/-- The RH-deciding critical kernel `K_0`. -/
def criticalLogDerivKernel (W V : ℂ) : ℂ :=
  (logDeriv xiCent W + conj (logDeriv xiCent V)) / (W + conj V)

theorem re_add_conj (W V : ℂ) : (W + conj V).re = W.re + V.re := by
  simp [Complex.add_re, Complex.conj_re]

theorem add_conj_ne_zero {W V : ℂ} (hW : 0 < W.re) (hV : 0 < V.re) : W + conj V ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [re_add_conj] at this
  simp only [Complex.zero_re] at this
  linarith

theorem add_conj_sub_ne_zero {a : ℝ} {W V : ℂ} (hW : a < W.re) (hV : a < V.re) :
    W + conj V - 2 * (a : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.zero_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, re_add_conj] at this
  norm_num at this
  linarith

/-! ### Equation (4): the strictly subunit diagonal -/

theorem cauchyLossKernel_diag {a : ℝ} {W : ℂ} (hW : 0 < W.re) :
    cauchyLossKernel a W W = ((a / W.re : ℝ) : ℂ) := by
  have hsum : W + conj W = ((2 * W.re : ℝ) : ℂ) := by
    rw [Complex.add_conj]
    push_cast
    ring
  have hne : ((2 * W.re : ℝ) : ℂ) ≠ 0 := by
    simp only [Ne, Complex.ofReal_eq_zero]
    intro h
    linarith
  rw [cauchyLossKernel, hsum]
  rw [div_eq_div_iff hne (by simp only [Ne, Complex.ofReal_eq_zero]; exact ne_of_gt hW)]
  push_cast
  field_simp
  ring

theorem cauchyLossKernel_diag_lt_one {a : ℝ} {W : ℂ} (ha : 0 < a) (hW : a < W.re) :
    (a / W.re : ℝ) < 1 := by
  have hWpos : 0 < W.re := lt_trans ha hW
  rw [div_lt_one hWpos]
  exact hW

/-! ### Equation (6): the Laplace Gram realization of the Cauchy factor -/

theorem cauchyLossKernel_eq_laplace {a : ℝ} {W V : ℂ} (hW : 0 < W.re) (hV : 0 < V.re) :
    cauchyLossKernel a W V
      = ∫ x in Ioi (0 : ℝ), 2 * (a : ℂ) *
          (Complex.exp (-(W * (x : ℂ))) * Complex.exp (-(conj V * (x : ℂ)))) := by
  have hre : 0 < (W + conj V).re := by
    rw [re_add_conj]
    linarith
  have hcongr : ∀ x : ℝ, 2 * (a : ℂ) *
      (Complex.exp (-(W * (x : ℂ))) * Complex.exp (-(conj V * (x : ℂ))))
      = 2 * (a : ℂ) * Complex.exp (-((W + conj V) * (x : ℂ))) := by
    intro x
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x _ => hcongr x),
    MeasureTheory.integral_const_mul, integral_cexp_neg_mul_Ioi_zero hre, cauchyLossKernel]
  field_simp

end RHTower
