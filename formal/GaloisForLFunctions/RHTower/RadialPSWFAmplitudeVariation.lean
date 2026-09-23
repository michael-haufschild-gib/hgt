import GaloisForLFunctions.HTGeometry.GronwallScaledBound
import GaloisForLFunctions.RHTower.RadialPSWFInteractionPicture

/-!
# Bounded variation of the interaction-picture amplitudes

The exact transport laws of `RadialPSWFInteractionPicture` say that the two oscillatory amplitudes
of `W'' + c²W = ψW` move only under the short-range potential:

```text
a₊' = e^{−icx} ψ W /(2ic) ,      a₋' = −e^{icx} ψ W /(2ic) .
```

Since `|e^{±icx}| = 1` and `‖W‖ ≤ ‖a₊‖ + ‖a₋‖`, the total amplitude `A = ‖a₊‖ + ‖a₋‖` obeys the
Volterra inequality `A(x) ≤ A(a) + ∫ (‖ψ‖/c) A`, so the variable-coefficient Grönwall inequality
gives

```text
A(x) ≤ A(a) · exp( (1/c) ∫_a^x ‖ψ‖ ) ,
```

and the total variation of each amplitude over the whole interval is at most
`A(a)·(exp(V/c) − 1)` with `V = ∫_a^b ‖ψ‖`, i.e. `O(V/c)`.

This is the estimate that converts the exact decomposition into a genuine symbol bound: the
amplitudes are almost constant, with total variation one power of the bandwidth small.
-/

open Set MeasureTheory intervalIntegral

open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

variable {c : ℝ} {W V psi : ℝ → ℂ}

/-- The total interaction amplitude. -/
def radialInteractionTotal (c : ℝ) (W V : ℝ → ℂ) (x : ℝ) : ℝ :=
  ‖radialInteractionPlus c W V x‖ + ‖radialInteractionMinus c W V x‖

theorem radialInteractionTotal_nonneg (c : ℝ) (W V : ℝ → ℂ) (x : ℝ) :
    0 ≤ radialInteractionTotal c W V x := by
  unfold radialInteractionTotal
  positivity

theorem norm_exp_neg_I_mul (c x : ℝ) :
    ‖Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem norm_exp_I_mul (c x : ℝ) :
    ‖Complex.exp (Complex.I * (c : ℂ) * (x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- The solution is dominated by the total amplitude. -/
theorem norm_le_radialInteractionTotal (hc : c ≠ 0) (W V : ℝ → ℂ) (x : ℝ) :
    ‖W x‖ ≤ radialInteractionTotal c W V x := by
  have hrec := radialInteraction_reconstruct (c := c) (x := x) hc W V
  calc ‖W x‖ = ‖radialInteractionPlus c W V x * Complex.exp (Complex.I * (c : ℂ) * (x : ℂ))
        + radialInteractionMinus c W V x * Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ))‖ := by
        rw [hrec]
    _ ≤ ‖radialInteractionPlus c W V x * Complex.exp (Complex.I * (c : ℂ) * (x : ℂ))‖
        + ‖radialInteractionMinus c W V x * Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ))‖ :=
        norm_add_le _ _
    _ = radialInteractionTotal c W V x := by
        rw [norm_mul, norm_mul, norm_exp_I_mul, norm_exp_neg_I_mul, radialInteractionTotal]
        ring

/-- The norm of the transport derivative. -/
theorem norm_transport_deriv (hc : 0 < c) (psi W : ℝ → ℂ) (x : ℝ) :
    ‖Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x / (2 * Complex.I * (c : ℂ))‖
      = ‖psi x‖ * ‖W x‖ / (2 * c) := by
  rw [norm_div, norm_mul, norm_mul, norm_exp_neg_I_mul, one_mul]
  congr 1
  simp [abs_of_pos hc]

theorem norm_transport_deriv_neg (hc : 0 < c) (psi W : ℝ → ℂ) (x : ℝ) :
    ‖-Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x / (2 * Complex.I * (c : ℂ))‖
      = ‖psi x‖ * ‖W x‖ / (2 * c) := by
  rw [norm_div, norm_mul, norm_mul, norm_neg, norm_exp_I_mul, one_mul]
  congr 1
  simp [abs_of_pos hc]

/-! ## The real two-branch form -/

/-- The cosine amplitude of a real solution. -/
def radialAmpCos (c : ℝ) (W V : ℝ → ℂ) (x : ℝ) : ℝ := 2 * (radialInteractionPlus c W V x).re

/-- The sine amplitude of a real solution. -/
def radialAmpSin (c : ℝ) (W V : ℝ → ℂ) (x : ℝ) : ℝ := -(2 * (radialInteractionPlus c W V x).im)

/-- **A real solution is a two-branch oscillation.**  Its cosine and sine amplitudes are twice the
real and minus twice the imaginary part of the positive-frequency interaction amplitude. -/
theorem realPart_eq_twoBranch {c : ℝ} (hc : c ≠ 0) {W V : ℝ → ℂ}
    (hWre : ∀ x, (W x).im = 0) (hVre : ∀ x, (V x).im = 0) (x : ℝ) :
    (W x).re = radialAmpCos c W V x * Real.cos (c * x)
      + radialAmpSin c W V x * Real.sin (c * x) := by
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hW : W x = (((W x).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hWre x]
  have hV : V x = (((V x).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hVre x]
  have hexp : Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ))
      = ((Real.cos (c * x) : ℝ) : ℂ) - ((Real.sin (c * x) : ℝ) : ℂ) * Complex.I := by
    have h : (-Complex.I * (c : ℂ) * (x : ℂ)) = ((-(c * x) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  set u : ℝ := (W x).re with hu
  set v : ℝ := (V x).re with hv
  set C : ℝ := Real.cos (c * x) with hCdef
  set S : ℝ := Real.sin (c * x) with hSdef
  have hpy : S ^ (2 : ℕ) + C ^ (2 : ℕ) = 1 := by
    rw [hSdef, hCdef]
    exact Real.sin_sq_add_cos_sq (c * x)
  have hval : radialInteractionPlus c W V x
      = ((1 / 2 * (u * C - v / c * S) : ℝ) : ℂ)
        + ((-(1 / 2) * (v / c * C + u * S) : ℝ) : ℂ) * Complex.I := by
    rw [radialInteractionPlus, hexp, hW, hV]
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [radialAmpCos, radialAmpSin, hval]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  linear_combination (-u) * hpy

theorem abs_radialAmpCos_le (c : ℝ) (W V : ℝ → ℂ) (x : ℝ) :
    |radialAmpCos c W V x| ≤ 2 * ‖radialInteractionPlus c W V x‖ := by
  rw [radialAmpCos, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)

theorem abs_radialAmpSin_le (c : ℝ) (W V : ℝ → ℂ) (x : ℝ) :
    |radialAmpSin c W V x| ≤ 2 * ‖radialInteractionPlus c W V x‖ := by
  rw [radialAmpSin, abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (by norm_num)

theorem hasDerivAt_radialAmpCos {c x : ℝ} (hc : c ≠ 0) {W V psi : ℝ → ℂ}
    (hW : HasDerivAt W (V x) x)
    (hV : HasDerivAt V ((psi x - (c : ℂ) ^ (2 : ℕ)) * W x) x) :
    HasDerivAt (radialAmpCos c W V)
      (2 * (Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x
        / (2 * Complex.I * (c : ℂ))).re) x := by
  have h := hasDerivAt_radialInteractionPlus hc hW hV
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h
  exact hre.const_mul 2

theorem hasDerivAt_radialAmpSin {c x : ℝ} (hc : c ≠ 0) {W V psi : ℝ → ℂ}
    (hW : HasDerivAt W (V x) x)
    (hV : HasDerivAt V ((psi x - (c : ℂ) ^ (2 : ℕ)) * W x) x) :
    HasDerivAt (radialAmpSin c W V)
      (-(2 * (Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x
        / (2 * Complex.I * (c : ℂ))).im)) x := by
  have h := hasDerivAt_radialInteractionPlus hc hW hV
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h
  exact (him.const_mul 2).neg

/-- The transported derivative of the cosine amplitude is `‖ψ‖‖W‖/c`. -/
theorem abs_transport_deriv_re_le {c : ℝ} (hc : 0 < c) (psi W : ℝ → ℂ) (x : ℝ) :
    |2 * (Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x
        / (2 * Complex.I * (c : ℂ))).re|
      ≤ ‖psi x‖ * ‖W x‖ / c := by
  have hnorm := norm_transport_deriv hc psi W x
  have hre := Complex.abs_re_le_norm
    (Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x / (2 * Complex.I * (c : ℂ)))
  rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have hstep : 2 * |(Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x
      / (2 * Complex.I * (c : ℂ))).re| ≤ 2 * (‖psi x‖ * ‖W x‖ / (2 * c)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact hre.trans hnorm.le
  have hval : (2 : ℝ) * (‖psi x‖ * ‖W x‖ / (2 * c)) = ‖psi x‖ * ‖W x‖ / c := by
    field_simp
  linarith [hstep, hval.le, hval.ge]

/-- The transported derivative of the sine amplitude obeys the same bound. -/
theorem abs_transport_deriv_im_le {c : ℝ} (hc : 0 < c) (psi W : ℝ → ℂ) (x : ℝ) :
    |(-(2 * (Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x
        / (2 * Complex.I * (c : ℂ))).im))|
      ≤ ‖psi x‖ * ‖W x‖ / c := by
  have hnorm := norm_transport_deriv hc psi W x
  have him := Complex.abs_im_le_norm
    (Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x / (2 * Complex.I * (c : ℂ)))
  rw [abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have hstep : 2 * |(Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x
      / (2 * Complex.I * (c : ℂ))).im| ≤ 2 * (‖psi x‖ * ‖W x‖ / (2 * c)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact him.trans hnorm.le
  have hval : (2 : ℝ) * (‖psi x‖ * ‖W x‖ / (2 * c)) = ‖psi x‖ * ‖W x‖ / c := by
    field_simp
  linarith [hstep, hval.le, hval.ge]

/-- **The transported derivative bound in symbol form.**  A short-range potential decaying like
`κ/x²` along the phase, a bounded solution, and a bounded phase speed give the `K'/x²` decay a
symbol record wants, with `K' = κ K L / c` — one power of the bandwidth small. -/
theorem abs_transport_deriv_comp_le {c κ K L x : ℝ} (hc : 0 < c) (hκ : 0 ≤ κ) (hK : 0 ≤ K)
    (hx : 0 < x) {psi W : ℝ → ℂ} {Φ Φ' : ℝ → ℝ}
    (hpsi : ‖psi (Φ x)‖ ≤ κ / x ^ (2 : ℕ)) (hWb : ‖W (Φ x)‖ ≤ K) (hΦ : |Φ' x| ≤ L) :
    |2 * (Complex.exp (-Complex.I * (c : ℂ) * ((Φ x : ℝ) : ℂ)) * psi (Φ x) * W (Φ x)
        / (2 * Complex.I * (c : ℂ))).re * Φ' x| ≤ (κ * K * L / c) / x ^ (2 : ℕ) := by
  have hL : (0 : ℝ) ≤ L := le_trans (abs_nonneg _) hΦ
  have hbase := abs_transport_deriv_re_le hc psi W (Φ x)
  have hmul : ‖psi (Φ x)‖ * ‖W (Φ x)‖ ≤ (κ / x ^ (2 : ℕ)) * K :=
    mul_le_mul hpsi hWb (norm_nonneg _) (by positivity)
  rw [abs_mul]
  have hstep : |2 * (Complex.exp (-Complex.I * (c : ℂ) * ((Φ x : ℝ) : ℂ)) * psi (Φ x) * W (Φ x)
      / (2 * Complex.I * (c : ℂ))).re| * |Φ' x|
      ≤ ((κ / x ^ (2 : ℕ)) * K / c) * L := by
    refine mul_le_mul ?_ hΦ (abs_nonneg _) (by positivity)
    refine hbase.trans ?_
    gcongr
  have hval : ((κ / x ^ (2 : ℕ)) * K / c) * L = (κ * K * L / c) / x ^ (2 : ℕ) := by
    field_simp
  linarith [hstep, hval.le, hval.ge]

section

variable (hc : 0 < c)
  (hW : ∀ x, HasDerivAt W (V x) x)
  (hV : ∀ x, HasDerivAt V ((psi x - (c : ℂ) ^ (2 : ℕ)) * W x) x)
  (hWc : Continuous W) (hpsic : Continuous psi)

include hc hW hV hWc hpsic

omit hWc hpsic in
theorem continuous_radialInteractionPlus : Continuous (radialInteractionPlus c W V) :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_radialInteractionPlus hc.ne' (hW x) (hV x)).continuousAt

omit hWc hpsic in
theorem continuous_radialInteractionMinus : Continuous (radialInteractionMinus c W V) :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_radialInteractionMinus hc.ne' (hW x) (hV x)).continuousAt

omit hWc hpsic in
theorem continuous_radialInteractionTotal : Continuous (radialInteractionTotal c W V) :=
  ((continuous_radialInteractionPlus hc hW hV).norm).add
    ((continuous_radialInteractionMinus hc hW hV).norm)

/-- The Volterra inequality satisfied by the total amplitude. -/
theorem radialInteractionTotal_volterra {a x : ℝ} (hax : a ≤ x) :
    radialInteractionTotal c W V x
      ≤ radialInteractionTotal c W V a
        + ∫ t in a..x, ‖psi t‖ / c * radialInteractionTotal c W V t := by
  have hcne : c ≠ 0 := hc.ne'
  have hdplus : Continuous fun t : ℝ =>
      Complex.exp (-Complex.I * (c : ℂ) * (t : ℂ)) * psi t * W t / (2 * Complex.I * (c : ℂ)) := by
    have h1 : Continuous fun t : ℝ => Complex.exp (-Complex.I * (c : ℂ) * (t : ℂ)) := by
      exact Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)
    exact ((h1.mul hpsic).mul hWc).div_const _
  have hdminus : Continuous fun t : ℝ =>
      -Complex.exp (Complex.I * (c : ℂ) * (t : ℂ)) * psi t * W t / (2 * Complex.I * (c : ℂ)) := by
    have h1 : Continuous fun t : ℝ => Complex.exp (Complex.I * (c : ℂ) * (t : ℂ)) := by
      exact Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)
    exact (((h1.neg).mul hpsic).mul hWc).div_const _
  have hfplus : radialInteractionPlus c W V x - radialInteractionPlus c W V a
      = ∫ t in a..x,
        Complex.exp (-Complex.I * (c : ℂ) * (t : ℂ)) * psi t * W t / (2 * Complex.I * (c : ℂ)) := by
    refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ =>
      hasDerivAt_radialInteractionPlus hcne (hW t) (hV t)) ?_).symm
    exact hdplus.intervalIntegrable a x
  have hfminus : radialInteractionMinus c W V x - radialInteractionMinus c W V a
      = ∫ t in a..x,
        -Complex.exp (Complex.I * (c : ℂ) * (t : ℂ)) * psi t * W t / (2 * Complex.I * (c : ℂ)) := by
    refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ =>
      hasDerivAt_radialInteractionMinus hcne (hW t) (hV t)) ?_).symm
    exact hdminus.intervalIntegrable a x
  have hboundplus : ‖radialInteractionPlus c W V x - radialInteractionPlus c W V a‖
      ≤ ∫ t in a..x, ‖psi t‖ * ‖W t‖ / (2 * c) := by
    rw [hfplus]
    refine (intervalIntegral.norm_integral_le_abs_integral_norm).trans ?_
    have hcongr : (∫ t in a..x, ‖Complex.exp (-Complex.I * (c : ℂ) * (t : ℂ)) * psi t * W t
        / (2 * Complex.I * (c : ℂ))‖) = ∫ t in a..x, ‖psi t‖ * ‖W t‖ / (2 * c) :=
      intervalIntegral.integral_congr fun t _ => norm_transport_deriv hc psi W t
    rw [hcongr]
    refine abs_of_nonneg ?_ |>.le
    refine intervalIntegral.integral_nonneg hax fun t _ => ?_
    positivity
  have hboundminus : ‖radialInteractionMinus c W V x - radialInteractionMinus c W V a‖
      ≤ ∫ t in a..x, ‖psi t‖ * ‖W t‖ / (2 * c) := by
    rw [hfminus]
    refine (intervalIntegral.norm_integral_le_abs_integral_norm).trans ?_
    have hcongr : (∫ t in a..x, ‖-Complex.exp (Complex.I * (c : ℂ) * (t : ℂ)) * psi t * W t
        / (2 * Complex.I * (c : ℂ))‖) = ∫ t in a..x, ‖psi t‖ * ‖W t‖ / (2 * c) :=
      intervalIntegral.integral_congr fun t _ => norm_transport_deriv_neg hc psi W t
    rw [hcongr]
    refine abs_of_nonneg ?_ |>.le
    refine intervalIntegral.integral_nonneg hax fun t _ => ?_
    positivity
  have hsplit : (∫ t in a..x, ‖psi t‖ * ‖W t‖ / (2 * c))
      + ∫ t in a..x, ‖psi t‖ * ‖W t‖ / (2 * c)
      = ∫ t in a..x, ‖psi t‖ * ‖W t‖ / c := by
    have h2 : (∫ t in a..x, ‖psi t‖ * ‖W t‖ / c)
        = 2 * ∫ t in a..x, ‖psi t‖ * ‖W t‖ / (2 * c) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      field_simp
    rw [h2]
    ring
  have hmono : (∫ t in a..x, ‖psi t‖ * ‖W t‖ / c)
      ≤ ∫ t in a..x, ‖psi t‖ / c * radialInteractionTotal c W V t := by
    refine intervalIntegral.integral_mono_on hax
      ((hpsic.norm.mul hWc.norm).div_const c |>.intervalIntegrable a x)
      (((hpsic.norm.div_const c).mul
        (continuous_radialInteractionTotal hc hW hV)).intervalIntegrable a x)
      fun t _ => ?_
    have hWt := norm_le_radialInteractionTotal (c := c) hcne W V t
    have hpsinn : (0 : ℝ) ≤ ‖psi t‖ := norm_nonneg _
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hc]
    exact mul_le_mul_of_nonneg_left hWt hpsinn
  have hplus : ‖radialInteractionPlus c W V x‖
      ≤ ‖radialInteractionPlus c W V a‖ + ∫ t in a..x, ‖psi t‖ * ‖W t‖ / (2 * c) := by
    have := norm_sub_norm_le (radialInteractionPlus c W V x) (radialInteractionPlus c W V a)
    linarith [hboundplus]
  have hminus : ‖radialInteractionMinus c W V x‖
      ≤ ‖radialInteractionMinus c W V a‖ + ∫ t in a..x, ‖psi t‖ * ‖W t‖ / (2 * c) := by
    have := norm_sub_norm_le (radialInteractionMinus c W V x) (radialInteractionMinus c W V a)
    linarith [hboundminus]
  have hgx : radialInteractionTotal c W V x
      = ‖radialInteractionPlus c W V x‖ + ‖radialInteractionMinus c W V x‖ := rfl
  have hga : radialInteractionTotal c W V a
      = ‖radialInteractionPlus c W V a‖ + ‖radialInteractionMinus c W V a‖ := rfl
  rw [hgx, hga]
  linarith [hplus, hminus, hsplit.le, hsplit.ge, hmono]

/-- **The amplitudes stay inside the error-control exponential.** -/
theorem radialInteractionTotal_le_exp {a b : ℝ} (hab : a ≤ b) :
    ∀ x ∈ Icc a b, radialInteractionTotal c W V x
      ≤ radialInteractionTotal c W V a * Real.exp ((1 / c) * ∫ t in a..x, ‖psi t‖) := by
  have hAc := continuous_radialInteractionTotal hc hW hV
  have hφc : Continuous fun t : ℝ => ‖psi t‖ / c := hpsic.norm.div_const c
  have hφ0 : ∀ t : ℝ, 0 ≤ ‖psi t‖ / c := fun t => div_nonneg (norm_nonneg _) hc.le
  have hbd : ∀ x ∈ Icc a b, |radialInteractionTotal c W V x|
      ≤ radialInteractionTotal c W V a
        + ∫ t in a..x, (‖psi t‖ / c) * |radialInteractionTotal c W V t| := by
    intro x hx
    have habs : ∀ t : ℝ, |radialInteractionTotal c W V t| = radialInteractionTotal c W V t :=
      fun t => abs_of_nonneg (radialInteractionTotal_nonneg c W V t)
    rw [habs x]
    have hcongr : (∫ t in a..x, (‖psi t‖ / c) * |radialInteractionTotal c W V t|)
        = ∫ t in a..x, (‖psi t‖ / c) * radialInteractionTotal c W V t :=
      intervalIntegral.integral_congr fun t _ => by rw [habs t]
    rw [hcongr]
    exact radialInteractionTotal_volterra hc hW hV hWc hpsic hx.1
  intro x hx
  have hmain := abs_le_const_mul_exp_of_volterra_bound hab
    (radialInteractionTotal_nonneg c W V a) hAc hφc hφ0 hbd x hx
  rw [abs_of_nonneg (radialInteractionTotal_nonneg c W V x)] at hmain
  have hint : (∫ t in a..x, ‖psi t‖ / c) = (1 / c) * ∫ t in a..x, ‖psi t‖ := by
    rw [intervalIntegral.integral_div, one_div, inv_mul_eq_div]
  rwa [hint] at hmain

/-- **The total variation of each amplitude is one power of the bandwidth small.** -/
theorem integral_norm_deriv_radialInteraction_le {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, ‖psi t‖ * ‖W t‖ / (2 * c))
      ≤ radialInteractionTotal c W V a
        * (Real.exp ((1 / c) * ∫ t in a..b, ‖psi t‖) - 1) / 2 := by
  have hAc := continuous_radialInteractionTotal hc hW hV
  have hAnn : ∀ t : ℝ, 0 ≤ radialInteractionTotal c W V t := radialInteractionTotal_nonneg c W V
  have hmono : (∫ t in a..b, ‖psi t‖ * ‖W t‖ / (2 * c))
      ≤ ∫ t in a..b, ‖psi t‖ * radialInteractionTotal c W V t / (2 * c) := by
    refine intervalIntegral.integral_mono_on hab
      ((hpsic.norm.mul hWc.norm).div_const (2 * c) |>.intervalIntegrable a b)
      ((hpsic.norm.mul hAc).div_const (2 * c) |>.intervalIntegrable a b) fun t _ => ?_
    have hWt := norm_le_radialInteractionTotal (c := c) hc.ne' W V t
    have h2c : (0 : ℝ) < 2 * c := by linarith
    rw [div_le_div_iff_of_pos_right h2c]
    exact mul_le_mul_of_nonneg_left hWt (norm_nonneg _)
  have henv : ∀ t ∈ Icc a b, radialInteractionTotal c W V t
      ≤ radialInteractionTotal c W V a * Real.exp ((1 / c) * ∫ s in a..t, ‖psi s‖) :=
    radialInteractionTotal_le_exp hc hW hV hWc hpsic hab
  have hgrow : ∀ t ∈ Icc a b, ‖psi t‖ * radialInteractionTotal c W V t / (2 * c)
      ≤ radialInteractionTotal c W V a
        * ((‖psi t‖ / c) * Real.exp ((1 / c) * ∫ s in a..t, ‖psi s‖)) / 2 := by
    intro t ht
    have h2c : (0 : ℝ) < 2 * c := by linarith
    have h := henv t ht
    have hpsinn : (0 : ℝ) ≤ ‖psi t‖ := norm_nonneg _
    have hkey : ‖psi t‖ * radialInteractionTotal c W V t
        ≤ ‖psi t‖ * (radialInteractionTotal c W V a
          * Real.exp ((1 / c) * ∫ s in a..t, ‖psi s‖)) :=
      mul_le_mul_of_nonneg_left h hpsinn
    have hrhs : radialInteractionTotal c W V a
        * ((‖psi t‖ / c) * Real.exp ((1 / c) * ∫ s in a..t, ‖psi s‖)) / 2
        = (‖psi t‖ * (radialInteractionTotal c W V a
            * Real.exp ((1 / c) * ∫ s in a..t, ‖psi s‖))) / (2 * c) := by
      field_simp
    rw [hrhs, div_le_div_iff_of_pos_right h2c]
    exact hkey
  have hprim : ∀ t : ℝ, HasDerivAt (fun u : ℝ =>
      Real.exp ((1 / c) * ∫ s in a..u, ‖psi s‖))
      ((‖psi t‖ / c) * Real.exp ((1 / c) * ∫ s in a..t, ‖psi s‖)) t := by
    intro t
    have hI : HasDerivAt (fun u : ℝ => ∫ s in a..u, ‖psi s‖) ‖psi t‖ t :=
      intervalIntegral.integral_hasDerivAt_right
        (hpsic.norm.intervalIntegrable a t)
        (hpsic.norm.stronglyMeasurableAtFilter volume (nhds t))
        hpsic.norm.continuousAt
    have h := ((hI.const_mul (1 / c)).exp)
    convert h using 1
    field_simp
  have hFTC : (∫ t in a..b, (‖psi t‖ / c) * Real.exp ((1 / c) * ∫ s in a..t, ‖psi s‖))
      = Real.exp ((1 / c) * ∫ s in a..b, ‖psi s‖) - 1 := by
    have hcontd : Continuous fun t : ℝ =>
        (‖psi t‖ / c) * Real.exp ((1 / c) * ∫ s in a..t, ‖psi s‖) := by
      refine (hpsic.norm.div_const c).mul ?_
      exact Real.continuous_exp.comp
        ((intervalIntegral.continuous_primitive
          (fun u v => hpsic.norm.intervalIntegrable u v) a).const_mul (1 / c))
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hprim t)
      (hcontd.intervalIntegrable a b)
    rw [h]
    simp
  have hstep : (∫ t in a..b, ‖psi t‖ * radialInteractionTotal c W V t / (2 * c))
      ≤ ∫ t in a..b, radialInteractionTotal c W V a
        * ((‖psi t‖ / c) * Real.exp ((1 / c) * ∫ s in a..t, ‖psi s‖)) / 2 := by
    refine intervalIntegral.integral_mono_on hab
      ((hpsic.norm.mul hAc).div_const (2 * c) |>.intervalIntegrable a b) ?_ hgrow
    have hcontd : Continuous fun t : ℝ =>
        radialInteractionTotal c W V a
          * ((‖psi t‖ / c) * Real.exp ((1 / c) * ∫ s in a..t, ‖psi s‖)) / 2 := by
      refine (Continuous.mul continuous_const ((hpsic.norm.div_const c).mul ?_)).div_const 2
      exact Real.continuous_exp.comp
        ((intervalIntegral.continuous_primitive
          (fun u v => hpsic.norm.intervalIntegrable u v) a).const_mul (1 / c))
    exact hcontd.intervalIntegrable a b
  have hfinal : (∫ t in a..b, radialInteractionTotal c W V a
      * ((‖psi t‖ / c) * Real.exp ((1 / c) * ∫ s in a..t, ‖psi s‖)) / 2)
      = radialInteractionTotal c W V a
        * (Real.exp ((1 / c) * ∫ s in a..b, ‖psi s‖) - 1) / 2 := by
    have hpull : (∫ t in a..b, radialInteractionTotal c W V a
        * ((‖psi t‖ / c) * Real.exp ((1 / c) * ∫ s in a..t, ‖psi s‖)) / 2)
        = (radialInteractionTotal c W V a / 2)
          * ∫ t in a..b, (‖psi t‖ / c) * Real.exp ((1 / c) * ∫ s in a..t, ‖psi s‖) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      ring
    rw [hpull, hFTC]
    ring
  linarith [hmono, hstep, hfinal.le, hfinal.ge]

end

end RHTower

end
