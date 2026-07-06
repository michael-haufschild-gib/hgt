/-
The argument principle on a rectangle: the boundary winding of the logarithmic derivative
counts the enclosed zeros.

The Cauchy kernel `(z − p)⁻¹` has an explicit antiderivative on any half-plane avoiding `p`.
Covering the rectangle boundary by its four edges, the three edges on which `z − p` stays off
the negative real ray use `log(z − p)`; the left edge, where `Re(z − p) < 0`, uses the rotated
branch `log(−(z − p))` (its argument `−(z − p)` lies in the right half-plane).  Both branches
have derivative `(z − p)⁻¹`, so each edge integral is a difference of branch values, and the two
branches disagree by `πi` at each of the two left corners (`arg` of a negation).  The four edge
contributions telescope to `2πi`: the rectangle boundary winds once around any interior point.

Peeling the finitely many zeros of an analytic function off a nonvanishing cofactor turns its
logarithmic derivative into a sum of Cauchy kernels plus a boundary-holomorphic term (whose
boundary integral vanishes by the rectangle Cauchy theorem), giving the argument principle:
`∮_{∂R} f'/f = 2πi · Σ orders`.
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import GaloisForLFunctions.RHTower.Peeling

open Complex intervalIntegral Set

namespace RHTower

/-! ### §1 Branch antiderivatives of the Cauchy kernel -/

/-- On the slit plane, `log(z − p)` is an antiderivative of `(z − p)⁻¹`. -/
private theorem hasDerivAt_logSub {p z : ℂ} (h : z - p ∈ slitPlane) :
    HasDerivAt (fun z => Complex.log (z - p)) (z - p)⁻¹ z := by
  simpa using (Complex.hasDerivAt_log h).comp z ((hasDerivAt_id z).sub_const p)

/-- Where `−(z − p)` is in the slit plane, `log(−(z − p))` is an antiderivative of `(z − p)⁻¹`. -/
private theorem hasDerivAt_logNegSub {p z : ℂ} (h : -(z - p) ∈ slitPlane) :
    HasDerivAt (fun z => Complex.log (-(z - p))) (z - p)⁻¹ z := by
  have hc := (Complex.hasDerivAt_log h).comp z (((hasDerivAt_id z).sub_const p).neg)
  have hval : (-(z - p))⁻¹ * (-1) = (z - p)⁻¹ := by rw [inv_neg]; ring
  rw [hval] at hc; exact hc

private theorem negI_mul_I : (-I) * I = (1 : ℂ) := by rw [neg_mul, Complex.I_mul_I, neg_neg]

private theorem I_mul_negI : I * -I = (1 : ℂ) := by rw [mul_neg, Complex.I_mul_I, neg_neg]

/-! ### §2 The four edge integrals -/

/-- A horizontal edge integral of the Cauchy kernel, via the `log(z − p)` branch. -/
private theorem integral_horizontal {p : ℂ} {h a b : ℝ}
    (hslit : ∀ x ∈ uIcc a b, ((x : ℂ) + h * I) - p ∈ slitPlane) :
    (∫ x in a..b, ((x : ℂ) + h * I - p)⁻¹) =
      Complex.log ((b : ℂ) + h * I - p) - Complex.log ((a : ℂ) + h * I - p) := by
  have hHD : ∀ x ∈ uIcc a b,
      HasDerivAt (fun x : ℝ => Complex.log ((x : ℂ) + h * I - p))
        (((x : ℂ) + h * I - p)⁻¹) x := by
    intro x hx
    have hin : HasDerivAt (fun x : ℝ => (x : ℂ) + (h : ℂ) * I) 1 x := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((h : ℂ) * I))
    have hout := hasDerivAt_logSub (hslit x hx)
    simpa using hout.comp x hin
  have hcont : ContinuousOn (fun x : ℝ => ((x : ℂ) + h * I - p)⁻¹) (uIcc a b) :=
    (continuousOn_of_forall_continuousAt (fun x => by fun_prop)).inv₀
      (fun x hx => slitPlane_ne_zero (hslit x hx))
  rw [integral_eq_sub_of_hasDerivAt hHD hcont.intervalIntegrable]

/-- A vertical edge integral of the Cauchy kernel via the `log(z − p)` branch, weighted by `I`
as in the rectangle boundary. -/
private theorem integral_vertical_A {p : ℂ} {v a b : ℝ}
    (hslit : ∀ y ∈ uIcc a b, ((v : ℂ) + y * I) - p ∈ slitPlane) :
    I • (∫ y in a..b, ((v : ℂ) + y * I - p)⁻¹) =
      Complex.log ((v : ℂ) + b * I - p) - Complex.log ((v : ℂ) + a * I - p) := by
  have hHD : ∀ y ∈ uIcc a b,
      HasDerivAt (fun y : ℝ => -I * Complex.log ((v : ℂ) + y * I - p))
        (((v : ℂ) + y * I - p)⁻¹) y := by
    intro y hy
    have hin : HasDerivAt (fun y : ℝ => (v : ℂ) + (y : ℂ) * I) I y := by
      have : HasDerivAt (fun y : ℝ => (y : ℂ) * I) I y := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I
      simpa using this.const_add ((v : ℂ))
    have hout := hasDerivAt_logSub (hslit y hy)
    have hchain := hout.comp y hin
    have := (hchain.const_mul (-I))
    have hval : -I * (((v : ℂ) + y * I - p)⁻¹ * I) = ((v : ℂ) + y * I - p)⁻¹ := by
      calc -I * (((v : ℂ) + y * I - p)⁻¹ * I)
          = ((-I) * I) * ((v : ℂ) + y * I - p)⁻¹ := by ring
        _ = ((v : ℂ) + y * I - p)⁻¹ := by rw [negI_mul_I, one_mul]
    simpa [hval] using this
  have hcont : ContinuousOn (fun y : ℝ => ((v : ℂ) + y * I - p)⁻¹) (uIcc a b) :=
    (continuousOn_of_forall_continuousAt (fun y => by fun_prop)).inv₀
      (fun y hy => slitPlane_ne_zero (hslit y hy))
  rw [integral_eq_sub_of_hasDerivAt hHD hcont.intervalIntegrable, smul_eq_mul, mul_sub]
  rw [show I * (-I * Complex.log ((v : ℂ) + b * I - p)) = Complex.log ((v : ℂ) + b * I - p) by
        rw [show I * (-I * Complex.log ((v : ℂ) + b * I - p)) =
          (I * -I) * Complex.log ((v : ℂ) + b * I - p) by ring, I_mul_negI, one_mul],
      show I * (-I * Complex.log ((v : ℂ) + a * I - p)) = Complex.log ((v : ℂ) + a * I - p) by
        rw [show I * (-I * Complex.log ((v : ℂ) + a * I - p)) =
          (I * -I) * Complex.log ((v : ℂ) + a * I - p) by ring, I_mul_negI, one_mul]]

/-- A vertical edge integral of the Cauchy kernel via the rotated `log(−(z − p))` branch. -/
private theorem integral_vertical_B {p : ℂ} {v a b : ℝ}
    (hslit : ∀ y ∈ uIcc a b, -((v : ℂ) + y * I - p) ∈ slitPlane) :
    I • (∫ y in a..b, ((v : ℂ) + y * I - p)⁻¹) =
      Complex.log (-((v : ℂ) + b * I - p)) - Complex.log (-((v : ℂ) + a * I - p)) := by
  have hHD : ∀ y ∈ uIcc a b,
      HasDerivAt (fun y : ℝ => -I * Complex.log (-((v : ℂ) + y * I - p)))
        (((v : ℂ) + y * I - p)⁻¹) y := by
    intro y hy
    have hin : HasDerivAt (fun y : ℝ => (v : ℂ) + (y : ℂ) * I) I y := by
      have : HasDerivAt (fun y : ℝ => (y : ℂ) * I) I y := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I
      simpa using this.const_add ((v : ℂ))
    have hout := hasDerivAt_logNegSub (hslit y hy)
    have hchain := hout.comp y hin
    have := (hchain.const_mul (-I))
    have hval : -I * (((v : ℂ) + y * I - p)⁻¹ * I) = ((v : ℂ) + y * I - p)⁻¹ := by
      calc -I * (((v : ℂ) + y * I - p)⁻¹ * I)
          = ((-I) * I) * ((v : ℂ) + y * I - p)⁻¹ := by ring
        _ = ((v : ℂ) + y * I - p)⁻¹ := by rw [negI_mul_I, one_mul]
    simpa [hval] using this
  have hcont : ContinuousOn (fun y : ℝ => ((v : ℂ) + y * I - p)⁻¹) (uIcc a b) :=
    (continuousOn_of_forall_continuousAt (fun y => by fun_prop)).inv₀
      (fun y hy => neg_ne_zero.mp (slitPlane_ne_zero (hslit y hy)))
  rw [integral_eq_sub_of_hasDerivAt hHD hcont.intervalIntegrable, smul_eq_mul, mul_sub]
  rw [show I * (-I * Complex.log (-((v : ℂ) + b * I - p))) = Complex.log (-((v : ℂ) + b * I - p)) by
        rw [show I * (-I * Complex.log (-((v : ℂ) + b * I - p))) =
          (I * -I) * Complex.log (-((v : ℂ) + b * I - p)) by ring, I_mul_negI, one_mul],
      show I * (-I * Complex.log (-((v : ℂ) + a * I - p))) = Complex.log (-((v : ℂ) + a * I - p)) by
        rw [show I * (-I * Complex.log (-((v : ℂ) + a * I - p))) =
          (I * -I) * Complex.log (-((v : ℂ) + a * I - p)) by ring, I_mul_negI, one_mul]]

/-! ### §3 The two corner branch mismatches -/

/-- In the second quadrant the two branches differ by `πi`. -/
private theorem log_sub_log_neg_of_im_pos {ζ : ℂ} (him : 0 < ζ.im) :
    Complex.log ζ - Complex.log (-ζ) = Real.pi * I := by
  rw [Complex.log, Complex.log, norm_neg, Complex.arg_neg_eq_arg_sub_pi_of_im_pos him]
  push_cast; ring

/-- In the third quadrant the two branches differ by `−πi`. -/
private theorem log_sub_log_neg_of_im_neg {ζ : ℂ} (him : ζ.im < 0) :
    Complex.log ζ - Complex.log (-ζ) = -(Real.pi * I) := by
  rw [Complex.log, Complex.log, norm_neg, Complex.arg_neg_eq_arg_add_pi_of_im_neg him]
  push_cast; ring

/-! ### §4 The rectangle winding number of the Cauchy kernel -/

private theorem horizontal_pt_im (x h pim : ℝ) (pre : ℝ) :
    ((x : ℂ) + (h : ℂ) * I - (⟨pre, pim⟩ : ℂ)).im = h - pim := by
  simp [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]

/-- **The rectangle winds once.**  For `p` strictly inside the axis-aligned rectangle with
lower-left corner `z₁` and upper-right corner `z₂`, the boundary contour integral of the Cauchy
kernel is `2πi`. -/
theorem rectangle_winding {p z₁ z₂ : ℂ}
    (hre1 : z₁.re < p.re) (hre2 : p.re < z₂.re)
    (him1 : z₁.im < p.im) (him2 : p.im < z₂.im) :
    (((∫ x in z₁.re..z₂.re, ((x : ℂ) + z₁.im * I - p)⁻¹) -
          ∫ x in z₁.re..z₂.re, ((x : ℂ) + z₂.im * I - p)⁻¹) +
        I • ∫ y in z₁.im..z₂.im, ((z₂.re : ℂ) + y * I - p)⁻¹) -
      I • ∫ y in z₁.im..z₂.im, ((z₁.re : ℂ) + y * I - p)⁻¹ =
      2 * Real.pi * I := by
  have him_bot : ∀ x : ℝ, ((x : ℂ) + (z₁.im : ℂ) * I - p).im = z₁.im - p.im := fun x => by
    simp [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  have him_top : ∀ x : ℝ, ((x : ℂ) + (z₂.im : ℂ) * I - p).im = z₂.im - p.im := fun x => by
    simp [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  have hre_right : ∀ y : ℝ, ((z₂.re : ℂ) + (y : ℂ) * I - p).re = z₂.re - p.re := fun y => by
    simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  have hre_left : ∀ y : ℝ, (-((z₁.re : ℂ) + (y : ℂ) * I - p)).re = p.re - z₁.re := fun y => by
    simp [Complex.neg_re, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
  -- slit-plane data on the four edges
  have hbot : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + (z₁.im : ℂ) * I) - p ∈ slitPlane := fun x _ =>
    Complex.mem_slitPlane_iff.mpr (Or.inr (by rw [him_bot]; linarith))
  have htop : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + (z₂.im : ℂ) * I) - p ∈ slitPlane := fun x _ =>
    Complex.mem_slitPlane_iff.mpr (Or.inr (by rw [him_top]; linarith))
  have hright : ∀ y ∈ uIcc z₁.im z₂.im, ((z₂.re : ℂ) + (y : ℂ) * I) - p ∈ slitPlane := fun y _ =>
    Complex.mem_slitPlane_iff.mpr (Or.inl (by rw [hre_right]; linarith))
  have hleft : ∀ y ∈ uIcc z₁.im z₂.im, -((z₁.re : ℂ) + (y : ℂ) * I - p) ∈ slitPlane := fun y _ =>
    Complex.mem_slitPlane_iff.mpr (Or.inl (by rw [hre_left]; linarith))
  rw [integral_horizontal hbot, integral_horizontal htop, integral_vertical_A hright,
    integral_vertical_B hleft]
  have hTL : Complex.log ((z₁.re : ℂ) + z₂.im * I - p) -
      Complex.log (-((z₁.re : ℂ) + z₂.im * I - p)) = Real.pi * I :=
    log_sub_log_neg_of_im_pos (by rw [him_top]; linarith)
  have hBL : Complex.log ((z₁.re : ℂ) + z₁.im * I - p) -
      Complex.log (-((z₁.re : ℂ) + z₁.im * I - p)) = -(Real.pi * I) :=
    log_sub_log_neg_of_im_neg (by rw [him_bot]; linarith)
  linear_combination hTL - hBL

end RHTower
