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
    simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
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

namespace RHTower

open Complex intervalIntegral Set

/-! ### §5 The boundary contour integral and the residue theorem -/

/-- The positively-oriented boundary contour integral of `g` around the axis-aligned rectangle
with corners `z₁` (lower-left) and `z₂` (upper-right). -/
noncomputable def rectIntegral (g : ℂ → ℂ) (z₁ z₂ : ℂ) : ℂ :=
  (((∫ x in z₁.re..z₂.re, g ((x : ℂ) + z₁.im * I)) - ∫ x in z₁.re..z₂.re, g ((x : ℂ) + z₂.im * I)) +
      I • ∫ y in z₁.im..z₂.im, g ((z₂.re : ℂ) + y * I)) -
    I • ∫ y in z₁.im..z₂.im, g ((z₁.re : ℂ) + y * I)

/-- The boundary integral of the Cauchy kernel around a rectangle enclosing `p` is `2πi`. -/
theorem rectIntegral_cauchyKernel {p z₁ z₂ : ℂ}
    (hre1 : z₁.re < p.re) (hre2 : p.re < z₂.re)
    (him1 : z₁.im < p.im) (him2 : p.im < z₂.im) :
    rectIntegral (fun z => (z - p)⁻¹) z₁ z₂ = 2 * Real.pi * I := by
  unfold rectIntegral
  simpa using rectangle_winding hre1 hre2 him1 him2

/-- **Rectangle Cauchy theorem.** A function holomorphic on a neighbourhood of the closed
rectangle has vanishing boundary integral. -/
theorem rectIntegral_eq_zero_of_analyticOnNhd {g : ℂ → ℂ} {z₁ z₂ : ℂ} {U : Set ℂ}
    (hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U)
    (hg : AnalyticOnNhd ℂ g U) :
    rectIntegral g z₁ z₂ = 0 := by
  refine integral_boundary_rect_eq_zero_of_differentiable_on_off_countable g z₁ z₂ ∅
    countable_empty ?_ ?_
  · exact (hg.mono hsub).continuousOn
  · intro x hx
    have hxU : x ∈ U := hsub (by
      rcases hx.1 with ⟨h1, h2⟩
      exact ⟨Ioo_subset_Icc_self h1, Ioo_subset_Icc_self h2⟩)
    exact (hg x hxU).differentiableAt

/-- Boundary integrals are additive, given edgewise integrability. -/
theorem rectIntegral_add {g₁ g₂ : ℂ → ℂ} {z₁ z₂ : ℂ}
    (hb1 : IntervalIntegrable (fun x : ℝ => g₁ ((x : ℂ) + z₁.im * I)) MeasureTheory.volume z₁.re z₂.re)
    (hb2 : IntervalIntegrable (fun x : ℝ => g₂ ((x : ℂ) + z₁.im * I)) MeasureTheory.volume z₁.re z₂.re)
    (ht1 : IntervalIntegrable (fun x : ℝ => g₁ ((x : ℂ) + z₂.im * I)) MeasureTheory.volume z₁.re z₂.re)
    (ht2 : IntervalIntegrable (fun x : ℝ => g₂ ((x : ℂ) + z₂.im * I)) MeasureTheory.volume z₁.re z₂.re)
    (hr1 : IntervalIntegrable (fun y : ℝ => g₁ ((z₂.re : ℂ) + y * I)) MeasureTheory.volume z₁.im z₂.im)
    (hr2 : IntervalIntegrable (fun y : ℝ => g₂ ((z₂.re : ℂ) + y * I)) MeasureTheory.volume z₁.im z₂.im)
    (hl1 : IntervalIntegrable (fun y : ℝ => g₁ ((z₁.re : ℂ) + y * I)) MeasureTheory.volume z₁.im z₂.im)
    (hl2 : IntervalIntegrable (fun y : ℝ => g₂ ((z₁.re : ℂ) + y * I)) MeasureTheory.volume z₁.im z₂.im) :
    rectIntegral (fun z => g₁ z + g₂ z) z₁ z₂ = rectIntegral g₁ z₁ z₂ + rectIntegral g₂ z₁ z₂ := by
  have eb : (∫ x in z₁.re..z₂.re, g₁ ((x : ℂ) + z₁.im * I) + g₂ ((x : ℂ) + z₁.im * I)) =
      (∫ x in z₁.re..z₂.re, g₁ ((x : ℂ) + z₁.im * I)) +
        ∫ x in z₁.re..z₂.re, g₂ ((x : ℂ) + z₁.im * I) := integral_add hb1 hb2
  have et : (∫ x in z₁.re..z₂.re, g₁ ((x : ℂ) + z₂.im * I) + g₂ ((x : ℂ) + z₂.im * I)) =
      (∫ x in z₁.re..z₂.re, g₁ ((x : ℂ) + z₂.im * I)) +
        ∫ x in z₁.re..z₂.re, g₂ ((x : ℂ) + z₂.im * I) := integral_add ht1 ht2
  have er : (∫ y in z₁.im..z₂.im, g₁ ((z₂.re : ℂ) + y * I) + g₂ ((z₂.re : ℂ) + y * I)) =
      (∫ y in z₁.im..z₂.im, g₁ ((z₂.re : ℂ) + y * I)) +
        ∫ y in z₁.im..z₂.im, g₂ ((z₂.re : ℂ) + y * I) := integral_add hr1 hr2
  have el : (∫ y in z₁.im..z₂.im, g₁ ((z₁.re : ℂ) + y * I) + g₂ ((z₁.re : ℂ) + y * I)) =
      (∫ y in z₁.im..z₂.im, g₁ ((z₁.re : ℂ) + y * I)) +
        ∫ y in z₁.im..z₂.im, g₂ ((z₁.re : ℂ) + y * I) := integral_add hl1 hl2
  unfold rectIntegral
  dsimp only
  rw [eb, et, er, el, smul_add, smul_add]
  ring

/-- Boundary integrals commute with scalar multiplication. -/
theorem rectIntegral_const_mul (c : ℂ) (g : ℂ → ℂ) (z₁ z₂ : ℂ) :
    rectIntegral (fun z => c * g z) z₁ z₂ = c * rectIntegral g z₁ z₂ := by
  unfold rectIntegral
  rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  simp only [smul_eq_mul]; ring

/-- Boundary integrals depend only on the values on the four edges. -/
theorem rectIntegral_congr {g₁ g₂ : ℂ → ℂ} {z₁ z₂ : ℂ} {S : Set ℂ}
    (hg : ∀ z ∈ S, g₁ z = g₂ z)
    (hb : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + z₁.im * I) ∈ S)
    (ht : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + z₂.im * I) ∈ S)
    (hr : ∀ y ∈ uIcc z₁.im z₂.im, ((z₂.re : ℂ) + y * I) ∈ S)
    (hl : ∀ y ∈ uIcc z₁.im z₂.im, ((z₁.re : ℂ) + y * I) ∈ S) :
    rectIntegral g₁ z₁ z₂ = rectIntegral g₂ z₁ z₂ := by
  unfold rectIntegral
  rw [integral_congr (fun x hx => hg _ (hb x hx)), integral_congr (fun x hx => hg _ (ht x hx)),
    integral_congr (fun y hy => hg _ (hr y hy)), integral_congr (fun y hy => hg _ (hl y hy))]

end RHTower

namespace RHTower

open Complex intervalIntegral Set

/-! ### §6 The rectangle residue theorem (argument principle) -/

private theorem edgePt_re (x c : ℝ) : ((x : ℂ) + (c : ℂ) * I).re = x := by
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]

private theorem edgePt_im (x c : ℝ) : ((x : ℂ) + (c : ℂ) * I).im = c := by
  simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]

/-- **The rectangle residue theorem.**  If `h` is analytic and nonvanishing on a neighbourhood of
the closed rectangle with corners `z₁ z₂`, and `ρ` is strictly inside, then the boundary contour
integral of the logarithmic derivative of `(·−ρ)^m · h` is `2πi · m`: the winding of `f'/f`
counts the enclosed zero with its multiplicity. -/
theorem rectIntegral_logDeriv_single_zero {h : ℂ → ℂ} {ρ z₁ z₂ : ℂ} {m : ℕ} {U : Set ℂ}
    (hre1 : z₁.re < ρ.re) (hre2 : ρ.re < z₂.re) (him1 : z₁.im < ρ.im) (him2 : ρ.im < z₂.im)
    (hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U)
    (hh : AnalyticOnNhd ℂ h U) (hh0 : ∀ z ∈ U, h z ≠ 0) :
    rectIntegral (logDeriv (fun z => (z - ρ) ^ m * h z)) z₁ z₂ = 2 * Real.pi * I * m := by
  have hz12re : z₁.re ≤ z₂.re := le_of_lt (lt_trans hre1 hre2)
  have hz12im : z₁.im ≤ z₂.im := le_of_lt (lt_trans him1 him2)
  -- analyticity and continuity of the logarithmic derivative of the cofactor
  have hlogh : AnalyticOnNhd ℂ (logDeriv h) U := by
    have : logDeriv h = fun z => deriv h z / h z := rfl
    rw [this]; exact fun z hz => (hh.deriv z hz).div (hh z hz) (hh0 z hz)
  -- the four edges lie in `U` and avoid `ρ`
  have hbot : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + z₁.im * I) ∈ U ∧ ((x : ℂ) + z₁.im * I) ≠ ρ :=
    fun x hx => ⟨hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [edgePt_re]; exact hx, by rw [edgePt_im]; exact left_mem_uIcc⟩),
      fun he => by have := congrArg Complex.im he; rw [edgePt_im] at this; linarith⟩
  have htop : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + z₂.im * I) ∈ U ∧ ((x : ℂ) + z₂.im * I) ≠ ρ :=
    fun x hx => ⟨hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [edgePt_re]; exact hx, by rw [edgePt_im]; exact right_mem_uIcc⟩),
      fun he => by have := congrArg Complex.im he; rw [edgePt_im] at this; linarith⟩
  have hrig : ∀ y ∈ uIcc z₁.im z₂.im, ((z₂.re : ℂ) + y * I) ∈ U ∧ ((z₂.re : ℂ) + y * I) ≠ ρ :=
    fun y hy => ⟨hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [edgePt_re]; exact right_mem_uIcc, by rw [edgePt_im]; exact hy⟩),
      fun he => by have := congrArg Complex.re he; rw [edgePt_re] at this; linarith⟩
  have hlef : ∀ y ∈ uIcc z₁.im z₂.im, ((z₁.re : ℂ) + y * I) ∈ U ∧ ((z₁.re : ℂ) + y * I) ≠ ρ :=
    fun y hy => ⟨hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [edgePt_re]; exact left_mem_uIcc, by rw [edgePt_im]; exact hy⟩),
      fun he => by have := congrArg Complex.re he; rw [edgePt_re] at this; linarith⟩
  -- the logarithmic derivative splits off the enclosed zero on `U ∖ {ρ}`
  have hid : ∀ z ∈ {z ∈ U | z ≠ ρ}, logDeriv (fun z => (z - ρ) ^ m * h z) z =
      (m : ℂ) * (z - ρ)⁻¹ + logDeriv h z := by
    rintro z ⟨hzU, hzρ⟩
    have hzρ0 : z - ρ ≠ 0 := sub_ne_zero.mpr hzρ
    rw [logDeriv_mul (f := fun w => (w - ρ) ^ m) (g := h) z (pow_ne_zero m hzρ0) (hh0 z hzU)
      (by fun_prop) (hh z hzU).differentiableAt]
    congr 1
    rw [logDeriv_fun_pow (f := fun w => w - ρ) (by fun_prop) m,
      show logDeriv (fun w => w - ρ) z = (z - ρ)⁻¹ from by
        rw [logDeriv_apply, show deriv (fun w => w - ρ) z = 1 from
          ((hasDerivAt_id z).sub_const ρ).deriv, one_div]]
  -- integrability of the two summands on each edge
  have contA : ∀ {c d : ℝ} (pt : ℝ → ℂ) (hpt : Continuous pt),
      (∀ t ∈ uIcc c d, pt t ≠ ρ) →
      IntervalIntegrable (fun t : ℝ => (m : ℂ) * (pt t - ρ)⁻¹) MeasureTheory.volume c d := by
    intro c d pt hpt hne
    refine (ContinuousOn.mul continuousOn_const ?_).intervalIntegrable
    exact (hpt.continuousOn).sub continuousOn_const |>.inv₀ (fun t ht => sub_ne_zero.mpr (hne t ht))
  have contB : ∀ {c d : ℝ} (pt : ℝ → ℂ) (hpt : Continuous pt),
      (∀ t ∈ uIcc c d, pt t ∈ U) →
      IntervalIntegrable (fun t : ℝ => logDeriv h (pt t)) MeasureTheory.volume c d := by
    intro c d pt hpt hmem
    exact (hlogh.continuousOn.comp hpt.continuousOn (fun t ht => hmem t ht)).intervalIntegrable
  rw [rectIntegral_congr hid (fun x hx => ⟨(hbot x hx).1, (hbot x hx).2⟩)
      (fun x hx => ⟨(htop x hx).1, (htop x hx).2⟩) (fun y hy => ⟨(hrig y hy).1, (hrig y hy).2⟩)
      (fun y hy => ⟨(hlef y hy).1, (hlef y hy).2⟩),
    rectIntegral_add
      (contA _ (by fun_prop) (fun x hx => (hbot x hx).2))
      (contB _ (by fun_prop) (fun x hx => (hbot x hx).1))
      (contA _ (by fun_prop) (fun x hx => (htop x hx).2))
      (contB _ (by fun_prop) (fun x hx => (htop x hx).1))
      (contA _ (by fun_prop) (fun y hy => (hrig y hy).2))
      (contB _ (by fun_prop) (fun y hy => (hrig y hy).1))
      (contA _ (by fun_prop) (fun y hy => (hlef y hy).2))
      (contB _ (by fun_prop) (fun y hy => (hlef y hy).1)),
    rectIntegral_const_mul, rectIntegral_cauchyKernel hre1 hre2 him1 him2,
    rectIntegral_eq_zero_of_analyticOnNhd hsub hlogh]
  ring

end RHTower

namespace RHTower

open Complex intervalIntegral Set

/-! ### §7 The multi-zero residue theorem -/

/-- Boundary integrals are additive over a finite family, given edgewise integrability. -/
theorem rectIntegral_finsetSum {κ : Type*} (t : Finset κ) (g : κ → ℂ → ℂ) (z₁ z₂ : ℂ)
    (hb : ∀ i ∈ t, IntervalIntegrable (fun x : ℝ => g i ((x : ℂ) + z₁.im * I)) MeasureTheory.volume z₁.re z₂.re)
    (ht : ∀ i ∈ t, IntervalIntegrable (fun x : ℝ => g i ((x : ℂ) + z₂.im * I)) MeasureTheory.volume z₁.re z₂.re)
    (hr : ∀ i ∈ t, IntervalIntegrable (fun y : ℝ => g i ((z₂.re : ℂ) + y * I)) MeasureTheory.volume z₁.im z₂.im)
    (hl : ∀ i ∈ t, IntervalIntegrable (fun y : ℝ => g i ((z₁.re : ℂ) + y * I)) MeasureTheory.volume z₁.im z₂.im) :
    rectIntegral (fun z => ∑ i ∈ t, g i z) z₁ z₂ = ∑ i ∈ t, rectIntegral (g i) z₁ z₂ := by
  unfold rectIntegral
  rw [integral_finsetSum (h := hb), integral_finsetSum (h := ht),
    integral_finsetSum (h := hr), integral_finsetSum (h := hl),
    Finset.smul_sum, Finset.smul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]

/-- **The rectangle residue theorem (argument principle).**  If `h` is analytic and nonvanishing on
a neighbourhood of the closed rectangle with corners `z₁ z₂`, and every `ρ i` (`i ∈ t`) is strictly
inside, then the boundary contour integral of the logarithmic derivative of
`(∏ᵢ (·−ρ i)^{m i}) · h` is `2πi · Σᵢ m i`: the boundary winding of `f'/f` counts the enclosed zeros
with multiplicity. -/
theorem rectIntegral_logDeriv_multi_zero {κ : Type*} (t : Finset κ) (ρ : κ → ℂ) (m : κ → ℕ)
    {h : ℂ → ℂ} {z₁ z₂ : ℂ} {U : Set ℂ}
    (hin : ∀ i ∈ t, z₁.re < (ρ i).re ∧ (ρ i).re < z₂.re ∧ z₁.im < (ρ i).im ∧ (ρ i).im < z₂.im)
    (hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U)
    (hh : AnalyticOnNhd ℂ h U) (hh0 : ∀ z ∈ U, h z ≠ 0) :
    rectIntegral (logDeriv (fun z => (∏ i ∈ t, (z - ρ i) ^ m i) * h z)) z₁ z₂ =
      2 * Real.pi * I * (∑ i ∈ t, (m i : ℂ)) := by
  classical
  have hlogh : AnalyticOnNhd ℂ (logDeriv h) U := by
    have : logDeriv h = fun z => deriv h z / h z := rfl
    rw [this]; exact fun z hz => (hh.deriv z hz).div (hh z hz) (hh0 z hz)
  set S : Set ℂ := {z : ℂ | z ∈ U ∧ ∀ i ∈ t, z ≠ ρ i} with hS
  -- the four edges lie in `S`
  have hbot : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + z₁.im * I) ∈ S := by
    intro x hx
    refine ⟨hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [edgePt_re]; exact hx, by rw [edgePt_im]; exact left_mem_uIcc⟩), fun i hi he => ?_⟩
    obtain ⟨_, _, hi1, _⟩ := hin i hi
    have := congrArg Complex.im he; rw [edgePt_im] at this; linarith
  have htop : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + z₂.im * I) ∈ S := by
    intro x hx
    refine ⟨hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [edgePt_re]; exact hx, by rw [edgePt_im]; exact right_mem_uIcc⟩), fun i hi he => ?_⟩
    obtain ⟨_, _, _, hi2⟩ := hin i hi
    have := congrArg Complex.im he; rw [edgePt_im] at this; linarith
  have hrig : ∀ y ∈ uIcc z₁.im z₂.im, ((z₂.re : ℂ) + y * I) ∈ S := by
    intro y hy
    refine ⟨hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [edgePt_re]; exact right_mem_uIcc, by rw [edgePt_im]; exact hy⟩), fun i hi he => ?_⟩
    obtain ⟨_, hi2, _, _⟩ := hin i hi
    have := congrArg Complex.re he; rw [edgePt_re] at this; linarith
  have hlef : ∀ y ∈ uIcc z₁.im z₂.im, ((z₁.re : ℂ) + y * I) ∈ S := by
    intro y hy
    refine ⟨hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [edgePt_re]; exact left_mem_uIcc, by rw [edgePt_im]; exact hy⟩), fun i hi he => ?_⟩
    obtain ⟨hi1, _, _, _⟩ := hin i hi
    have := congrArg Complex.re he; rw [edgePt_re] at this; linarith
  -- the logarithmic derivative decomposes on `S`
  have hid : ∀ z ∈ S, logDeriv (fun z => (∏ i ∈ t, (z - ρ i) ^ m i) * h z) z =
      (∑ i ∈ t, (m i : ℂ) * (z - ρ i)⁻¹) + logDeriv h z := by
    rintro z ⟨hzU, hzρ⟩
    have hpne : ∀ i ∈ t, (fun w => (w - ρ i) ^ m i) z ≠ 0 :=
      fun i hi => pow_ne_zero _ (sub_ne_zero.mpr (hzρ i hi))
    rw [logDeriv_mul (f := fun w => ∏ i ∈ t, (w - ρ i) ^ m i) (g := h) z
        (Finset.prod_ne_zero_iff.mpr hpne) (hh0 z hzU) (by fun_prop) (hh z hzU).differentiableAt,
      logDeriv_prod hpne (fun i _ => by fun_prop)]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [logDeriv_fun_pow (f := fun w => w - ρ i) (by fun_prop) (m i),
      show logDeriv (fun w => w - ρ i) z = (z - ρ i)⁻¹ from by
        rw [logDeriv_apply, show deriv (fun w => w - ρ i) z = 1 from
          ((hasDerivAt_id z).sub_const (ρ i)).deriv, one_div]]
  -- integrability building blocks
  have IIk : ∀ {c d : ℝ} (pt : ℝ → ℂ), Continuous pt → (∀ tt ∈ uIcc c d, ∀ i ∈ t, pt tt ≠ ρ i) →
      ∀ i ∈ t, IntervalIntegrable (fun tt : ℝ => (m i : ℂ) * (pt tt - ρ i)⁻¹)
        MeasureTheory.volume c d := by
    intro c d pt hpt hnz i _
    refine (ContinuousOn.mul continuousOn_const ((hpt.continuousOn.sub continuousOn_const).inv₀
      (fun tt htt => sub_ne_zero.mpr (hnz tt htt i ‹_›)))).intervalIntegrable
  have IIsum : ∀ {c d : ℝ} (pt : ℝ → ℂ), Continuous pt → (∀ tt ∈ uIcc c d, ∀ i ∈ t, pt tt ≠ ρ i) →
      IntervalIntegrable (fun tt : ℝ => ∑ i ∈ t, (m i : ℂ) * (pt tt - ρ i)⁻¹)
        MeasureTheory.volume c d :=
    fun pt hpt hnz => by
      refine IntervalIntegrable.congr ?_
        (IntervalIntegrable.sum t (fun i hi => IIk pt hpt hnz i hi))
      intro tt _
      simp [Finset.sum_apply]
  have IIh : ∀ {c d : ℝ} (pt : ℝ → ℂ), Continuous pt → (∀ tt ∈ uIcc c d, pt tt ∈ U) →
      IntervalIntegrable (fun tt : ℝ => logDeriv h (pt tt)) MeasureTheory.volume c d :=
    fun pt hpt hmem => (hlogh.continuousOn.comp hpt.continuousOn hmem).intervalIntegrable
  -- assemble
  rw [rectIntegral_congr hid hbot htop hrig hlef,
    rectIntegral_add
      (IIsum _ (by fun_prop) (fun x hx => (hbot x hx).2))
      (IIh _ (by fun_prop) (fun x hx => (hbot x hx).1))
      (IIsum _ (by fun_prop) (fun x hx => (htop x hx).2))
      (IIh _ (by fun_prop) (fun x hx => (htop x hx).1))
      (IIsum _ (by fun_prop) (fun y hy => (hrig y hy).2))
      (IIh _ (by fun_prop) (fun y hy => (hrig y hy).1))
      (IIsum _ (by fun_prop) (fun y hy => (hlef y hy).2))
      (IIh _ (by fun_prop) (fun y hy => (hlef y hy).1)),
    rectIntegral_finsetSum t (fun i z => (m i : ℂ) * (z - ρ i)⁻¹) z₁ z₂
      (fun i hi => IIk _ (by fun_prop) (fun x hx => (hbot x hx).2) i hi)
      (fun i hi => IIk _ (by fun_prop) (fun x hx => (htop x hx).2) i hi)
      (fun i hi => IIk _ (by fun_prop) (fun y hy => (hrig y hy).2) i hi)
      (fun i hi => IIk _ (by fun_prop) (fun y hy => (hlef y hy).2) i hi),
    rectIntegral_eq_zero_of_analyticOnNhd hsub hlogh, add_zero]
  rw [Finset.sum_congr rfl (fun i hi => by
    rw [rectIntegral_const_mul, rectIntegral_cauchyKernel (hin i hi).1 (hin i hi).2.1
      (hin i hi).2.2.1 (hin i hi).2.2.2]), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => by ring)

end RHTower

namespace RHTower

open Complex intervalIntegral Set

/-! ### §8 The rectangle zero-count of an analytic function -/

/-- The logarithmic derivative depends only on the germ. -/
private theorem logDeriv_of_eventuallyEq {f g : ℂ → ℂ} {z : ℂ} (heq : f =ᶠ[nhds z] g) :
    logDeriv f z = logDeriv g z := by
  rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds]

/-- **The rectangle zero-count.**  If `f` factors on a neighbourhood `U` of the closed rectangle as
`(∏ᵢ (·−ρ i)^{m i}) · h` with `h` analytic and nonvanishing on `U`, and every `ρ i` (`i ∈ t`) is
strictly inside the rectangle, then `∮_{∂R} f'/f = 2πi · Σᵢ m i`: the boundary winding recovers the
exact integer total order of the enclosed zeros — the full signed count, not merely its residue. -/
theorem rectIntegral_logDeriv_boxCount {κ : Type*} (t : Finset κ) (ρ : κ → ℂ) (m : κ → ℕ)
    {f h : ℂ → ℂ} {z₁ z₂ : ℂ} {U : Set ℂ}
    (hUopen : IsOpen U)
    (hin : ∀ i ∈ t, z₁.re < (ρ i).re ∧ (ρ i).re < z₂.re ∧ z₁.im < (ρ i).im ∧ (ρ i).im < z₂.im)
    (hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U)
    (hh : AnalyticOnNhd ℂ h U) (hh0 : ∀ z ∈ U, h z ≠ 0)
    (hfact : ∀ z ∈ U, f z = (∏ i ∈ t, (z - ρ i) ^ m i) * h z) :
    rectIntegral (logDeriv f) z₁ z₂ = 2 * Real.pi * I * (∑ i ∈ t, (m i : ℂ)) := by
  have hcongr : ∀ z ∈ U, logDeriv f z =
      logDeriv (fun z => (∏ i ∈ t, (z - ρ i) ^ m i) * h z) z := by
    intro z hz
    refine logDeriv_of_eventuallyEq ?_
    filter_upwards [hUopen.mem_nhds hz] with w hw using hfact w hw
  rw [rectIntegral_congr hcongr
      (fun x hx => hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [edgePt_re]; exact hx, by rw [edgePt_im]; exact left_mem_uIcc⟩))
      (fun x hx => hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [edgePt_re]; exact hx, by rw [edgePt_im]; exact right_mem_uIcc⟩))
      (fun y hy => hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [edgePt_re]; exact right_mem_uIcc, by rw [edgePt_im]; exact hy⟩))
      (fun y hy => hsub (Complex.mem_reProdIm.mpr
        ⟨by rw [edgePt_re]; exact left_mem_uIcc, by rw [edgePt_im]; exact hy⟩))]
  exact rectIntegral_logDeriv_multi_zero t ρ m hin hsub hh hh0

end RHTower
