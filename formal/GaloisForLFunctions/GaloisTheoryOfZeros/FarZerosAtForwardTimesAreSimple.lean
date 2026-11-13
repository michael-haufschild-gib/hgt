import GaloisForLFunctions.GaloisTheoryOfZeros.TheHalfTransformIsLocallyAnExponential
import GaloisForLFunctions.GaloisTheoryOfZeros.TheReflectedHalfTransformIsDominated

/-!
# Far zeros at forward times are simple

For `τ` in a box `{t₀ ≤ Re τ, ‖τ‖ ≤ T₀}` the far zeros of `H_τ` lie in the strip
`|Im z| < 12 + 21T₀`. Near a far point `(τ₀, z₀)` of that strip both half transforms are
exponentials, so the heat family is a sum of two exponentials: with `a = farSlope T₀ z₀`,
`b = farSlope T₀ (−z₀)` the slopes of `ξ` at the two base points and `P`, `Q` the two saddle
values, for `τ₀, τ` in the box and `‖z − z₀‖ ≤ 1`

`H_τ(z) = P e^{ia(z − z₀) + a²(τ − τ₀)} + Q e^{−ib(z − z₀) + b²(τ − τ₀)}`

up to `ε` times the sum of the two moduli (`exists_norm_complexHeat_sub_farModel_le`).

* **Phase lock.** If `(τ₀, z₀)` and `(τ, z)` are both zeros, the quotient of the two exponentials
  is within `ε` of one: `‖e^{Φ} − 1‖ ≤ ε` for the phase
  `Φ = (a + b)(i(z − z₀) + (a − b)(τ − τ₀))` (`exists_norm_exp_zeroPhase_sub_one_le`). The far
  zeros of `H_τ` near `z₀` are spaced by `2π/(a + b)`, and they drift with the time at the
  bounded velocity `i(a − b)` (`norm_zeroDrift_le`).
* **Simplicity.** A far zero is simple (`exists_deriv_complexHeat_ne_zero`): at a zero
  `P + Q` is small, the derivative of the model is `i(a + b)P − ib(P + Q)`, and Cauchy's estimate
  on the circle of radius `1/(1 + ‖a‖ + ‖b‖)` bounds the derivative of the error by a small
  multiple of `(‖a‖ + ‖b‖)‖P‖`.
-/

open Complex Set Metric
open RHTower

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## Elementary facts -/

/-- Two points of an annulus `[n − c, n + c]`, `n ≥ 2c`, have logarithms within `2`. -/
theorem abs_log_sub_log_le_two {x y c n : ℝ} (hn : 2 * c ≤ n) (hcn : 0 < n)
    (hx1 : n - c ≤ x) (hx2 : x ≤ n + c) (hy1 : n - c ≤ y) (hy2 : y ≤ n + c) :
    |Real.log x - Real.log y| ≤ 2 := by
  have hx : 0 < x := by linarith
  have hy : 0 < y := by linarith
  have key : ∀ u v : ℝ, 0 < u → 0 < v → u ≤ 3 * v → Real.log u - Real.log v ≤ 2 := by
    intro u v hu hv huv
    rw [← Real.log_div hu.ne' hv.ne']
    have h1 := Real.log_le_sub_one_of_pos (div_pos hu hv)
    have h2 : u / v ≤ 3 := by
      rw [div_le_iff₀ hv]
      exact huv
    linarith
  rw [abs_le]
  constructor
  · have := key y x hy hx (by linarith)
    linarith
  · exact key x y hx hy (by linarith)

/-- If `P + Q` is small relative to `‖P‖ + ‖Q‖`, the two moduli are comparable. -/
theorem norm_le_two_mul_of_cancellation {P Q : ℂ} {ε : ℝ} (hε' : ε ≤ 1 / 3)
    (h0 : ‖P + Q‖ ≤ ε * (‖P‖ + ‖Q‖)) : ‖Q‖ ≤ 2 * ‖P‖ := by
  have h2 : ‖Q‖ ≤ ‖P + Q‖ + ‖P‖ := by
    have := norm_sub_le (P + Q) P
    rwa [add_sub_cancel_left] at this
  have h3 : ε * ‖P‖ ≤ 1 / 3 * ‖P‖ := mul_le_mul_of_nonneg_right hε' (norm_nonneg _)
  have h4 : ε * ‖Q‖ ≤ 1 / 3 * ‖Q‖ := mul_le_mul_of_nonneg_right hε' (norm_nonneg _)
  linarith

theorem mul_dist_le_of_two_cancellations {p q d nu nv ε : ℝ} (hp : 0 ≤ p) (hd : 0 ≤ d)
    (hnv : 0 ≤ nv) (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 3) (hq : q ≤ 2 * p) (hu : nu ≤ d + nv)
    (h : p * d ≤ ε * (p * nu + q * nv) + ε * (p + q) * nv) : p * d ≤ 9 * ε * (p * nv) := by
  have h1 : p * nu ≤ p * d + p * nv := by
    have := mul_le_mul_of_nonneg_left hu hp
    linarith
  have h2 : q * nv ≤ 2 * (p * nv) := by
    have := mul_le_mul_of_nonneg_right hq hnv
    linarith
  have h3 : ε * (p * nu + q * nv) ≤ ε * (p * d + 3 * (p * nv)) :=
    mul_le_mul_of_nonneg_left (by linarith) hε
  have h4 : ε * (p + q) * nv ≤ ε * (3 * (p * nv)) := by
    have h5 : (p + q) * nv ≤ 3 * (p * nv) := by
      have := mul_le_mul_of_nonneg_right (by linarith : p + q ≤ 3 * p) hnv
      linarith
    have := mul_le_mul_of_nonneg_left h5 hε
    linarith
  have h5 : ε * (p * d) ≤ 1 / 3 * (p * d) :=
    mul_le_mul_of_nonneg_right hε' (mul_nonneg hp hd)
  linarith

/-- **Two cancellations lock the phase.** If `P + Q` and `Pu + Qv` are both small relative to
the moduli of their terms, then `u` and `v` are close: from `P(u − v) = (Pu + Qv) − (P + Q)v`. -/
theorem norm_sub_le_of_two_cancellations {P Q u v : ℂ} {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 3)
    (hP : P ≠ 0) (h0 : ‖P + Q‖ ≤ ε * (‖P‖ + ‖Q‖))
    (h1 : ‖P * u + Q * v‖ ≤ ε * (‖P * u‖ + ‖Q * v‖)) : ‖u - v‖ ≤ 9 * ε * ‖v‖ := by
  have hq := norm_le_two_mul_of_cancellation hε' h0
  have e : P * (u - v) = (P * u + Q * v) - (P + Q) * v := by ring
  have h5 : ‖P‖ * ‖u - v‖ ≤ ε * (‖P‖ * ‖u‖ + ‖Q‖ * ‖v‖) + ε * (‖P‖ + ‖Q‖) * ‖v‖ := by
    rw [← norm_mul P (u - v), e]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul (P + Q) v]
    rw [norm_mul, norm_mul] at h1
    have := mul_le_mul_of_nonneg_right h0 (norm_nonneg v)
    linarith
  have hu : ‖u‖ ≤ ‖u - v‖ + ‖v‖ := by
    have := norm_add_le (u - v) v
    rwa [sub_add_cancel] at this
  have h6 := mul_dist_le_of_two_cancellations (norm_nonneg P) (norm_nonneg (u - v))
    (norm_nonneg v) hε hε' hq hu h5
  have h7 : ‖P‖ * ‖u - v‖ ≤ ‖P‖ * (9 * ε * ‖v‖) := by linarith
  exact le_of_mul_le_mul_left h7 (norm_pos_iff.2 hP)

/-- The budget of the simplicity argument: the model derivative `(α + β)p` cannot be absorbed by
the cancellation defect and the Cauchy estimate of the error. -/
theorem false_of_simple_zero_budget {p q α β na nb D : ℝ} (hp : 0 < p) (hq0 : 0 ≤ q)
    (hq : q ≤ 2 * p) (hα : 1 ≤ α) (hβ : 1 ≤ β) (hna0 : 0 ≤ na) (hnb0 : 0 ≤ nb)
    (hna : na ≤ α + 1) (hnb : nb ≤ β + 1)
    (hlow : (α + β) * p - nb * (1 / 40 * (p + q)) ≤ D)
    (hup : D ≤ 1 / 40 * (3 * (p + q)) * (1 + na + nb)) : False := by
  have h1 : nb * (p + q) ≤ (β + 1) * (3 * p) :=
    mul_le_mul hnb (by linarith) (by linarith) (by linarith)
  have h2 : (p + q) * (1 + na + nb) ≤ 3 * p * (3 + α + β) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have h3 : p ≤ α * p := le_mul_of_one_le_left hp.le hα
  have h4 : p ≤ β * p := le_mul_of_one_le_left hp.le hβ
  linarith

/-! ## The exponential model at a far place -/

/-- The slope of the half transform at the far place `z`: the slope of `ξ` at the base point
`1/2 + iz + κ`, `κ = 18 + 21T₀`. -/
def farSlope (T₀ : ℝ) (z : ℂ) : ℂ := saddleSlope (13 + 21 * T₀ + 5) (1 / 2 + I * z)

/-- The saddle value of the half transform at `(τ, z)`. -/
def farValue (T₀ : ℝ) (τ z : ℂ) : ℂ := saddleValue (13 + 21 * T₀ + 5) τ (1 / 2 + I * z)

/-- The exponential model of the half transform around `(τ₀, z₀)`. -/
def farModel (T₀ : ℝ) (τ₀ z₀ τ z : ℂ) : ℂ :=
  farValue T₀ τ₀ z₀ * cexp (farSlope T₀ z₀ * (I * (z - z₀)) + farSlope T₀ z₀ ^ 2 * (τ - τ₀))

theorem saddleModel_eq_farModel (T₀ : ℝ) (τ₀ z₀ τ z : ℂ) :
    saddleModel (13 + 21 * T₀ + 5) τ₀ (1 / 2 + I * z₀) τ (1 / 2 + I * z) =
      farModel T₀ τ₀ z₀ τ z := by
  rw [saddleModel, farModel, farValue, farSlope,
    show (1 / 2 + I * z : ℂ) - (1 / 2 + I * z₀) = I * (z - z₀) by ring]

theorem farModel_self (T₀ : ℝ) (τ₀ z₀ : ℂ) : farModel T₀ τ₀ z₀ τ₀ z₀ = farValue T₀ τ₀ z₀ := by
  simp [farModel]

theorem norm_farModel_le (T₀ : ℝ) (τ₀ z₀ z : ℂ) :
    ‖farModel T₀ τ₀ z₀ τ₀ z‖ ≤
      ‖farValue T₀ τ₀ z₀‖ * Real.exp (‖farSlope T₀ z₀‖ * ‖z - z₀‖) := by
  rw [farModel, sub_self, mul_zero, add_zero, norm_mul, Complex.norm_exp]
  refine mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 ((Complex.re_le_norm _).trans ?_)) (norm_nonneg _)
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul]

theorem hasDerivAt_farModel (T₀ : ℝ) (τ₀ z₀ τ z : ℂ) :
    HasDerivAt (fun w => farModel T₀ τ₀ z₀ τ w)
      (farModel T₀ τ₀ z₀ τ z * (farSlope T₀ z₀ * I)) z := by
  have h1 : HasDerivAt
      (fun w : ℂ => farSlope T₀ z₀ * (I * (w - z₀)) + farSlope T₀ z₀ ^ 2 * (τ - τ₀))
      (farSlope T₀ z₀ * (I * 1)) z :=
    ((((hasDerivAt_id' z).sub_const z₀).const_mul I).const_mul (farSlope T₀ z₀)).add_const _
  have h2 := h1.cexp.const_mul (farValue T₀ τ₀ z₀)
  rw [mul_one] at h2
  have e : farModel T₀ τ₀ z₀ τ z * (farSlope T₀ z₀ * I) =
      farValue T₀ τ₀ z₀ *
        (cexp (farSlope T₀ z₀ * (I * (z - z₀)) + farSlope T₀ z₀ ^ 2 * (τ - τ₀)) *
          (farSlope T₀ z₀ * I)) := by
    rw [farModel, mul_assoc]
  rw [e]
  exact h2

theorem hasDerivAt_farModel_neg (T₀ : ℝ) (τ₀ z₀ τ z : ℂ) :
    HasDerivAt (fun w => farModel T₀ τ₀ z₀ τ (-w))
      (-(farModel T₀ τ₀ z₀ τ (-z) * (farSlope T₀ z₀ * I))) z := by
  have h := (hasDerivAt_farModel T₀ τ₀ z₀ τ (-z)).comp z (hasDerivAt_neg' z)
  rw [mul_neg_one] at h
  exact h

/-! ## The slopes at a far place -/

theorem farBase_re (T₀ : ℝ) (z : ℂ) :
    ((1 / 2 + I * z : ℂ) + ((13 + 21 * T₀ + 5 : ℝ) : ℂ)).re = 37 / 2 + 21 * T₀ - z.im := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.add_re, Complex.add_re,
    Complex.ofReal_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  ring

theorem farBase_eq (T₀ : ℝ) (z : ℂ) :
    (1 / 2 + I * z : ℂ) + ((13 + 21 * T₀ + 5 : ℝ) : ℂ) =
      I * z - (-((37 / 2 + 21 * T₀ : ℝ) : ℂ)) := by
  push_cast
  ring

theorem le_norm_farBase {T₀ : ℝ} (hT : 0 ≤ T₀) (z : ℂ) :
    ‖z‖ - (37 / 2 + 21 * T₀) ≤ ‖(1 / 2 + I * z : ℂ) + ((13 + 21 * T₀ + 5 : ℝ) : ℂ)‖ := by
  have h1 := norm_sub_norm_le (I * z) (-((37 / 2 + 21 * T₀ : ℝ) : ℂ))
  rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith)] at h1
  rw [farBase_eq]
  exact h1

theorem norm_farBase_le {T₀ : ℝ} (hT : 0 ≤ T₀) (z : ℂ) :
    ‖(1 / 2 + I * z : ℂ) + ((13 + 21 * T₀ + 5 : ℝ) : ℂ)‖ ≤ ‖z‖ + (37 / 2 + 21 * T₀) := by
  have h1 := norm_sub_le (I * z) (-((37 / 2 + 21 * T₀ : ℝ) : ℂ))
  rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith)] at h1
  rw [farBase_eq]
  exact h1

/-- The real part of the slope is large at a far place. -/
theorem le_farSlope_re {T₀ A : ℝ} {z : ℂ} (hT : 0 ≤ T₀)
    (hz : 2 * Real.pi * Real.exp (2 * A) + (37 / 2 + 21 * T₀) ≤ ‖z‖) :
    A ≤ (farSlope T₀ z).re :=
  le_saddleSlope_re (by
    have := le_norm_farBase hT z
    linarith)

/-- The slope is its real part up to one: its imaginary part is half an argument in the right
half-plane. -/
theorem norm_farSlope_le {T₀ : ℝ} {z : ℂ} (hz : z.im ≤ 13 + 21 * T₀)
    (hre : 0 ≤ (farSlope T₀ z).re) : ‖farSlope T₀ z‖ ≤ (farSlope T₀ z).re + 1 := by
  have hpos : 0 < ((1 / 2 + I * z : ℂ) + ((13 + 21 * T₀ + 5 : ℝ) : ℂ)).re := by
    rw [farBase_re]
    linarith
  have h1 := Complex.norm_le_abs_re_add_abs_im (farSlope T₀ z)
  have h2 : |(farSlope T₀ z).im| < Real.pi / 4 := abs_xiSlope_im_lt hpos
  rw [abs_of_nonneg hre] at h1
  have := Real.pi_lt_d2
  linarith

/-- The frequency of the far zeros near `z`: consecutive zeros differ by `2π/(a + b)`. -/
def zeroFrequency (T₀ : ℝ) (z : ℂ) : ℂ := farSlope T₀ z + farSlope T₀ (-z)

/-- The drift of the far zeros near `z`: they move with the time at the velocity `i(a − b)`. -/
def zeroDrift (T₀ : ℝ) (z : ℂ) : ℂ := farSlope T₀ z - farSlope T₀ (-z)

/-- The phase between the two exponentials of the model around `(τ₀, z₀)`, normalised to vanish
at `(τ₀, z₀)`. -/
def zeroPhase (T₀ : ℝ) (τ₀ z₀ τ z : ℂ) : ℂ :=
  zeroFrequency T₀ z₀ * (I * (z - z₀) + zeroDrift T₀ z₀ * (τ - τ₀))

theorem zeroPhase_self (T₀ : ℝ) (τ₀ z₀ : ℂ) : zeroPhase T₀ τ₀ z₀ τ₀ z₀ = 0 := by
  simp [zeroPhase]

theorem zeroFrequency_re (T₀ : ℝ) (z : ℂ) :
    (zeroFrequency T₀ z).re = (farSlope T₀ z).re + (farSlope T₀ (-z)).re := rfl

/-- The frequency is large at a far place. -/
theorem le_norm_zeroFrequency {T₀ A : ℝ} {z : ℂ} (hT : 0 ≤ T₀)
    (hz : 2 * Real.pi * Real.exp (2 * A) + (37 / 2 + 21 * T₀) ≤ ‖z‖) :
    2 * A ≤ ‖zeroFrequency T₀ z‖ := by
  have h1 := le_farSlope_re hT hz
  have h2 := le_farSlope_re (z := -z) hT (by rwa [norm_neg])
  have h3 := Complex.re_le_norm (zeroFrequency T₀ z)
  rw [zeroFrequency_re] at h3
  linarith

/-- **The drift is bounded.** In the strip the two base points have comparable moduli and
arguments in `(−π/2, π/2)`. -/
theorem norm_zeroDrift_le {T₀ : ℝ} {z : ℂ} (hT : 0 ≤ T₀) (him : |z.im| ≤ 13 + 21 * T₀)
    (hz : 37 + 42 * T₀ ≤ ‖z‖) : ‖zeroDrift T₀ z‖ ≤ 3 := by
  obtain ⟨h1, h2⟩ := abs_le.1 him
  have hp : 0 < ((1 / 2 + I * z : ℂ) + ((13 + 21 * T₀ + 5 : ℝ) : ℂ)).re := by
    rw [farBase_re]
    linarith
  have hm : 0 < ((1 / 2 + I * (-z) : ℂ) + ((13 + 21 * T₀ + 5 : ℝ) : ℂ)).re := by
    rw [farBase_re, Complex.neg_im]
    linarith
  have h := norm_xiSlope_sub_le_log hp hm
  have hx1 := le_norm_farBase hT z
  have hx2 := norm_farBase_le hT z
  have hy1 := le_norm_farBase hT (-z)
  have hy2 := norm_farBase_le hT (-z)
  rw [norm_neg] at hy1 hy2
  have hlog := abs_log_sub_log_le_two (c := 37 / 2 + 21 * T₀) (n := ‖z‖) (by linarith)
    (by linarith) hx1 hx2 hy1 hy2
  have hpi := Real.pi_lt_d2
  show ‖xiSlope ((1 / 2 + I * z : ℂ) + ((13 + 21 * T₀ + 5 : ℝ) : ℂ)) -
    xiSlope ((1 / 2 + I * (-z) : ℂ) + ((13 + 21 * T₀ + 5 : ℝ) : ℂ))‖ ≤ 3
  linarith

/-- The displacement of the place is the phase divided by the frequency, up to the drift. -/
theorem norm_sub_le_of_zeroPhase {T₀ : ℝ} {τ₀ z₀ : ℂ} (τ z : ℂ)
    (hΛ : 1 ≤ ‖zeroFrequency T₀ z₀‖) :
    ‖z - z₀‖ ≤ ‖zeroPhase T₀ τ₀ z₀ τ z‖ + ‖zeroDrift T₀ z₀‖ * ‖τ - τ₀‖ := by
  have h1 : ‖I * (z - z₀) + zeroDrift T₀ z₀ * (τ - τ₀)‖ ≤ ‖zeroPhase T₀ τ₀ z₀ τ z‖ := by
    rw [zeroPhase, norm_mul]
    exact le_mul_of_one_le_left (norm_nonneg _) hΛ
  have h2 := norm_sub_le (I * (z - z₀) + zeroDrift T₀ z₀ * (τ - τ₀))
    (zeroDrift T₀ z₀ * (τ - τ₀))
  rw [add_sub_cancel_right, norm_mul, norm_mul, Complex.norm_I, one_mul] at h2
  linarith

/-! ## The heat family is a sum of two exponentials -/

/-- **Near a far point of the strip the heat family is a sum of two exponentials.** For `τ₀, τ`
in the box `{t₀ ≤ Re τ, ‖τ‖ ≤ T₀}`, `|Im z₀| ≤ 12 + 21T₀`, `‖z₀‖ ≥ R` and `‖z − z₀‖ ≤ 1`, the
value `H_τ(z)` is the sum of the exponential models of the two half transforms up to `ε` times
the sum of their moduli; the two saddle values do not vanish. -/
theorem exists_norm_complexHeat_sub_farModel_le {t₀ ε : ℝ} (T₀ : ℝ) (ht₀ : 0 < t₀)
    (hε : 0 < ε) :
    ∃ R : ℝ, ∀ τ₀ τ z₀ z : ℂ, t₀ ≤ τ₀.re → ‖τ₀‖ ≤ T₀ → t₀ ≤ τ.re → ‖τ‖ ≤ T₀ →
      |z₀.im| ≤ 12 + 21 * T₀ → R ≤ ‖z₀‖ → ‖z - z₀‖ ≤ 1 →
      farValue T₀ τ₀ z₀ ≠ 0 ∧ farValue T₀ τ₀ (-z₀) ≠ 0 ∧
        ‖complexHeat τ z - (farModel T₀ τ₀ z₀ τ z + farModel T₀ τ₀ (-z₀) τ (-z))‖ ≤
          ε * (‖farModel T₀ τ₀ z₀ τ z‖ + ‖farModel T₀ τ₀ (-z₀) τ (-z)‖) := by
  by_cases hT : 0 ≤ T₀
  swap
  · exact ⟨0, fun τ₀ _ _ _ _ h2 _ _ _ _ _ => absurd ((norm_nonneg τ₀).trans h2) hT⟩
  obtain ⟨R, hR⟩ := exists_norm_halfHeat_sub_saddleModel_le (Y := 13 + 21 * T₀) (ε := ε) T₀ ht₀
    (by linarith) hε
  refine ⟨R, fun τ₀ τ z₀ z hτ₀t hτ₀T hτt hτT him hRz hnear => ?_⟩
  obtain ⟨h1, h2⟩ := abs_le.1 him
  have hd : |z.im - z₀.im| ≤ 1 := by
    have := Complex.abs_im_le_norm (z - z₀)
    rw [Complex.sub_im] at this
    exact this.trans hnear
  obtain ⟨h3, h4⟩ := abs_le.1 hd
  have hnear' : ‖-z - -z₀‖ ≤ 1 := by
    rw [show -z - -z₀ = -(z - z₀) by ring, norm_neg]
    exact hnear
  obtain ⟨hP, hp⟩ := hR τ₀ τ z₀ z hτ₀t hτ₀T hτt hτT (by linarith) (by linarith) hRz hnear
  obtain ⟨hQ, hq⟩ := hR τ₀ τ (-z₀) (-z) hτ₀t hτ₀T hτt hτT (by rw [Complex.neg_im]; linarith)
    (by rw [Complex.neg_im]; linarith) (by rwa [norm_neg]) hnear'
  rw [saddleModel_eq_farModel] at hp hq
  refine ⟨hP, hQ, ?_⟩
  rw [complexHeat_eq_halfHeat_add (ht₀.trans_le hτt) z, add_sub_add_comm, mul_add]
  exact (norm_add_le _ _).trans (add_le_add hp hq)

/-! ## The phase lock at two zeros -/

/-- **Two nearby far zeros have a phase near `2πiℤ`.** If `(τ₀, z₀)` and `(τ, z)` are zeros of
the heat family with `τ₀, τ` in the box, `‖z₀‖ ≥ R` and `‖z − z₀‖ ≤ 1`, then
`‖e^{Φ} − 1‖ ≤ ε` for the phase `Φ = (a + b)(i(z − z₀) + (a − b)(τ − τ₀))`. -/
theorem exists_norm_exp_zeroPhase_sub_one_le {t₀ ε : ℝ} (T₀ : ℝ) (ht₀ : 0 < t₀) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ τ₀ τ z₀ z : ℂ, t₀ ≤ τ₀.re → ‖τ₀‖ ≤ T₀ → t₀ ≤ τ.re → ‖τ‖ ≤ T₀ → R ≤ ‖z₀‖ →
      ‖z - z₀‖ ≤ 1 → complexHeat τ₀ z₀ = 0 → complexHeat τ z = 0 →
      ‖cexp (zeroPhase T₀ τ₀ z₀ τ z) - 1‖ ≤ ε := by
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = min (ε / 9) (1 / 3) := ⟨_, rfl⟩
  have hε₁0 : 0 < ε₁ := by
    rw [hε₁def]
    exact lt_min (by positivity) (by norm_num)
  have hε₁1 : ε₁ ≤ 1 / 3 := by
    rw [hε₁def]
    exact min_le_right _ _
  have hε₁ε : 9 * ε₁ ≤ ε := by
    have := min_le_left (ε / 9) (1 / 3)
    rw [← hε₁def] at this
    linarith
  obtain ⟨R₁, hR₁⟩ := exists_norm_complexHeat_sub_farModel_le T₀ ht₀ hε₁0
  obtain ⟨R₂, hR₂⟩ := exists_complexHeat_ne_zero_of_le_abs_im T₀ ht₀
  refine ⟨max R₁ R₂, fun τ₀ τ z₀ z hτ₀t hτ₀T hτt hτT hR hnear hH₀ hH => ?_⟩
  have him : |z₀.im| ≤ 12 + 21 * T₀ := by
    by_contra hcon
    exact hR₂ τ₀ z₀ hτ₀t hτ₀T (not_le.1 hcon).le ((le_max_right _ _).trans hR) hH₀
  have hR1 := (le_max_left _ _).trans hR
  obtain ⟨hP, -, h0⟩ := hR₁ τ₀ τ₀ z₀ z₀ hτ₀t hτ₀T hτ₀t hτ₀T him hR1
    (by rw [sub_self, norm_zero]; exact zero_le_one)
  obtain ⟨-, -, h1⟩ := hR₁ τ₀ τ z₀ z hτ₀t hτ₀T hτt hτT him hR1 hnear
  rw [hH₀, zero_sub, norm_neg, farModel_self, farModel_self] at h0
  rw [hH, zero_sub, norm_neg] at h1
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u =
      cexp (farSlope T₀ z₀ * (I * (z - z₀)) + farSlope T₀ z₀ ^ 2 * (τ - τ₀)) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℂ, v =
      cexp (farSlope T₀ (-z₀) * (I * (-z - -z₀)) + farSlope T₀ (-z₀) ^ 2 * (τ - τ₀)) :=
    ⟨_, rfl⟩
  have h1' : ‖farValue T₀ τ₀ z₀ * u + farValue T₀ τ₀ (-z₀) * v‖ ≤
      ε₁ * (‖farValue T₀ τ₀ z₀ * u‖ + ‖farValue T₀ τ₀ (-z₀) * v‖) := by
    rw [hu, hv]
    exact h1
  have h2 := norm_sub_le_of_two_cancellations hε₁0.le hε₁1 hP h0 h1'
  have hv0 : v ≠ 0 := by
    rw [hv]
    exact Complex.exp_ne_zero _
  have e : cexp (zeroPhase T₀ τ₀ z₀ τ z) - 1 = (u - v) / v := by
    rw [sub_div, div_self hv0, hu, hv, ← Complex.exp_sub]
    congr 2
    rw [zeroPhase, zeroFrequency, zeroDrift]
    ring
  rw [e, norm_div, div_le_iff₀ (norm_pos_iff.2 hv0)]
  have := mul_le_mul_of_nonneg_right hε₁ε (norm_nonneg v)
  linarith

/-! ## Far zeros are simple -/

/-- **Far zeros at forward times are simple.** For `τ` in the box `{t₀ ≤ Re τ, ‖τ‖ ≤ T₀}` every
zero `z` of `H_τ` with `‖z‖ ≥ R` is simple. -/
theorem exists_deriv_complexHeat_ne_zero {t₀ : ℝ} (T₀ : ℝ) (ht₀ : 0 < t₀) :
    ∃ R : ℝ, ∀ τ z : ℂ, t₀ ≤ τ.re → ‖τ‖ ≤ T₀ → R ≤ ‖z‖ → complexHeat τ z = 0 →
      deriv (complexHeat τ) z ≠ 0 := by
  by_cases hT : 0 ≤ T₀
  swap
  · exact ⟨0, fun τ _ _ h2 _ _ => absurd ((norm_nonneg τ).trans h2) hT⟩
  obtain ⟨R₁, hR₁⟩ := exists_norm_complexHeat_sub_farModel_le (ε := 1 / 40) T₀ ht₀
    (by norm_num)
  obtain ⟨R₂, hR₂⟩ := exists_complexHeat_ne_zero_of_le_abs_im T₀ ht₀
  refine ⟨max (max R₁ R₂) (2 * Real.pi * Real.exp (2 * 1) + (37 / 2 + 21 * T₀)),
    fun τ z hτt hτT hR hH hH' => ?_⟩
  have hRa := (le_max_left _ _).trans hR
  have hR1 := (le_max_left _ _).trans hRa
  have hR2 := (le_max_right _ _).trans hRa
  have hR3 := (le_max_right _ _).trans hR
  have him : |z.im| ≤ 12 + 21 * T₀ := by
    by_contra hcon
    exact hR₂ τ z hτt hτT (not_le.1 hcon).le hR2 hH
  obtain ⟨him1, him2⟩ := abs_le.1 him
  obtain ⟨P, hPdef⟩ : ∃ P : ℂ, P = farValue T₀ τ z := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℂ, Q = farValue T₀ τ (-z) := ⟨_, rfl⟩
  obtain ⟨a, hadef⟩ : ∃ a : ℂ, a = farSlope T₀ z := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b : ℂ, b = farSlope T₀ (-z) := ⟨_, rfl⟩
  -- the two slopes
  have hα : 1 ≤ a.re := by
    rw [hadef]
    exact le_farSlope_re hT hR3
  have hβ : 1 ≤ b.re := by
    rw [hbdef]
    exact le_farSlope_re hT (by rwa [norm_neg])
  have hna : ‖a‖ ≤ a.re + 1 := by
    have h0 : 0 ≤ a.re := by linarith
    rw [hadef] at h0 ⊢
    exact norm_farSlope_le (by linarith) h0
  have hnb : ‖b‖ ≤ b.re + 1 := by
    have h0 : 0 ≤ b.re := by linarith
    rw [hbdef] at h0 ⊢
    exact norm_farSlope_le (by rw [Complex.neg_im]; linarith) h0
  -- the cancellation at the zero
  obtain ⟨hP, -, h0⟩ := hR₁ τ τ z z hτt hτT hτt hτT him hR1
    (by rw [sub_self, norm_zero]; exact zero_le_one)
  rw [hH, zero_sub, norm_neg, farModel_self, farModel_self, ← hPdef, ← hQdef] at h0
  rw [← hPdef] at hP
  have hq := norm_le_two_mul_of_cancellation (by norm_num) h0
  -- the error of the model and its derivative at the zero
  have hF : ∀ w : ℂ, HasDerivAt
      (fun w => complexHeat τ w - (farModel T₀ τ z τ w + farModel T₀ τ (-z) τ (-w)))
      (deriv (complexHeat τ) w - (farModel T₀ τ z τ w * (farSlope T₀ z * I) +
        -(farModel T₀ τ (-z) τ (-w) * (farSlope T₀ (-z) * I)))) w := fun w =>
    ((differentiable_complexHeat τ w).hasDerivAt).sub
      ((hasDerivAt_farModel T₀ τ z τ w).add (hasDerivAt_farModel_neg T₀ τ (-z) τ w))
  have hFd : Differentiable ℂ
      (fun w => complexHeat τ w - (farModel T₀ τ z τ w + farModel T₀ τ (-z) τ (-w))) :=
    fun w => (hF w).differentiableAt
  have hderiv := (hF z).deriv
  rw [hH', zero_sub, farModel_self, farModel_self, ← hPdef, ← hQdef, ← hadef, ← hbdef]
    at hderiv
  -- the circle
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = (1 + ‖a‖ + ‖b‖)⁻¹ := ⟨_, rfl⟩
  have hna0 := norm_nonneg a
  have hnb0 := norm_nonneg b
  have hden : 1 ≤ 1 + ‖a‖ + ‖b‖ := by linarith
  have hρ0 : 0 < ρ := by
    rw [hρdef]
    exact inv_pos.2 (by linarith)
  have hρ1 : ρ ≤ 1 := by
    rw [hρdef]
    exact inv_le_one_of_one_le₀ hden
  have haρ : ‖a‖ * ρ ≤ 1 := by
    rw [hρdef, ← div_eq_mul_inv, div_le_one (by linarith)]
    linarith
  have hbρ : ‖b‖ * ρ ≤ 1 := by
    rw [hρdef, ← div_eq_mul_inv, div_le_one (by linarith)]
    linarith
  have he3 : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hsphere : ∀ w ∈ sphere z ρ,
      ‖complexHeat τ w - (farModel T₀ τ z τ w + farModel T₀ τ (-z) τ (-w))‖ ≤
        1 / 40 * (3 * (‖P‖ + ‖Q‖)) := by
    intro w hw
    rw [mem_sphere_iff_norm] at hw
    obtain ⟨-, -, h1⟩ := hR₁ τ τ z w hτt hτT hτt hτT him hR1 (by rw [hw]; exact hρ1)
    have h2 := norm_farModel_le T₀ τ z w
    have h3 := norm_farModel_le T₀ τ (-z) (-w)
    rw [← hPdef, ← hadef, hw] at h2
    rw [← hQdef, ← hbdef, show -w - -z = -(w - z) by ring, norm_neg, hw] at h3
    have h4 : Real.exp (‖a‖ * ρ) ≤ 3 := (Real.exp_le_exp.2 haρ).trans he3
    have h5 : Real.exp (‖b‖ * ρ) ≤ 3 := (Real.exp_le_exp.2 hbρ).trans he3
    have h6 := mul_le_mul_of_nonneg_left h4 (norm_nonneg P)
    have h7 := mul_le_mul_of_nonneg_left h5 (norm_nonneg Q)
    linarith
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ0 hFd.diffContOnCl
    hsphere
  rw [hderiv, hρdef, div_inv_eq_mul, norm_neg] at hcauchy
  -- the derivative of the model
  have e : P * (a * I) + -(Q * (b * I)) = I * ((a + b) * P - b * (P + Q)) := by ring
  have hlow : (a.re + b.re) * ‖P‖ - ‖b‖ * (1 / 40 * (‖P‖ + ‖Q‖)) ≤
      ‖P * (a * I) + -(Q * (b * I))‖ := by
    rw [e, norm_mul, Complex.norm_I, one_mul]
    have h1 := norm_sub_norm_le ((a + b) * P) (b * (P + Q))
    rw [norm_mul, norm_mul] at h1
    have h2 : a.re + b.re ≤ ‖a + b‖ := by
      have := Complex.re_le_norm (a + b)
      rwa [Complex.add_re] at this
    have h3 := mul_le_mul_of_nonneg_right h2 (norm_nonneg P)
    have h4 := mul_le_mul_of_nonneg_left h0 (norm_nonneg b)
    linarith
  exact false_of_simple_zero_budget (norm_pos_iff.2 hP) (norm_nonneg Q) hq hα hβ hna0 hnb0
    hna hnb hlow hcauchy

end

end GaloisForLFunctions.GaloisTheoryOfZeros
