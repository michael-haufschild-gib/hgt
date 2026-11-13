import GaloisForLFunctions.RHTower.DeBruijnTopZeroVelocity
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The Gaussian at the saddle of the kernel

At its saddle `a` (`τ a = π e^{2a}`), the leading phase of the heat family is
`τ(a+v)² − πe^{2(a+v)} = f(a) + Pψ(v) + τv²`, with `P = πe^{2a}` and

`ψ(v) = 1 + 2v − e^{2v} = −2v² − (4/3)v³ − …`.

This module evaluates the integral over the real line of `v`, where `ψ` is real: the modulus of
the integrand is a Gaussian of rate `≈ Re P`, although `P` itself may be almost imaginary.

* `saddlePhase_le_neg_sq`: `ψ(v) ≤ −v²` for `v ≥ −1/2`; `abs_saddlePhase_add_le`:
  `|ψ(v) + 2v²| ≤ 8|v|³e^{2|v|}`.
* `norm_cexp_sub_cexp_le`: `|e^{w₁} − e^{w₂}| ≤ e^{max Re}|w₁ − w₂|`.
* `norm_integral_saddleIntegrand_sub_le` (**Laplace**): for `Re P ≥ 18`, `8 Re τ ≤ Re P`,
  `|κ| ≤ 6`,
  `|∫_{−1/2}^∞ e^{κv + Pψ(v) + τv²} dv − (π/(2P − τ))^{1/2}| ≤ 64e⁴(1 + |P|/Re P)/Re P`.
  The error is of the order `|P|/(Re P)²` against the main term of the order `|P|^{−1/2}`.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower.DeBruijn
open scoped Real

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## The phase at the saddle -/

/-- The phase `ψ(v) = 1 + 2v − e^{2v}` of the kernel at its saddle. -/
def saddlePhase (v : ℝ) : ℝ := 1 + 2 * v - Real.exp (2 * v)

theorem continuous_saddlePhase : Continuous saddlePhase := by
  unfold saddlePhase
  fun_prop

/-- `ψ(v) ≤ −v²` for `v ≥ −1/2`. -/
theorem saddlePhase_le_neg_sq {v : ℝ} (hv : -(1 / 2) ≤ v) : saddlePhase v ≤ -v ^ 2 := by
  unfold saddlePhase
  rcases le_total 0 v with h | h
  · have h1 := Real.quadratic_le_exp_of_nonneg (x := 2 * v) (by linarith)
    nlinarith [sq_nonneg v]
  · have hx : |2 * v| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    have hb := Real.exp_bound hx (n := 3) (by norm_num)
    have hsum : ∑ m ∈ Finset.range 3, (2 * v) ^ m / (m.factorial : ℝ) =
        1 + 2 * v + (2 * v) ^ 2 / 2 := by
      simp [Finset.sum_range_succ, Nat.factorial]
    have hc : ((Nat.succ 3 : ℕ) : ℝ) / (((Nat.factorial 3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) = 2 / 9 := by
      norm_num [Nat.factorial]
    rw [hsum, hc, abs_of_nonpos (by linarith : 2 * v ≤ 0)] at hb
    have h1 := (abs_le.mp hb).1
    nlinarith [sq_nonneg v, mul_nonneg (sq_nonneg v) (by linarith : (0 : ℝ) ≤ 1 + 16 / 9 * v)]

/-- `|ψ(v) + 2v²| ≤ 8|v|³e^{2|v|}`: the cubic remainder of the phase. -/
theorem abs_saddlePhase_add_le (v : ℝ) :
    |saddlePhase v + 2 * v ^ 2| ≤ 8 * |v| ^ 3 * Real.exp (2 * |v|) := by
  have h := norm_cexp_sub_taylor_two_le ((2 * v : ℝ) : ℂ)
  have e : cexp ((2 * v : ℝ) : ℂ) - 1 - ((2 * v : ℝ) : ℂ) - ((2 * v : ℝ) : ℂ) ^ 2 / 2 =
      ((-(saddlePhase v + 2 * v ^ 2) : ℝ) : ℂ) := by
    unfold saddlePhase
    push_cast
    ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_two] at h
  calc |saddlePhase v + 2 * v ^ 2| ≤ (2 * |v|) ^ 3 * Real.exp (2 * |v|) := h
    _ = 8 * |v| ^ 3 * Real.exp (2 * |v|) := by ring

/-! ## Elementary inequalities -/

/-- `|e^{w₁} − e^{w₂}| ≤ e^{max(Re w₁, Re w₂)} |w₁ − w₂|`. -/
theorem norm_cexp_sub_cexp_le (w₁ w₂ : ℂ) :
    ‖cexp w₁ - cexp w₂‖ ≤ Real.exp (max w₁.re w₂.re) * ‖w₁ - w₂‖ := by
  have hs : Convex ℝ {w : ℂ | w.re ≤ max w₁.re w₂.re} := convex_halfSpace_re_le _
  have m₁ : w₁ ∈ {w : ℂ | w.re ≤ max w₁.re w₂.re} := by
    rw [Set.mem_setOf_eq]; exact le_max_left _ _
  have m₂ : w₂ ∈ {w : ℂ | w.re ≤ max w₁.re w₂.re} := by
    rw [Set.mem_setOf_eq]; exact le_max_right _ _
  refine hs.norm_image_sub_le_of_norm_deriv_le (f := cexp)
    (fun w _ => Complex.differentiableAt_exp) (fun w hw => ?_) m₂ m₁
  rw [Complex.deriv_exp, Complex.norm_exp]
  exact Real.exp_le_exp.mpr hw

theorem le_exp_sq_half (t : ℝ) : t ≤ Real.exp (t ^ 2 / 2) := by
  have h := Real.add_one_le_exp (t ^ 2 / 2)
  nlinarith [sq_nonneg (t - 1)]

theorem pow_three_le_two_mul_exp_sq_half (t : ℝ) :
    t ^ 3 ≤ 2 * Real.exp (t ^ 2 / 2) := by
  have h := Real.quadratic_le_exp_of_nonneg (x := t ^ 2 / 2) (by positivity)
  nlinarith [mul_nonneg (sq_nonneg t) (sq_nonneg (t / 2 - 1))]

/-- `|v| e^{−(p/2)v²} ≤ p^{−1/2}`. -/
theorem abs_mul_exp_neg_le {p : ℝ} (hp : 0 < p) (v : ℝ) :
    |v| * Real.exp (-(p / 2 * v ^ 2)) ≤ 1 / Real.sqrt p := by
  have hr : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have h := le_exp_sq_half (Real.sqrt p * |v|)
  have e : (Real.sqrt p * |v|) ^ 2 / 2 = p / 2 * v ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hp.le, sq_abs]
    ring
  rw [e] at h
  have hE := Real.exp_pos (p / 2 * v ^ 2)
  rw [Real.exp_neg, le_div_iff₀ hr]
  calc |v| * (Real.exp (p / 2 * v ^ 2))⁻¹ * Real.sqrt p
      = Real.sqrt p * |v| * (Real.exp (p / 2 * v ^ 2))⁻¹ := by ring
    _ ≤ Real.exp (p / 2 * v ^ 2) * (Real.exp (p / 2 * v ^ 2))⁻¹ :=
        mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hE.le)
    _ = 1 := mul_inv_cancel₀ hE.ne'

/-- `|v|³ e^{−(p/2)v²} ≤ 2 p^{−3/2}`. -/
theorem abs_pow_three_mul_exp_neg_le {p : ℝ} (hp : 0 < p) (v : ℝ) :
    |v| ^ 3 * Real.exp (-(p / 2 * v ^ 2)) ≤ 2 * (1 / Real.sqrt p) ^ 3 := by
  have hr : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have h := pow_three_le_two_mul_exp_sq_half (Real.sqrt p * |v|)
  have e : (Real.sqrt p * |v|) ^ 2 / 2 = p / 2 * v ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hp.le, sq_abs]
    ring
  rw [e] at h
  have hE := Real.exp_pos (p / 2 * v ^ 2)
  have hr3 : 0 < Real.sqrt p ^ 3 := pow_pos hr 3
  rw [Real.exp_neg, one_div, inv_pow, ← div_eq_mul_inv 2, le_div_iff₀ hr3]
  calc |v| ^ 3 * (Real.exp (p / 2 * v ^ 2))⁻¹ * Real.sqrt p ^ 3
      = (Real.sqrt p * |v|) ^ 3 * (Real.exp (p / 2 * v ^ 2))⁻¹ := by ring
    _ ≤ 2 * Real.exp (p / 2 * v ^ 2) * (Real.exp (p / 2 * v ^ 2))⁻¹ :=
        mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hE.le)
    _ = 2 := by rw [mul_assoc, mul_inv_cancel₀ hE.ne', mul_one]

/-- `e^{6|v|} e^{−(7/8)pv²} ≤ e⁴ e^{−(p/2)v²} e^{−(p/4)v²}` for `p ≥ 18`. -/
theorem exp_mul_exp_neg_le {p : ℝ} (hp : 18 ≤ p) (v : ℝ) :
    Real.exp (6 * |v|) * Real.exp (-(7 / 8 * p * v ^ 2)) ≤
      Real.exp 4 * Real.exp (-(p / 2 * v ^ 2)) * Real.exp (-(p / 4) * v ^ 2) := by
  have hp0 : 0 < p := by linarith
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have e : (p * |v|) ^ 2 = p ^ 2 * v ^ 2 := by rw [mul_pow, sq_abs]
  have h1 : 6 * |v| * p ≤ p * (p / 8 * v ^ 2 + 4) := by
    nlinarith [sq_nonneg (p * |v| - 24)]
  have h2 : 6 * |v| ≤ p / 8 * v ^ 2 + 4 := by
    by_contra hcon
    push Not at hcon
    have := mul_lt_mul_of_pos_right hcon hp0
    linarith
  linarith

/-! ## The integrand at the saddle -/

/-- The integrand at the saddle: `e^{κv + Pψ(v) + τv²}`. -/
def saddleIntegrand (P τ κ : ℂ) (v : ℝ) : ℂ :=
  cexp (κ * v + P * ((saddlePhase v : ℝ) : ℂ) + τ * (v : ℂ) ^ 2)

theorem continuous_saddleIntegrand (P τ κ : ℂ) : Continuous (saddleIntegrand P τ κ) := by
  have h := continuous_saddlePhase
  unfold saddleIntegrand
  fun_prop

/-- On `v ≥ −1/2` the real part of `Pψ(v) + τv²` is at most `−(7/8) Re P · v²`. -/
theorem re_saddle_exponent_le {P τ : ℂ} (hp : 0 ≤ P.re) (hτ : 8 * τ.re ≤ P.re) {v : ℝ}
    (hv : -(1 / 2) ≤ v) :
    (P * ((saddlePhase v : ℝ) : ℂ) + τ * (v : ℂ) ^ 2).re ≤ -(7 / 8 * P.re * v ^ 2) := by
  have e : τ * (v : ℂ) ^ 2 = τ * ((v ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [Complex.add_re, Complex.re_mul_ofReal, e, Complex.re_mul_ofReal]
  have h1 := mul_le_mul_of_nonneg_left (saddlePhase_le_neg_sq hv) hp
  have h2 := mul_le_mul_of_nonneg_right hτ (sq_nonneg v)
  linarith

/-- **Pointwise comparison with the Gaussian.** On `v ≥ −1/2`,
`|e^{κv+Pψ(v)+τv²} − e^{−(2P−τ)v²}| ≤ e⁴(6p^{−1/2} + 16|P|p^{−3/2}) e^{−(p/4)v²}`, `p = Re P`. -/
theorem norm_saddleIntegrand_sub_gaussian_le {P τ κ : ℂ} (hp : 18 ≤ P.re)
    (hτ : 8 * τ.re ≤ P.re) (hκ : ‖κ‖ ≤ 6) {v : ℝ} (hv : -(1 / 2) ≤ v) :
    ‖saddleIntegrand P τ κ v - cexp (-(2 * P - τ) * (v : ℂ) ^ 2)‖ ≤
      Real.exp 4 * (6 * (1 / Real.sqrt P.re) + 16 * ‖P‖ * (1 / Real.sqrt P.re) ^ 3) *
        Real.exp (-(P.re / 4) * v ^ 2) := by
  set p := P.re with hpdef
  have hp0 : 0 < p := by linarith
  set u : ℝ := 1 / Real.sqrt p with hu
  have hu0 : 0 ≤ u := by positivity
  set w₀ : ℂ := P * ((saddlePhase v : ℝ) : ℂ) + τ * (v : ℂ) ^ 2 with hw₀
  set w₂ : ℂ := -(2 * P - τ) * (v : ℂ) ^ 2 with hw₂
  set g₇ : ℝ := Real.exp (-(7 / 8 * p * v ^ 2)) with hg₇
  have hre0 : w₀.re ≤ -(7 / 8 * p * v ^ 2) := re_saddle_exponent_le hp0.le hτ hv
  have hre2 : w₂.re ≤ -(7 / 8 * p * v ^ 2) := by
    have e : w₂ = (-(2 * P - τ)) * ((v ^ 2 : ℝ) : ℂ) := by rw [hw₂]; push_cast; ring
    rw [e, Complex.re_mul_ofReal]
    simp only [Complex.neg_re, Complex.sub_re, Complex.mul_re, Complex.re_ofNat,
      Complex.im_ofNat, zero_mul, sub_zero]
    have h2 := mul_le_mul_of_nonneg_right hτ (sq_nonneg v)
    nlinarith [mul_nonneg hp0.le (sq_nonneg v)]
  -- the factor `e^{κv}`
  have hd1 : ‖saddleIntegrand P τ κ v - cexp w₀‖ ≤ 6 * |v| * Real.exp (6 * |v|) * g₇ := by
    have e : saddleIntegrand P τ κ v - cexp w₀ = (cexp (κ * v) - 1) * cexp w₀ := by
      rw [saddleIntegrand, show κ * (v : ℂ) + P * ((saddlePhase v : ℝ) : ℂ) + τ * (v : ℂ) ^ 2 =
        κ * v + w₀ by rw [hw₀]; ring, Complex.exp_add]
      ring
    rw [e, norm_mul, Complex.norm_exp]
    have h1 := norm_cexp_sub_one_le (κ * v)
    have h2 : ‖κ * (v : ℂ)‖ ≤ 6 * |v| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hκ (abs_nonneg v)
    have h3 : ‖cexp (κ * v) - 1‖ ≤ 6 * |v| * Real.exp (6 * |v|) :=
      h1.trans (mul_le_mul h2 (Real.exp_le_exp.mpr h2) (Real.exp_pos _).le (by positivity))
    exact mul_le_mul h3 (Real.exp_le_exp.mpr hre0) (Real.exp_pos _).le (by positivity)
  -- the cubic remainder of the phase
  have hd2 : ‖cexp w₀ - cexp w₂‖ ≤ 8 * ‖P‖ * |v| ^ 3 * Real.exp (2 * |v|) * g₇ := by
    have h1 := norm_cexp_sub_cexp_le w₀ w₂
    have e : w₀ - w₂ = P * ((saddlePhase v + 2 * v ^ 2 : ℝ) : ℂ) := by
      rw [hw₀, hw₂]; push_cast; ring
    have h2 : ‖w₀ - w₂‖ ≤ ‖P‖ * (8 * |v| ^ 3 * Real.exp (2 * |v|)) := by
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (abs_saddlePhase_add_le v) (norm_nonneg _)
    have h3 : Real.exp (max w₀.re w₂.re) ≤ g₇ := Real.exp_le_exp.mpr (max_le hre0 hre2)
    calc ‖cexp w₀ - cexp w₂‖ ≤ Real.exp (max w₀.re w₂.re) * ‖w₀ - w₂‖ := h1
      _ ≤ g₇ * (‖P‖ * (8 * |v| ^ 3 * Real.exp (2 * |v|))) :=
          mul_le_mul h3 h2 (norm_nonneg _) (Real.exp_pos _).le
      _ = 8 * ‖P‖ * |v| ^ 3 * Real.exp (2 * |v|) * g₇ := by ring
  -- absorb the polynomial factors into the Gaussian
  set X : ℝ := Real.exp (-(p / 2 * v ^ 2)) with hX
  set Y : ℝ := Real.exp (-(p / 4) * v ^ 2) with hY
  have hX0 : 0 < X := Real.exp_pos _
  have hY0 : 0 < Y := Real.exp_pos _
  have k1 : Real.exp (6 * |v|) * g₇ ≤ Real.exp 4 * X * Y := exp_mul_exp_neg_le hp v
  have k1' : Real.exp (2 * |v|) * g₇ ≤ Real.exp 4 * X * Y := by
    refine le_trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le) k1
    nlinarith [abs_nonneg v]
  have k2 : |v| * X ≤ u := abs_mul_exp_neg_le hp0 v
  have k3 : |v| ^ 3 * X ≤ 2 * u ^ 3 := abs_pow_three_mul_exp_neg_le hp0 v
  have hE4 : 0 < Real.exp 4 := Real.exp_pos _
  have a1 : 6 * |v| * Real.exp (6 * |v|) * g₇ ≤ Real.exp 4 * (6 * u) * Y := by
    calc 6 * |v| * Real.exp (6 * |v|) * g₇ = 6 * |v| * (Real.exp (6 * |v|) * g₇) := by ring
      _ ≤ 6 * |v| * (Real.exp 4 * X * Y) :=
          mul_le_mul_of_nonneg_left k1 (by positivity)
      _ = Real.exp 4 * (6 * (|v| * X)) * Y := by ring
      _ ≤ Real.exp 4 * (6 * u) * Y := by gcongr
  have a2 : 8 * ‖P‖ * |v| ^ 3 * Real.exp (2 * |v|) * g₇ ≤
      Real.exp 4 * (16 * ‖P‖ * u ^ 3) * Y := by
    calc 8 * ‖P‖ * |v| ^ 3 * Real.exp (2 * |v|) * g₇
        = 8 * ‖P‖ * |v| ^ 3 * (Real.exp (2 * |v|) * g₇) := by ring
      _ ≤ 8 * ‖P‖ * |v| ^ 3 * (Real.exp 4 * X * Y) :=
          mul_le_mul_of_nonneg_left k1' (by positivity)
      _ = Real.exp 4 * (8 * ‖P‖ * (|v| ^ 3 * X)) * Y := by ring
      _ ≤ Real.exp 4 * (8 * ‖P‖ * (2 * u ^ 3)) * Y := by gcongr
      _ = Real.exp 4 * (16 * ‖P‖ * u ^ 3) * Y := by ring
  calc ‖saddleIntegrand P τ κ v - cexp w₂‖
      ≤ ‖saddleIntegrand P τ κ v - cexp w₀‖ + ‖cexp w₀ - cexp w₂‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ Real.exp 4 * (6 * u) * Y + Real.exp 4 * (16 * ‖P‖ * u ^ 3) * Y := by linarith
    _ = Real.exp 4 * (6 * u + 16 * ‖P‖ * u ^ 3) * Y := by ring

/-! ## The Laplace evaluation -/

/-- **The Gaussian at the saddle.** For `Re P ≥ 18`, `8 Re τ ≤ Re P` and `|κ| ≤ 6`,
`∫_{−1/2}^∞ e^{κv + Pψ(v) + τv²} dv = (π/(2P − τ))^{1/2} + O((1 + |P|/Re P)/Re P)`. -/
theorem norm_integral_saddleIntegrand_sub_le {P τ κ : ℂ} (hp : 18 ≤ P.re)
    (hτ : 8 * τ.re ≤ P.re) (hκ : ‖κ‖ ≤ 6) :
    ‖(∫ v in Ioi (-(1 / 2) : ℝ), saddleIntegrand P τ κ v) -
        ((π : ℂ) / (2 * P - τ)) ^ (1 / 2 : ℂ)‖ ≤
      64 * Real.exp 4 * (1 + ‖P‖ / P.re) / P.re := by
  set p := P.re with hpdef
  have hp0 : 0 < p := by linarith
  have hr : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  set u : ℝ := 1 / Real.sqrt p with hu
  have hu0 : 0 < u := by positivity
  have hu2 : u ^ 2 = 1 / p := by rw [hu, div_pow, one_pow, Real.sq_sqrt hp0.le]
  have hu1 : u ≤ 1 := by
    rw [hu, div_le_one hr]
    exact Real.one_le_sqrt.mpr (by linarith)
  set lam : ℂ := 2 * P - τ with hlam
  have hlamre : lam.re = 2 * p - τ.re := by
    rw [hlam]
    simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
      sub_zero]
    rw [hpdef]
  have hlam0 : 0 < lam.re := by rw [hlamre]; linarith
  set E : ℝ → ℂ := saddleIntegrand P τ κ with hE
  set G : ℝ → ℂ := fun v => cexp (-lam * (v : ℂ) ^ 2) with hG
  have hGi : Integrable G := integrable_cexp_neg_mul_sq hlam0
  set c₁ : ℝ := Real.exp 4 * (6 * u + 16 * ‖P‖ * u ^ 3) with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  set c₂ : ℝ := 32 / 5 * u ^ 2 with hc₂
  have hc₂0 : 0 ≤ c₂ := by positivity
  set g : ℝ → ℝ := fun v => Real.exp (-(p / 4) * v ^ 2) with hg
  have hgi : Integrable g := integrable_exp_neg_mul_sq (by positivity)
  have hg0 : ∀ v, 0 ≤ g v := fun v => (Real.exp_pos _).le
  have hgint : ∫ v, g v = Real.sqrt (π / (p / 4)) := integral_gaussian (p / 4)
  -- the two pointwise bounds
  have hEG : ∀ v ∈ Ioi (-(1 / 2) : ℝ), ‖E v - G v‖ ≤ c₁ * g v := fun v hv =>
    norm_saddleIntegrand_sub_gaussian_le hp hτ hκ (le_of_lt hv)
  have hGtail : ∀ v ∈ Iic (-(1 / 2) : ℝ), ‖G v‖ ≤ c₂ * g v := by
    intro v hv
    have hv2 : 1 / 4 ≤ v ^ 2 := by
      have : v ≤ -(1 / 2) := hv
      nlinarith
    have e : -lam * (v : ℂ) ^ 2 = (-lam) * ((v ^ 2 : ℝ) : ℂ) := by push_cast; ring
    have h1 : ‖G v‖ = Real.exp (-(lam.re * v ^ 2)) := by
      simp only [hG]
      rw [Complex.norm_exp, e, Complex.re_mul_ofReal, Complex.neg_re, neg_mul]
    have h2 : Real.exp (-(5 * p / 32)) ≤ c₂ := by
      have h3 : 5 * p / 32 < Real.exp (5 * p / 32) := by
        have := Real.add_one_le_exp (5 * p / 32)
        linarith
      rw [Real.exp_neg, hc₂, hu2]
      rw [inv_le_comm₀ (Real.exp_pos _) (by positivity)]
      have h4 : (32 / 5 * (1 / p))⁻¹ = 5 * p / 32 := by field_simp
      rw [h4]
      exact h3.le
    rw [h1]
    calc Real.exp (-(lam.re * v ^ 2))
        ≤ Real.exp (-(5 * p / 32) + -(p / 4) * v ^ 2) := by
          refine Real.exp_le_exp.mpr ?_
          rw [hlamre]
          nlinarith [mul_nonneg hp0.le (sq_nonneg v)]
      _ = Real.exp (-(5 * p / 32)) * g v := by rw [Real.exp_add]
      _ ≤ c₂ * g v := mul_le_mul_of_nonneg_right h2 (hg0 v)
  -- integrability of the integrand at the saddle
  have hEi : IntegrableOn E (Ioi (-(1 / 2) : ℝ)) := by
    have hdom : Integrable fun v => c₁ * g v + ‖G v‖ := (hgi.const_mul c₁).add hGi.norm
    refine Integrable.mono' hdom.integrableOn
      (continuous_saddleIntegrand P τ κ).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_)
    have h1 := hEG v hv
    calc ‖E v‖ = ‖(E v - G v) + G v‖ := by rw [sub_add_cancel]
      _ ≤ ‖E v - G v‖ + ‖G v‖ := norm_add_le _ _
      _ ≤ c₁ * g v + ‖G v‖ := by linarith
  -- the difference as two integrals
  have hsplit : (∫ v, G v) =
      (∫ v in Iic (-(1 / 2) : ℝ), G v) + ∫ v in Ioi (-(1 / 2) : ℝ), G v := by
    have h := integral_add_compl (measurableSet_Iic (a := (-(1 / 2) : ℝ))) hGi
    rw [compl_Iic] at h
    exact h.symm
  have hgauss : ((π : ℂ) / lam) ^ (1 / 2 : ℂ) = ∫ v, G v :=
    (integral_gaussian_complex hlam0).symm
  have hdiff : (∫ v in Ioi (-(1 / 2) : ℝ), E v) - ((π : ℂ) / lam) ^ (1 / 2 : ℂ) =
      (∫ v in Ioi (-(1 / 2) : ℝ), (E v - G v)) - ∫ v in Iic (-(1 / 2) : ℝ), G v := by
    rw [hgauss, hsplit, integral_sub hEi hGi.integrableOn]
    ring
  have hI1 : ‖∫ v in Ioi (-(1 / 2) : ℝ), (E v - G v)‖ ≤ c₁ * ∫ v, g v := by
    have h1 : ‖∫ v in Ioi (-(1 / 2) : ℝ), (E v - G v)‖ ≤
        ∫ v in Ioi (-(1 / 2) : ℝ), c₁ * g v :=
      norm_integral_le_of_norm_le (hgi.const_mul c₁).integrableOn
        ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hEG))
    have h2 : (∫ v in Ioi (-(1 / 2) : ℝ), c₁ * g v) ≤ c₁ * ∫ v, g v := by
      rw [← integral_const_mul]
      exact setIntegral_le_integral (hgi.const_mul c₁)
        (Eventually.of_forall fun v => mul_nonneg hc₁0 (hg0 v))
    exact h1.trans h2
  have hI2 : ‖∫ v in Iic (-(1 / 2) : ℝ), G v‖ ≤ c₂ * ∫ v, g v := by
    have h1 : ‖∫ v in Iic (-(1 / 2) : ℝ), G v‖ ≤ ∫ v in Iic (-(1 / 2) : ℝ), c₂ * g v :=
      norm_integral_le_of_norm_le (hgi.const_mul c₂).integrableOn
        ((ae_restrict_iff' measurableSet_Iic).2 (Eventually.of_forall hGtail))
    have h2 : (∫ v in Iic (-(1 / 2) : ℝ), c₂ * g v) ≤ c₂ * ∫ v, g v := by
      rw [← integral_const_mul]
      exact setIntegral_le_integral (hgi.const_mul c₂)
        (Eventually.of_forall fun v => mul_nonneg hc₂0 (hg0 v))
    exact h1.trans h2
  -- the Gaussian mass
  have hmass : ∫ v, g v ≤ 4 * u := by
    rw [hgint, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have h4 := Real.pi_le_four
    rw [mul_pow, hu2]
    rw [div_le_iff₀ (by positivity)]
    have : (4 : ℝ) ^ 2 * (1 / p) * (p / 4) = 4 := by field_simp
    linarith
  have hmass0 : 0 ≤ ∫ v, g v := integral_nonneg hg0
  have hE4 : 1 ≤ Real.exp 4 := Real.one_le_exp (by norm_num)
  rw [hdiff]
  calc ‖(∫ v in Ioi (-(1 / 2) : ℝ), (E v - G v)) - ∫ v in Iic (-(1 / 2) : ℝ), G v‖
      ≤ c₁ * (∫ v, g v) + c₂ * (∫ v, g v) := (norm_sub_le _ _).trans (add_le_add hI1 hI2)
    _ ≤ (c₁ + c₂) * (4 * u) := by
        rw [← add_mul]
        exact mul_le_mul_of_nonneg_left hmass (add_nonneg hc₁0 hc₂0)
    _ ≤ 64 * Real.exp 4 * (1 + ‖P‖ * u ^ 2) * u ^ 2 := by
        rw [hc₁, hc₂]
        have hP := norm_nonneg P
        have hu3 : u ^ 3 ≤ u ^ 2 := by nlinarith [sq_nonneg u]
        have hEu : 0 ≤ Real.exp 4 * u ^ 2 := by positivity
        have hEPu : 0 ≤ Real.exp 4 * ‖P‖ * u ^ 4 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hE4 (sq_nonneg u), sq_nonneg u]
    _ = 64 * Real.exp 4 * (1 + ‖P‖ / p) / p := by
        rw [hu2]
        ring

end

end GaloisForLFunctions.GaloisTheoryOfZeros
