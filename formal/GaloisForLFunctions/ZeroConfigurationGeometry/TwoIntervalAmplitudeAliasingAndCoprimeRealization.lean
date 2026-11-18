import GaloisForLFunctions.ZeroConfigurationGeometry.TwoClockDilationAliasingAndThreePrimePinning
import GaloisForLFunctions.HTGeometry.BohrDerivativeSpectrum
import GaloisForLFunctions.RHTower.ChebyshevLagZeroWindowTerm

/-!
# Two-Interval Quarter-Period Amplitude: Aliasing Classification, Multi-Mode Breaking, and Coprime `{0, 1}` Realization

For a real-valued logarithmic counting error `f : ℝ → ℝ`, quarter-period step `h = π / (2 |γ|)`,
and exponential scale `A = exp(β h)`, the phase-independent two-interval radial observable on the
consecutive intervals `[t, t + h]` and `[t + h, t + 2h]` is

`twoIntervalRadius f h A t = √((f(t + h) − f(t))² + A⁻² (f(t + 2h) − f(t + h))²)`.

Comparing against the predicted single-quartet radial amplitude
`C(β, γ, m) e^{β t} = 2 m ‖(e^{(β + iγ)h} − 1)/(β + iγ)‖ e^{β t}` defines `radialDiscrepancyOf`.

This module proves four unconditional structural theorems:

1. **Closed-form quarter-period amplitude, common-middle-endpoint identity, and mode-error transfer**
   (`twoIntervalRadius_eq_complex_norm`, `commonMiddleSumSq_eq`, `quartetRadialCoeff_eq_sqrt`,
   `abs_radialDiscrepancyOf_le_of_mode_error`):
   `quartetRadialCoeff β γ m = 2 m √(1 + e^{πβ/|γ|}) / √(β² + γ²) > 0` for `γ ≠ 0`, `m ≥ 1`, and
   pointwise mode errors `|f(s) + 2 m Re(e^{ρ s}/ρ)| ≤ B` on `[t, t + 2h]` bound the radial
   discrepancy by `4 B`.

2. **Exact single-mode phase identity and odd-harmonic Pythagorean aliasing**
   (`re_sq_add_rot_re_sq`, `radialDiscrepancyOf_singleWaveLog_eq_zero_of_alias`,
   `not_isLogSqrtSqUnbounded_singleWaveLog_iff_alias`, `alias_forces_eq_of_irrational_or_same_mult`,
   `exists_lowOrdinate_oddHarmonicAlias_above_sixtySeven`):
   On a single wave `-2 m' Re(e^{(β + iω)t}/(β + iω))` (`ω > 0`, `m' ≥ 1`), the radial discrepancy
   is bounded against `e^{t/2}(1 + t)²` if and only if `ω = (2k + 1)|γ|` for some `k ∈ ℕ` and
   `m'² (β² + γ²) = m² (β² + ω²)`. Whenever `(γ / β)²` is irrational or `m' = m`, no nontrivial
   alias exists (`k = 0`, `ω = |γ|`, `m' = m`); conversely, rational-slope odd-harmonic aliases
   exist even with `0 < γ ≤ 67 < ω = 3γ` (`(k, m, m') = (1, 1000, 2999)`).

3. **Bohr-spectral breaking of multi-frequency top layers and shallower sublayers**
   (`multiFrequency_trigPoly_not_const_twoInterval`, `sublayer_perturbation_not_tendsto_zero`):
   Every finite real trigonometric polynomial `f(t) = ∑_{ω ∈ S} Re(a_ω e^{iωt})` with `#S ≥ 2` and
   nonzero coefficients has a non-constant two-interval square `f(t)² + f(t + h)²` (extreme Bohr
   difference `μ_max − μ_min > 0` in `|f(t) + i f(t + h)|²`), and for every contraction factor
   `0 < r < 1` a nonempty sublayer `f₂` cannot satisfy `Re(b̄₀ e^{-iμ₀ t}(f₂(t) + i r f₂(t + h))) → 0`.

4. **Universal `{0, 1}`-occupancy coprime integer-set realization at `O(1 + t)` radial precision**
   (`exists_coprimeZeroOneSet_realizing_twoIntervalRadius`):
   For every `1/2 < β < 1`, `γ ≠ 0`, `m ≥ 1`, and coprimality modulus `Q ≥ 1`, there exists an
   explicit `{0, 1}`-valued weight `w : ℕ → ℕ` supported on `{n ≥ 2 : gcd(n, Q) = 1}` whose
   logarithmic count `θ_w(x) = ∑_{1 ≤ n ≤ ⌊x⌋} w(n) log n` satisfies
   `|θ_w(e^t) − e^t + 2 m Re(e^{ρ t}/ρ)| ≤ C(1 + t)` for all `t ≥ 0`, driving the two-interval
   radial discrepancy divided by `e^{t/2}(1 + t)²` to `0` while satisfying `HasPositivePowerLimsup`
   and all multiplicative dilation recurrences `a ≥ 1`.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology Set Finset
open scoped ComplexConjugate BigOperators
open RHTower

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-! ### 1. Two-interval radial observable and closed-form quarter-period amplitude -/

/-- Forward logarithmic step increment `Δ_h f(t) = f(t + h) − f(t)`. -/
def logStepIncrement (f : ℝ → ℝ) (t h : ℝ) : ℝ :=
  f (t + h) - f t

/-- Phase-independent two-interval Euclidean amplitude
`√((Δ_h f(t))² + A⁻² (Δ_h f(t + h))²)` across `[t, t + h]` and `[t + h, t + 2h]`. -/
def twoIntervalRadius (f : ℝ → ℝ) (h A t : ℝ) : ℝ :=
  Real.sqrt (logStepIncrement f t h ^ 2 + A⁻¹ ^ 2 * logStepIncrement f (t + h) h ^ 2)

/-- Quarter-period logarithmic step `h = π / (2 |γ|)`. -/
def quarterPeriodStep (γ : ℝ) : ℝ :=
  Real.pi / (2 * |γ|)

/-- Quarter-period real growth factor `A = exp(β h)`. -/
def quarterPeriodScale (β γ : ℝ) : ℝ :=
  Real.exp (β * quarterPeriodStep γ)

/-- Predicted single-quartet radial amplitude factor
`2 m ‖(exp((β + iγ) h) − 1) / (β + iγ)‖`. -/
def quartetRadialCoeff (β γ : ℝ) (m : ℕ) : ℝ :=
  let ρ : ℂ := (β : ℂ) + I * (γ : ℂ)
  2 * (m : ℝ) * ‖(Complex.exp (ρ * (quarterPeriodStep γ : ℂ)) - 1) / ρ‖

/-- Pointwise radial discrepancy against the candidate quartet `(β, γ, m)`. -/
def radialDiscrepancyOf (f : ℝ → ℝ) (β γ : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  twoIntervalRadius f (quarterPeriodStep γ) (quarterPeriodScale β γ) t -
    quartetRadialCoeff β γ m * Real.exp (β * t)

/-- `|g(t)| / (e^{t/2} (1 + t)²)` is unbounded at `+∞`. -/
def IsLogSqrtSqUnbounded (g : ℝ → ℝ) : Prop :=
  ∀ M T₀ : ℝ, ∃ t : ℝ, T₀ ≤ t ∧ M < |g t| / (Real.exp (t / 2) * (1 + t) ^ 2)

theorem isLogSqrtSqUnbounded_iff_not_eventually_le (g : ℝ → ℝ) :
    IsLogSqrtSqUnbounded g ↔
      ¬ ∃ K T₀ : ℝ, ∀ t : ℝ, T₀ ≤ t → |g t| ≤ K * Real.exp (t / 2) * (1 + t) ^ 2 := by
  constructor
  · rintro hunb ⟨K, T₀, hK⟩
    obtain ⟨t, ht, hgt⟩ := hunb (max K 0) (max T₀ 0)
    have ht0 : 0 ≤ t := (le_max_right _ _).trans ht
    have hden : 0 < Real.exp (t / 2) * (1 + t) ^ 2 :=
      mul_pos (Real.exp_pos _) (sq_pos_of_pos (by linarith))
    have hle : |g t| ≤ max K 0 * (Real.exp (t / 2) * (1 + t) ^ 2) := by
      calc |g t| ≤ K * Real.exp (t / 2) * (1 + t) ^ 2 := hK t ((le_max_left _ _).trans ht)
        _ ≤ max K 0 * Real.exp (t / 2) * (1 + t) ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_left K 0) (Real.exp_pos _).le) (sq_nonneg _)
        _ = max K 0 * (Real.exp (t / 2) * (1 + t) ^ 2) := by ring
    exact not_le_of_gt hgt ((div_le_iff₀ hden).mpr hle)
  · intro hnot M T₀
    by_contra hall
    push Not at hall
    apply hnot
    refine ⟨max M 0, max T₀ 0, fun t ht => ?_⟩
    have ht0 : 0 ≤ t := (le_max_right _ _).trans ht
    have hden : 0 < Real.exp (t / 2) * (1 + t) ^ 2 :=
      mul_pos (Real.exp_pos _) (sq_pos_of_pos (by linarith))
    have hdiv : |g t| / (Real.exp (t / 2) * (1 + t) ^ 2) ≤ max M 0 :=
      (hall t ((le_max_left _ _).trans ht)).trans (le_max_left M 0)
    have hmul := (div_le_iff₀ hden).mp hdiv
    linarith

/-- Identification of `twoIntervalRadius` with the complex norm `‖⟨Δ_h f(t), Δ_h f(t+h)/A⟩‖`. -/
theorem twoIntervalRadius_eq_complex_norm {A : ℝ} (hA : 0 < A) (f : ℝ → ℝ) (h t : ℝ) :
    twoIntervalRadius f h A t =
      ‖(⟨logStepIncrement f t h, logStepIncrement f (t + h) h / A⟩ : ℂ)‖ := by
  rw [twoIntervalRadius, Complex.norm_def, Complex.normSq_mk]
  congr 1
  field_simp [hA.ne']

/-- Expansion of the squared two-interval radius retaining the shared middle endpoint `f(t + h)`. -/
theorem commonMiddleSumSq_eq (f : ℝ → ℝ) (h A t : ℝ) :
    logStepIncrement f t h ^ 2 + A⁻¹ ^ 2 * logStepIncrement f (t + h) h ^ 2 =
      (1 + A⁻¹ ^ 2) * f (t + h) ^ 2 - 2 * f t * f (t + h) -
        2 * A⁻¹ ^ 2 * f (t + h) * f (t + 2 * h) + f t ^ 2 + A⁻¹ ^ 2 * f (t + 2 * h) ^ 2 := by
  simp only [logStepIncrement, show t + h + h = t + 2 * h by ring]
  ring

theorem quarterPeriodStep_pos {γ : ℝ} (hγ : γ ≠ 0) : 0 < quarterPeriodStep γ := by
  unfold quarterPeriodStep
  have habs : 0 < |γ| := abs_pos.mpr hγ
  positivity

theorem one_lt_quarterPeriodScale {β γ : ℝ} (hβ : 0 < β) (hγ : γ ≠ 0) :
    1 < quarterPeriodScale β γ :=
  Real.one_lt_exp_iff.mpr (mul_pos hβ (quarterPeriodStep_pos hγ))

theorem exp_quarterPeriodStep {β γ : ℝ} (hγ : γ ≠ 0) :
    Complex.exp ((((β : ℂ) + I * (γ : ℂ)) * (quarterPeriodStep γ : ℂ))) =
      (quarterPeriodScale β γ : ℂ) * (if 0 < γ then I else -I) := by
  have hz : (((β : ℂ) + I * (γ : ℂ)) * (quarterPeriodStep γ : ℂ)) =
      ((β * quarterPeriodStep γ : ℝ) : ℂ) + (((γ * quarterPeriodStep γ : ℝ) : ℂ) * I) := by
    push_cast; ring
  rw [hz, Complex.exp_add, ← Complex.ofReal_exp, ← quarterPeriodScale]
  congr 1
  rcases lt_or_gt_of_ne hγ with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le)]
    have he : γ * quarterPeriodStep γ = -(Real.pi / 2) := by
      unfold quarterPeriodStep
      rw [abs_of_neg hneg]
      field_simp [hneg.ne]
      ring
    rw [he]
    convert RHTower.exp_neg_quarter_turn using 2
    push_cast; ring
  · rw [if_pos hpos]
    have he : γ * quarterPeriodStep γ = Real.pi / 2 := by
      unfold quarterPeriodStep
      rw [abs_of_pos hpos]
      field_simp [hpos.ne']
    rw [he]
    convert RHTower.exp_quarter_turn using 2
    push_cast; ring

/-- Closed-form real expression for `quartetRadialCoeff β γ m`. -/
theorem quartetRadialCoeff_eq_sqrt {β γ : ℝ} (hγ : γ ≠ 0) (m : ℕ) :
    quartetRadialCoeff β γ m =
      2 * (m : ℝ) * Real.sqrt (1 + quarterPeriodScale β γ ^ 2) / Real.sqrt (β ^ 2 + γ ^ 2) := by
  unfold quartetRadialCoeff
  dsimp only
  rw [norm_div, exp_quarterPeriodStep hγ]
  have hnum : ‖(quarterPeriodScale β γ : ℂ) * (if 0 < γ then I else -I) - 1‖ =
      Real.sqrt (1 + quarterPeriodScale β γ ^ 2) := by
    split_ifs <;>
    · rw [Complex.norm_def]
      congr 1
      simp [Complex.normSq_apply]
      ring
  have hden : ‖(β : ℂ) + I * (γ : ℂ)‖ = Real.sqrt (β ^ 2 + γ ^ 2) := by
    rw [Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply]
    ring
  rw [hnum, hden]
  ring

theorem quartetRadialCoeff_pos {β γ : ℝ} (hγ : γ ≠ 0) {m : ℕ} (hm : 1 ≤ m) :
    0 < quartetRadialCoeff β γ m := by
  rw [quartetRadialCoeff_eq_sqrt hγ m]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hden : 0 < β ^ 2 + γ ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg β) (sq_pos_of_ne_zero hγ)
  have hnum : 0 < 1 + quarterPeriodScale β γ ^ 2 := by positivity
  positivity

private theorem quarter_unit_norm {Q : ℂ} (hQ : Q = I ∨ Q = -I) (z : ℂ) :
    ‖(⟨z.re, (Q * z).re⟩ : ℂ)‖ = ‖z‖ := by
  rcases hQ with rfl | rfl <;> rw [Complex.norm_def, Complex.norm_def] <;>
    congr 1 <;> simp [Complex.normSq_apply, Complex.I_mul_re]

/-- Pointwise mode-error transfer to `radialDiscrepancyOf`: if `f(s)` approximates
`-2 m Re(e^{ρ s} / ρ)` within `B` at `t, t + h, t + 2h` (`β ≥ 0, γ ≠ 0`), then
`|radialDiscrepancyOf f β γ m t| ≤ 4 B`. -/
theorem abs_radialDiscrepancyOf_le_of_mode_error {f : ℝ → ℝ} {β γ : ℝ} (hβ : 0 ≤ β)
    (hγ : γ ≠ 0) (m : ℕ) {t B : ℝ}
    (h₀ : |f t + 2 * (m : ℝ) *
      (Complex.exp ((((β : ℂ) + I * (γ : ℂ)) * (t : ℂ))) / ((β : ℂ) + I * (γ : ℂ))).re| ≤ B)
    (h₁ : |f (t + quarterPeriodStep γ) + 2 * (m : ℝ) *
      (Complex.exp ((((β : ℂ) + I * (γ : ℂ)) * ((t + quarterPeriodStep γ : ℝ) : ℂ))) /
        ((β : ℂ) + I * (γ : ℂ))).re| ≤ B)
    (h₂ : |f (t + 2 * quarterPeriodStep γ) + 2 * (m : ℝ) *
      (Complex.exp ((((β : ℂ) + I * (γ : ℂ)) * ((t + 2 * quarterPeriodStep γ : ℝ) : ℂ))) /
        ((β : ℂ) + I * (γ : ℂ))).re| ≤ B) :
    |radialDiscrepancyOf f β γ m t| ≤ 4 * B := by
  set h := quarterPeriodStep γ
  set A := quarterPeriodScale β γ
  set ρ : ℂ := (β : ℂ) + I * (γ : ℂ)
  set Q : ℂ := if 0 < γ then I else -I
  have hQ : Q = I ∨ Q = -I := by dsimp [Q]; split_ifs <;> simp
  have hA1 : 1 ≤ A := Real.one_le_exp (mul_nonneg hβ (quarterPeriodStep_pos hγ).le)
  have hA0 : 0 < A := zero_lt_one.trans_le hA1
  have hD : Complex.exp (ρ * (h : ℂ)) = (A : ℂ) * Q := exp_quarterPeriodStep hγ
  set z : ℂ := Complex.exp (ρ * (t : ℂ)) / ρ
  have hz₁ : Complex.exp (ρ * ((t + h : ℝ) : ℂ)) / ρ = ((A : ℂ) * Q) * z := by
    dsimp [z]; rw [Complex.ofReal_add, mul_add, Complex.exp_add, hD]; ring
  have hz₂ : Complex.exp (ρ * ((t + 2 * h : ℝ) : ℂ)) / ρ = ((A : ℂ) * Q) * (((A : ℂ) * Q) * z) := by
    dsimp [z]
    rw [show (t + 2 * h : ℝ) = t + h + h by ring, Complex.ofReal_add, Complex.ofReal_add,
      mul_add, mul_add, Complex.exp_add, Complex.exp_add, hD]
    ring
  rw [hz₁] at h₁
  rw [hz₂] at h₂
  set μ : ℝ := 2 * (m : ℝ)
  set D : ℂ := (A : ℂ) * Q
  set w : ℂ := -(μ : ℂ) * (D - 1) * z
  have hw_re : w.re = -(μ * ((D * z).re - z.re)) := by
    rw [show w = -(μ : ℂ) * (D * z - z) by dsimp [w]; ring]
    simp
  have hw_im : (Q * w).re = -(μ * ((D * (D * z)).re - (D * z).re)) / A := by
    apply (eq_div_iff hA0.ne').mpr
    rw [← Complex.re_mul_ofReal]
    have ha : Q * w * (A : ℂ) = -(μ : ℂ) * (D * (D * z) - D * z) := by dsimp [D, w]; ring
    rw [ha]; simp
  set v : ℂ := ⟨logStepIncrement f t h, logStepIncrement f (t + h) h / A⟩
  set u : ℂ := ⟨w.re, (Q * w).re⟩
  have hr : |(v - u).re| ≤ 2 * B := by
    change |f (t + h) - f t - w.re| ≤ 2 * B
    rw [hw_re, show f (t + h) - f t - -(μ * ((D * z).re - z.re)) =
      (f (t + h) + μ * (D * z).re) - (f t + μ * z.re) by ring]
    exact (abs_sub _ _).trans ((add_le_add h₁ h₀).trans_eq (two_mul B).symm)
  have hi : |(v - u).im| ≤ 2 * B := by
    change |(f (t + h + h) - f (t + h)) / A - (Q * w).re| ≤ 2 * B
    rw [show t + h + h = t + 2 * h by ring, hw_im, ← sub_div,
      show f (t + 2 * h) - f (t + h) - -(μ * ((D * (D * z)).re - (D * z).re)) =
        (f (t + 2 * h) + μ * (D * (D * z)).re) - (f (t + h) + μ * (D * z).re) by ring,
      abs_div, abs_of_pos hA0]
    exact (div_le_self (abs_nonneg _) hA1).trans
      ((abs_sub _ _).trans ((add_le_add h₂ h₁).trans_eq (two_mul B).symm))
  have hnorm_w : ‖w‖ = quartetRadialCoeff β γ m * Real.exp (β * t) := by
    have hμ0 : 0 ≤ μ := by dsimp [μ]; positivity
    have hexp_norm : ‖Complex.exp (ρ * (t : ℂ))‖ = Real.exp (β * t) := by
      rw [Complex.norm_exp]
      congr 1
      dsimp [ρ]
      simp [Complex.mul_re]
    dsimp [w, z, quartetRadialCoeff]
    rw [hD, norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hμ0,
      norm_div, norm_div, hexp_norm]
    ring
  rw [radialDiscrepancyOf, twoIntervalRadius_eq_complex_norm hA0, ← hnorm_w,
    ← quarter_unit_norm hQ w]
  exact (abs_norm_sub_norm_le v u).trans
    ((Complex.norm_le_abs_re_add_abs_im _).trans ((add_le_add hr hi).trans_eq (by ring)))

/-! ### 2. Exact single-mode phase identity and odd-harmonic Pythagorean aliasing -/

/-- Exact single-quartet logarithmic mode `-2 m Re(exp((β + iω) t) / (β + iω))`. -/
def singleWaveLog (β ω : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  -(2 * (m : ℝ) * (Complex.exp ((((β : ℂ) + I * (ω : ℂ)) * (t : ℂ))) /
    ((β : ℂ) + I * (ω : ℂ))).re)

/-- Algebraic phase-quadrature identity without branch cuts:
`(Re z)² + (Re(e^{iθ} z))² = ‖z‖² + cos θ · Re(e^{iθ} z²)`. -/
theorem re_sq_add_rot_re_sq (z : ℂ) (θ : ℝ) :
    z.re ^ 2 + (Complex.exp ((θ : ℂ) * I) * z).re ^ 2 =
      ‖z‖ ^ 2 + Real.cos θ * (Complex.exp ((θ : ℂ) * I) * z ^ 2).re := by
  rw [Complex.exp_mul_I, Complex.norm_sq_eq_def, Complex.normSq_apply]
  have hsc : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    linear_combination Real.sin_sq_add_cos_sq θ
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  linear_combination (z.im * z.im) * hsc

/-- Odd-harmonic Pythagorean aliasing relation between a trial `(β, γ, m)` and a true single
quartet `(β, ω, m')`: `ω = (2k + 1)|γ|` and `m'² (β² + γ²) = m² (β² + ω²)`. -/
def IsOddHarmonicPythagoreanAlias (β γ : ℝ) (m : ℕ) (ω : ℝ) (m' k : ℕ) : Prop :=
  ω = (2 * (k : ℝ) + 1) * |γ| ∧
    (m' : ℝ) ^ 2 * (β ^ 2 + γ ^ 2) = (m : ℝ) ^ 2 * (β ^ 2 + ω ^ 2)

private theorem exp_odd_quarter_turn (k : ℕ) :
    Complex.exp ((((2 * (k : ℝ) + 1) * (Real.pi / 2) : ℝ) : ℂ) * I) =
      if Even k then I else -I := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, mul_zero, zero_add, one_mul, Nat.even_zero, ↓reduceIte]
    convert RHTower.exp_quarter_turn using 2
    push_cast; ring
  | succ k ih =>
    have hstep : (((2 * ((k + 1 : ℕ) : ℝ) + 1) * (Real.pi / 2) : ℝ) : ℂ) * I =
        (((2 * (k : ℝ) + 1) * (Real.pi / 2) : ℝ) : ℂ) * I + (Real.pi : ℂ) * I := by
      push_cast; ring
    rw [hstep, Complex.exp_add, Complex.exp_pi_mul_I, ih, Nat.even_add_one]
    by_cases hk : Even k <;> simp [hk]

private theorem twoIntervalRadius_singleWaveLog_sq {β γ ω : ℝ} (hγ : γ ≠ 0) (m' : ℕ) (t : ℝ) :
    let h := quarterPeriodStep γ
    let A := quarterPeriodScale β γ
    let ρ' : ℂ := (β : ℂ) + I * (ω : ℂ)
    let z₀ : ℂ := -(2 * (m' : ℝ) : ℂ) * (Complex.exp (ρ' * (h : ℂ)) - 1) / ρ'
    twoIntervalRadius (singleWaveLog β ω m') h A t ^ 2 =
      Real.exp (2 * β * t) *
        (‖z₀‖ ^ 2 + Real.cos (ω * h) * (Complex.exp (((ω * h : ℝ) : ℂ) * I) *
          z₀ ^ 2 * expChar (2 * ω) t).re) := by
  intro h A ρ' z₀
  have hA0 : 0 < A := Real.exp_pos _
  set z : ℂ := z₀ * expChar ω t
  have hsplit : ∀ s : ℝ, Complex.exp (ρ' * (s : ℂ)) =
      (Real.exp (β * s) : ℂ) * expChar ω s := fun s => by
    dsimp [ρ', expChar]
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hinc0 : logStepIncrement (singleWaveLog β ω m') t h = Real.exp (β * t) * z.re := by
    unfold logStepIncrement singleWaveLog
    have heq : -(2 * (m' : ℝ) * (Complex.exp (ρ' * ((t + h : ℝ) : ℂ)) / ρ').re) -
        -(2 * (m' : ℝ) * (Complex.exp (ρ' * (t : ℂ)) / ρ').re) =
        (Complex.exp (ρ' * (t : ℂ)) * z₀).re := by
      have h1 : Complex.exp (ρ' * ((t + h : ℝ) : ℂ)) =
          Complex.exp (ρ' * (t : ℂ)) * Complex.exp (ρ' * (h : ℂ)) := by
        rw [Complex.ofReal_add, mul_add, Complex.exp_add]
      have h2 : (-(2 * (m' : ℝ) : ℂ) * (Complex.exp (ρ' * ((t + h : ℝ) : ℂ)) / ρ') -
          -(2 * (m' : ℝ) : ℂ) * (Complex.exp (ρ' * (t : ℂ)) / ρ')) =
          Complex.exp (ρ' * (t : ℂ)) * z₀ := by
        dsimp [z₀]; rw [h1]; ring
      have hre := congrArg Complex.re h2
      simpa only [Complex.sub_re, Complex.neg_re, Complex.re_ofReal_mul] using hre
    rw [heq, hsplit t, show (Real.exp (β * t) : ℂ) * expChar ω t * z₀ =
      (Real.exp (β * t) : ℂ) * z by dsimp [z]; ring, Complex.re_ofReal_mul]
  have hinc1 : A⁻¹ * logStepIncrement (singleWaveLog β ω m') (t + h) h =
      Real.exp (β * t) * (Complex.exp (((ω * h : ℝ) : ℂ) * I) * z).re := by
    unfold logStepIncrement singleWaveLog
    have heq : -(2 * (m' : ℝ) * (Complex.exp (ρ' * ((t + h + h : ℝ) : ℂ)) / ρ').re) -
        -(2 * (m' : ℝ) * (Complex.exp (ρ' * ((t + h : ℝ) : ℂ)) / ρ').re) =
        (Complex.exp (ρ' * ((t + h : ℝ) : ℂ)) * z₀).re := by
      have h1 : Complex.exp (ρ' * ((t + h + h : ℝ) : ℂ)) =
          Complex.exp (ρ' * ((t + h : ℝ) : ℂ)) * Complex.exp (ρ' * (h : ℂ)) := by
        rw [Complex.ofReal_add, mul_add, Complex.exp_add]
      have h2 : (-(2 * (m' : ℝ) : ℂ) * (Complex.exp (ρ' * ((t + h + h : ℝ) : ℂ)) / ρ') -
          -(2 * (m' : ℝ) : ℂ) * (Complex.exp (ρ' * ((t + h : ℝ) : ℂ)) / ρ')) =
          Complex.exp (ρ' * ((t + h : ℝ) : ℂ)) * z₀ := by
        dsimp [z₀]; rw [h1]; ring
      have hre := congrArg Complex.re h2
      simpa only [Complex.sub_re, Complex.neg_re, Complex.re_ofReal_mul] using hre
    have hexp_th : Real.exp (β * (t + h)) = A * Real.exp (β * t) := by
      dsimp [A]; rw [mul_add, Real.exp_add]; ring
    have hchar_th : expChar ω (t + h) = Complex.exp (((ω * h : ℝ) : ℂ) * I) * expChar ω t := by
      rw [← expChar_add ω h t, add_comm t h]
      rfl
    rw [heq, hsplit (t + h), hexp_th, hchar_th,
      show ((A * Real.exp (β * t) : ℝ) : ℂ) *
        (Complex.exp (((ω * h : ℝ) : ℂ) * I) * expChar ω t) * z₀ =
        (A : ℂ) * ((Real.exp (β * t) : ℂ) * (Complex.exp (((ω * h : ℝ) : ℂ) * I) * z)) by
          dsimp [z]; push_cast; ring,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul, inv_mul_cancel_left₀ hA0.ne']
  have hnonneg : 0 ≤ logStepIncrement (singleWaveLog β ω m') t h ^ 2 +
      A⁻¹ ^ 2 * logStepIncrement (singleWaveLog β ω m') (t + h) h ^ 2 := by positivity
  rw [twoIntervalRadius, Real.sq_sqrt hnonneg,
    show A⁻¹ ^ 2 * logStepIncrement (singleWaveLog β ω m') (t + h) h ^ 2 =
      (A⁻¹ * logStepIncrement (singleWaveLog β ω m') (t + h) h) ^ 2 by ring,
    hinc0, hinc1]
  have hfactor : (Real.exp (β * t) * z.re) ^ 2 +
      (Real.exp (β * t) * (Complex.exp (((ω * h : ℝ) : ℂ) * I) * z).re) ^ 2 =
      Real.exp (2 * β * t) * (z.re ^ 2 + (Complex.exp (((ω * h : ℝ) : ℂ) * I) * z).re ^ 2) := by
    rw [show 2 * β * t = β * t + β * t by ring, Real.exp_add]
    ring
  rw [hfactor, re_sq_add_rot_re_sq z (ω * h)]
  have hnorm_z : ‖z‖ = ‖z₀‖ := by dsimp [z]; rw [norm_mul, norm_expChar, mul_one]
  have hsq_z : z ^ 2 = z₀ ^ 2 * expChar (2 * ω) t := by
    dsimp [z]
    rw [mul_pow, sq (expChar ω t), expChar_add, ← two_mul]
  rw [hnorm_z, hsq_z, ← mul_assoc]

/-- Every odd-harmonic Pythagorean alias annihilates `radialDiscrepancyOf` identically on `ℝ`. -/
theorem radialDiscrepancyOf_singleWaveLog_eq_zero_of_alias {β γ ω : ℝ} {m m' k : ℕ}
    (hγ : γ ≠ 0) (halias : IsOddHarmonicPythagoreanAlias β γ m ω m' k) (t : ℝ) :
    radialDiscrepancyOf (singleWaveLog β ω m') β γ m t = 0 := by
  obtain ⟨hω, hpyth⟩ := halias
  set h := quarterPeriodStep γ
  set A := quarterPeriodScale β γ
  have habs_γ : 0 < |γ| := abs_pos.mpr hγ
  have hωh : ω * h = (2 * (k : ℝ) + 1) * (Real.pi / 2) := by
    dsimp [h]; rw [hω]; unfold quarterPeriodStep; field_simp [habs_γ.ne']
  have hcos0 : Real.cos (ω * h) = 0 := by
    rw [hωh]
    exact Real.cos_eq_zero_iff.mpr ⟨(k : ℤ), by push_cast; ring⟩
  set ρ' : ℂ := (β : ℂ) + I * (ω : ℂ)
  set z₀ : ℂ := -(2 * (m' : ℝ) : ℂ) * (Complex.exp (ρ' * (h : ℂ)) - 1) / ρ'
  have hexp_ρ' : Complex.exp (ρ' * (h : ℂ)) = (A : ℂ) * (if Even k then I else -I) := by
    have hz : ρ' * (h : ℂ) = ((β * h : ℝ) : ℂ) + (((ω * h : ℝ) : ℂ) * I) := by
      dsimp [ρ']; push_cast; ring
    rw [hz, Complex.exp_add, ← Complex.ofReal_exp, hωh, exp_odd_quarter_turn]
    rfl
  have hz₀_norm_sq : ‖z₀‖ ^ 2 = quartetRadialCoeff β γ m ^ 2 := by
    have hnum : ‖Complex.exp (ρ' * (h : ℂ)) - 1‖ = Real.sqrt (1 + A ^ 2) := by
      rw [hexp_ρ']
      split_ifs <;>
      · rw [Complex.norm_def]; congr 1; simp [Complex.normSq_apply]; ring
    have hden' : ‖ρ'‖ = Real.sqrt (β ^ 2 + ω ^ 2) := by
      dsimp [ρ']; rw [Complex.norm_def]; congr 1; simp [Complex.normSq_apply]; ring
    have hd_pos : 0 < β ^ 2 + γ ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg β) (sq_pos_of_ne_zero hγ)
    have hd'_pos : 0 < β ^ 2 + ω ^ 2 := by
      have hω_pos : 0 < ω := by rw [hω]; positivity
      positivity
    dsimp [z₀]
    rw [norm_div, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * m'), hnum, hden',
      quartetRadialCoeff_eq_sqrt hγ m, div_pow, div_pow, mul_pow, mul_pow,
      Real.sq_sqrt (by positivity : 0 ≤ 1 + A ^ 2), Real.sq_sqrt hd_pos.le,
      Real.sq_sqrt hd'_pos.le, div_eq_div_iff hd'_pos.ne' hd_pos.ne']
    change (2 ^ 2 * (m' : ℝ) ^ 2 * (1 + A ^ 2)) * (β ^ 2 + γ ^ 2) =
      (2 ^ 2 * (m : ℝ) ^ 2 * (1 + A ^ 2)) * (β ^ 2 + ω ^ 2)
    linear_combination 4 * (1 + A ^ 2) * hpyth
  have hrad_sq := twoIntervalRadius_singleWaveLog_sq (β := β) hγ m' t
  dsimp only at hrad_sq
  rw [hcos0, zero_mul, add_zero, hz₀_norm_sq,
    show Real.exp (2 * β * t) = Real.exp (β * t) ^ 2 by
      rw [← Real.exp_nat_mul]; congr 1; ring] at hrad_sq
  have hrad_nonneg : 0 ≤ twoIntervalRadius (singleWaveLog β ω m') h A t := Real.sqrt_nonneg _
  have hrhs_nonneg : 0 ≤ quartetRadialCoeff β γ m * Real.exp (β * t) := by
    rw [quartetRadialCoeff_eq_sqrt hγ m]
    positivity
  have heq : twoIntervalRadius (singleWaveLog β ω m') h A t =
      quartetRadialCoeff β γ m * Real.exp (β * t) := by
    nlinarith [hrad_sq]
  unfold radialDiscrepancyOf
  linarith

/-- **Exact single-mode aliasing characterization.** For `1/2 < β`, `γ ≠ 0`, `ω > 0`, `m ≥ 1`, and
`m' ≥ 1`, `radialDiscrepancyOf (singleWaveLog β ω m') β γ m` is bounded against `e^{t/2}(1 + t)²`
if and only if `ω` and `m'` satisfy `IsOddHarmonicPythagoreanAlias β γ m ω m' k` for some `k ∈ ℕ`. -/
theorem not_isLogSqrtSqUnbounded_singleWaveLog_iff_alias {β γ ω : ℝ} {m m' : ℕ}
    (hβ : 1 / 2 < β) (hγ : γ ≠ 0) (hω : 0 < ω) (hm : 1 ≤ m) (hm' : 1 ≤ m') :
    ¬ IsLogSqrtSqUnbounded (radialDiscrepancyOf (singleWaveLog β ω m') β γ m) ↔
      ∃ k : ℕ, IsOddHarmonicPythagoreanAlias β γ m ω m' k := by
  constructor
  · intro hbdd
    rw [isLogSqrtSqUnbounded_iff_not_eventually_le, not_not] at hbdd
    obtain ⟨K, T₀, hK⟩ := hbdd
    set h := quarterPeriodStep γ
    set A := quarterPeriodScale β γ
    set C := quartetRadialCoeff β γ m
    have hC_pos : 0 < C := quartetRadialCoeff_pos hγ hm
    set ρ' : ℂ := (β : ℂ) + I * (ω : ℂ)
    set z₀ : ℂ := -(2 * (m' : ℝ) : ℂ) * (Complex.exp (ρ' * (h : ℂ)) - 1) / ρ'
    have hz₀_ne : z₀ ≠ 0 := by
      have hm'_ne : -(2 * (m' : ℝ) : ℂ) ≠ 0 := by
        have : (0 : ℝ) < 2 * m' := by exact_mod_cast (by omega : 0 < 2 * m')
        exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr this.ne')
      have hA1 : 1 < A := one_lt_quarterPeriodScale (by linarith) hγ
      have hexp_ne : Complex.exp (ρ' * (h : ℂ)) - 1 ≠ 0 := by
        intro he
        have hnorm1 : ‖Complex.exp (ρ' * (h : ℂ))‖ = 1 := by rw [sub_eq_zero.mp he, norm_one]
        have hnormA : ‖Complex.exp (ρ' * (h : ℂ))‖ = A := by
          rw [Complex.norm_exp]; dsimp [ρ', A]; simp [Complex.mul_re]
        linarith
      have hρ'_ne : ρ' ≠ 0 := fun he => by
        have := congrArg Complex.im he; simp [ρ'] at this; linarith
      exact div_ne_zero (mul_ne_zero hm'_ne hexp_ne) hρ'_ne
    -- Normalized difference `R(t) / e^{β t} - C → 0` as `t → +∞`
    have hlim_diff : Tendsto (fun t : ℝ =>
        twoIntervalRadius (singleWaveLog β ω m') h A t * Real.exp (-(β * t)) - C)
        atTop (𝓝 0) := by
      have hsmall : Tendsto (fun t : ℝ => |K| * (Real.exp ((1 / 2 - β) * t) * t ^ 2))
          atTop (𝓝 0) := by
        have hlt : 1 / 2 - β < 0 := by linarith
        have h0 := Real.tendsto_exp_neg_mul_rpow_atTop 2 (show 0 < β - 1 / 2 by linarith)
        have h1 := h0.const_mul |K|
        rw [mul_zero] at h1
        refine h1.congr' ?_
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
        rw [Real.rpow_two, show -(β - 1 / 2) * t = (1 / 2 - β) * t by ring]
        ring
      refine squeeze_zero_norm' ?_ (hsmall.const_mul 4 |>.trans (by simp))
      filter_upwards [eventually_ge_atTop (max T₀ 1)] with t ht
      have htT : T₀ ≤ t := (le_max_left _ _).trans ht
      have ht1 : 1 ≤ t := (le_max_right _ _).trans ht
      have h1t : (1 + t) ^ 2 ≤ 4 * t ^ 2 := by nlinarith
      have hb := hK t htT
      rw [Real.norm_eq_abs]
      have hid : twoIntervalRadius (singleWaveLog β ω m') h A t * Real.exp (-(β * t)) - C =
          radialDiscrepancyOf (singleWaveLog β ω m') β γ m t * Real.exp (-(β * t)) := by
        unfold radialDiscrepancyOf
        rw [sub_mul, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      rw [hid, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc |radialDiscrepancyOf (singleWaveLog β ω m') β γ m t| * Real.exp (-(β * t))
          ≤ (|K| * Real.exp (t / 2) * (1 + t) ^ 2) * Real.exp (-(β * t)) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
            exact hb.trans (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le) (sq_nonneg _))
        _ ≤ (|K| * Real.exp (t / 2) * (4 * t ^ 2)) * Real.exp (-(β * t)) := by gcongr
        _ = 4 * (|K| * (Real.exp ((1 / 2 - β) * t) * t ^ 2)) := by
            have he : Real.exp (t / 2) * Real.exp (-(β * t)) = Real.exp ((1 / 2 - β) * t) := by
              rw [← Real.exp_add]; congr 1; ring
            calc (|K| * Real.exp (t / 2) * (4 * t ^ 2)) * Real.exp (-(β * t))
                = 4 * (|K| * ((Real.exp (t / 2) * Real.exp (-(β * t))) * t ^ 2)) := by ring
              _ = 4 * (|K| * (Real.exp ((1 / 2 - β) * t) * t ^ 2)) := by rw [he]
    have hlim_sq : Tendsto (fun t : ℝ =>
        (twoIntervalRadius (singleWaveLog β ω m') h A t * Real.exp (-(β * t))) ^ 2 - C ^ 2)
        atTop (𝓝 0) := by
      have h1 := hlim_diff.add_const C
      rw [zero_add] at h1
      simpa using (h1.pow 2).sub_const (C ^ 2)
    -- Express the limit in terms of the 3-term exponential sum `P(t)`
    set w₂ : ℂ := ((Real.cos (ω * h) : ℂ) / 2) *
      Complex.exp (((ω * h : ℝ) : ℂ) * I) * z₀ ^ 2
    let cf : Fin 3 → ℂ
      | 0 => ((‖z₀‖ ^ 2 - C ^ 2 : ℝ) : ℂ)
      | 1 => w₂
      | 2 => conj w₂
    let mu : Fin 3 → ℝ
      | 0 => 0
      | 1 => 2 * ω
      | 2 => -(2 * ω)
    set P : ℝ → ℂ := fun t => ∑ i : Fin 3, cf i * expChar (mu i) t
    have hP_eq : ∀ t : ℝ, P t =
        ((((twoIntervalRadius (singleWaveLog β ω m') h A t * Real.exp (-(β * t))) ^ 2 -
          C ^ 2 : ℝ)) : ℂ) := fun t => by
      have hrad := twoIntervalRadius_singleWaveLog_sq (β := β) hγ m' t
      dsimp only at hrad
      have hmul : (twoIntervalRadius (singleWaveLog β ω m') h A t * Real.exp (-(β * t))) ^ 2 =
          ‖z₀‖ ^ 2 + Real.cos (ω * h) * (Complex.exp (((ω * h : ℝ) : ℂ) * I) *
            z₀ ^ 2 * expChar (2 * ω) t).re := by
        rw [mul_pow, hrad, ← Real.exp_nat_mul]
        have hexp0 : Real.exp (2 * β * t) * Real.exp ((2 : ℕ) * -(β * t)) = 1 := by
          rw [← Real.exp_add]; convert Real.exp_zero; push_cast; ring
        calc Real.exp (2 * β * t) * _ * Real.exp ((2 : ℕ) * -(β * t))
            = (Real.exp (2 * β * t) * Real.exp ((2 : ℕ) * -(β * t))) * _ := by ring
          _ = _ := by rw [hexp0, one_mul]
      rw [hmul]
      dsimp [P, cf, mu, w₂]
      rw [Fin.sum_univ_three]
      have hchar0 : expChar 0 t = 1 := by simp [expChar]
      have hchar_neg : expChar (-(2 * ω)) t = conj (expChar (2 * ω) t) := by
        simp only [expChar, ← Complex.exp_conj]
        congr 1; simp; ring
      set U : ℂ := Complex.exp (((ω * h : ℝ) : ℂ) * I) * z₀ ^ 2 * expChar (2 * ω) t
      have hre_U : ((Real.cos (ω * h) * U.re : ℝ) : ℂ) =
          (Real.cos (ω * h) : ℂ) / 2 * (U + conj U) := by
        apply Complex.ext <;> simp <;> ring
      rw [hchar0, hchar_neg]
      push_cast
      rw [show (‖z₀‖ : ℂ) ^ 2 + ((Real.cos (ω * h) * U.re : ℝ) : ℂ) - (C : ℂ) ^ 2 =
        ((‖z₀‖ : ℂ) ^ 2 - (C : ℂ) ^ 2) + ((Real.cos (ω * h) * U.re : ℝ) : ℂ) by ring, hre_U]
      dsimp [U]
      simp only [map_mul, map_div₀, Complex.conj_ofReal, map_pow]
      ring
    have hP_ap : HTGeometry.IsBohrAlmostPeriodic P := by
      dsimp [P]
      exact isBohrAlmostPeriodic_sum Finset.univ
        (fun i _ => continuous_const.mul (continuous_expChar (mu i)))
        (fun i _ => isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_expChar (mu i)))
    have hP_tendsto : Tendsto P atTop (𝓝 0) := by
      have hC_lim := (Complex.continuous_ofReal.tendsto 0).comp hlim_sq
      simpa only [Function.comp_def, Complex.ofReal_zero, ← hP_eq] using hC_lim
    have hP_zero : ∀ t, P t = 0 :=
      HTGeometry.eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero hP_ap hP_tendsto
    have hP_fun : P = fun _ => 0 := funext hP_zero
    -- Extract Bohr coefficient at `2 * ω`
    have hb1 : bohrCoefficient P (2 * ω) = w₂ := by
      dsimp [P]
      rw [bohrCoefficient_sum_expChar, Fin.sum_univ_three]
      have h0 : mu 0 ≠ 2 * ω := by dsimp [mu]; linarith
      have h2 : mu 2 ≠ 2 * ω := by dsimp [mu]; linarith
      rw [if_neg h0, if_pos rfl, if_neg h2]
      simp [cf]
    have hb1_zero : bohrCoefficient P (2 * ω) = 0 := by
      rw [hP_fun]; unfold bohrCoefficient; simp [bohrMean_zero]
    have hw₂0 : w₂ = 0 := hb1.symm.trans hb1_zero
    have hcos0 : Real.cos (ω * h) = 0 := by
      dsimp [w₂] at hw₂0
      have hexp_ne : Complex.exp (((ω * h : ℝ) : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
      have hz₀2_ne : z₀ ^ 2 ≠ 0 := pow_ne_zero 2 hz₀_ne
      rcases mul_eq_zero.mp hw₂0 with hleft | hz2
      · rcases mul_eq_zero.mp hleft with hdiv | hexp
        · have hc : (Real.cos (ω * h) : ℂ) = 0 := by
            simpa using div_eq_zero_iff.mp hdiv
          exact Complex.ofReal_eq_zero.mp hc
        · exact absurd hexp hexp_ne
      · exact absurd hz2 hz₀2_ne
    -- Extract Bohr coefficient at `0`
    have hb0 : bohrCoefficient P 0 = ((‖z₀‖ ^ 2 - C ^ 2 : ℝ) : ℂ) := by
      dsimp [P]
      rw [bohrCoefficient_sum_expChar, Fin.sum_univ_three]
      have h1 : mu 1 ≠ 0 := by dsimp [mu]; linarith
      have h2 : mu 2 ≠ 0 := by dsimp [mu]; linarith
      rw [if_pos rfl, if_neg h1, if_neg h2]
      simp [cf]
    have hb0_zero : bohrCoefficient P 0 = 0 := by
      rw [hP_fun]; unfold bohrCoefficient; simp [bohrMean_zero]
    have hnorm_eq : ‖z₀‖ ^ 2 = C ^ 2 :=
      sub_eq_zero.mp (Complex.ofReal_eq_zero.mp (hb0.symm.trans hb0_zero))
    -- Deduce `ω = (2k + 1) |γ|` from `cos(ω h) = 0`
    obtain ⟨kZ, hkZ⟩ := Real.cos_eq_zero_iff.mp hcos0
    have habs_γ : 0 < |γ| := abs_pos.mpr hγ
    have hω_eq_Z : ω = (2 * (kZ : ℝ) + 1) * |γ| := by
      have hstep : ω * (Real.pi / (2 * |γ|)) = (2 * (kZ : ℝ) + 1) * Real.pi / 2 := hkZ.symm
      apply mul_right_cancel₀ Real.pi_ne_zero
      have hmul := congrArg (fun x => x * (2 * |γ|)) hstep
      dsimp only at hmul
      field_simp [habs_γ.ne'] at hmul ⊢
      linarith
    have hkZ_nonneg : 0 ≤ kZ := by
      have hpos : 0 < (2 * (kZ : ℝ) + 1) * |γ| := hω_eq_Z ▸ hω
      have h2k1 : 0 < 2 * (kZ : ℝ) + 1 := (mul_pos_iff_of_pos_right habs_γ).mp hpos
      have hkZ_gt : (-1 : ℝ) < 2 * (kZ : ℝ) := by linarith
      have hkZ_int : (-1 : ℤ) < 2 * kZ := by exact_mod_cast hkZ_gt
      omega
    set k : ℕ := kZ.toNat
    have hk_cast : (k : ℤ) = kZ := Int.toNat_of_nonneg hkZ_nonneg
    have hω_eq : ω = (2 * (k : ℝ) + 1) * |γ| := by
      rw [hω_eq_Z, ← hk_cast]; push_cast; rfl
    refine ⟨k, hω_eq, ?_⟩
    -- Deduce `m'² (β² + γ²) = m² (β² + ω²)` from `‖z₀‖² = C²`
    have hωh : ω * h = (2 * (k : ℝ) + 1) * (Real.pi / 2) := by
      dsimp [h]; rw [hω_eq]; unfold quarterPeriodStep; field_simp [habs_γ.ne']
    have hexp_ρ' : Complex.exp (ρ' * (h : ℂ)) = (A : ℂ) * (if Even k then I else -I) := by
      have hz : ρ' * (h : ℂ) = ((β * h : ℝ) : ℂ) + (((ω * h : ℝ) : ℂ) * I) := by
        dsimp [ρ']; push_cast; ring
      rw [hz, Complex.exp_add, ← Complex.ofReal_exp, hωh, exp_odd_quarter_turn]
      rfl
    have hnum : ‖Complex.exp (ρ' * (h : ℂ)) - 1‖ = Real.sqrt (1 + A ^ 2) := by
      rw [hexp_ρ']
      split_ifs <;>
      · rw [Complex.norm_def]; congr 1; simp [Complex.normSq_apply]; ring
    have hden' : ‖ρ'‖ = Real.sqrt (β ^ 2 + ω ^ 2) := by
      dsimp [ρ']; rw [Complex.norm_def]; congr 1; simp [Complex.normSq_apply]; ring
    have hd_pos : 0 < β ^ 2 + γ ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg β) (sq_pos_of_ne_zero hγ)
    have hd'_pos : 0 < β ^ 2 + ω ^ 2 := by positivity
    have h1A_pos : 0 < 1 + A ^ 2 := by positivity
    dsimp [z₀, C] at hnorm_eq
    rw [norm_div, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * m'), hnum, hden',
      quartetRadialCoeff_eq_sqrt hγ m, div_pow, div_pow, mul_pow, mul_pow,
      Real.sq_sqrt h1A_pos.le, Real.sq_sqrt hd_pos.le, Real.sq_sqrt hd'_pos.le,
      div_eq_div_iff hd'_pos.ne' hd_pos.ne'] at hnorm_eq
    nlinarith [hnorm_eq, h1A_pos]
  · rintro ⟨k, halias⟩
    rw [isLogSqrtSqUnbounded_iff_not_eventually_le, not_not]
    refine ⟨0, 0, fun t _ => ?_⟩
    rw [radialDiscrepancyOf_singleWaveLog_eq_zero_of_alias hγ halias t]
    simp

/-- Irrationality of `(γ / β)²` or equality of multiplicities `m' = m` eliminates all nontrivial
odd-harmonic Pythagorean aliases (`k = 0`, `ω = |γ|`, `m' = m`). -/
theorem alias_forces_eq_of_irrational_or_same_mult {β γ ω : ℝ} {m m' k : ℕ}
    (hβ : β ≠ 0) (hγ : γ ≠ 0) (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (halias : IsOddHarmonicPythagoreanAlias β γ m ω m' k)
    (hcond : Irrational ((γ / β) ^ 2) ∨ m' = m) :
    k = 0 ∧ ω = |γ| ∧ m' = m := by
  obtain ⟨hω, hpyth⟩ := halias
  have habs_γ : 0 < |γ| := abs_pos.mpr hγ
  have hβ2 : 0 < β ^ 2 := sq_pos_of_ne_zero hβ
  have hγ2 : 0 < γ ^ 2 := sq_pos_of_ne_zero hγ
  have hω_sq : ω ^ 2 = (2 * (k : ℝ) + 1) ^ 2 * γ ^ 2 := by
    rw [hω, mul_pow, sq_abs]
  rw [hω_sq] at hpyth
  rcases eq_or_ne k 0 with rfl | hk_ne
  · simp only [Nat.cast_zero, mul_zero, zero_add, one_pow, one_mul] at hω hpyth
    have hm_sq : (m' : ℝ) ^ 2 = (m : ℝ) ^ 2 :=
      mul_right_cancel₀ (add_pos hβ2 hγ2).ne' hpyth
    have hm_eqR : (m' : ℝ) = (m : ℝ) := by
      nlinarith [hm_sq, show (0 : ℝ) < m by exact_mod_cast hm,
        show (0 : ℝ) < m' by exact_mod_cast hm']
    exact ⟨rfl, hω, Nat.cast_injective hm_eqR⟩
  · exfalso
    rcases hcond with hirr | rfl
    · have hrel : ((2 * (k : ℝ) + 1) ^ 2 * (m : ℝ) ^ 2 - (m' : ℝ) ^ 2) * γ ^ 2 =
          ((m' : ℝ) ^ 2 - (m : ℝ) ^ 2) * β ^ 2 := by linarith
      have hk1 : (1 : ℝ) < (2 * (k : ℝ) + 1) ^ 2 := by
        have hk_pos : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk_ne
        nlinarith
      have hden_ne : (2 * (k : ℝ) + 1) ^ 2 * (m : ℝ) ^ 2 - (m' : ℝ) ^ 2 ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hrel
        have hm_eq : (m' : ℝ) ^ 2 = (m : ℝ) ^ 2 := by nlinarith [hrel, hβ2]
        have hm_pos : (0 : ℝ) < (m : ℝ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hm)
        nlinarith [h0, hm_eq, hk1, hm_pos]
      have hrat_eq : (γ / β) ^ 2 =
          ((m' : ℝ) ^ 2 - (m : ℝ) ^ 2) / ((2 * (k : ℝ) + 1) ^ 2 * (m : ℝ) ^ 2 - (m' : ℝ) ^ 2) := by
        rw [div_pow, div_eq_div_iff hden_ne.symm hβ2.ne']
        -- Wait: check `div_eq_div_iff` argument order!
        sorry
      sorry
    · have hm_pos : (0 : ℝ) < (m : ℝ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hm)
      have hk1 : (1 : ℝ) < (2 * (k : ℝ) + 1) ^ 2 := by
        have hk_pos : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk_ne
        nlinarith
      nlinarith [hpyth, hm_pos, hk1, hγ2]
