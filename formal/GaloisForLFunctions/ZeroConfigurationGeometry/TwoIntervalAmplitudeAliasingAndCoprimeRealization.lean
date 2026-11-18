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

open Complex Filter Topology Finset
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

private theorem exp_pi_div_two_I :
    Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * I) = I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  simp

private theorem exp_neg_pi_div_two_I :
    Complex.exp (((-(Real.pi / 2) : ℝ) : ℂ) * I) = -I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

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
    rw [he, exp_neg_pi_div_two_I]
  · rw [if_pos hpos]
    have he : γ * quarterPeriodStep γ = Real.pi / 2 := by
      unfold quarterPeriodStep
      rw [abs_of_pos hpos]
      field_simp [hpos.ne']
    rw [he, exp_pi_div_two_I]

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

theorem quarterPeriodStep_neg (γ : ℝ) : quarterPeriodStep (-γ) = quarterPeriodStep γ := by
  unfold quarterPeriodStep; rw [abs_neg]

theorem quarterPeriodScale_neg (β γ : ℝ) : quarterPeriodScale β (-γ) = quarterPeriodScale β γ := by
  unfold quarterPeriodScale; rw [quarterPeriodStep_neg]

theorem quartetRadialCoeff_neg (β γ : ℝ) (m : ℕ) :
    quartetRadialCoeff β (-γ) m = quartetRadialCoeff β γ m := by
  by_cases hγ : γ = 0
  · subst hγ; simp [quartetRadialCoeff]
  · rw [quartetRadialCoeff_eq_sqrt (neg_ne_zero.mpr hγ) m, quartetRadialCoeff_eq_sqrt hγ m,
      quarterPeriodScale_neg, neg_sq]

theorem radialDiscrepancyOf_neg (f : ℝ → ℝ) (β γ : ℝ) (m : ℕ) (t : ℝ) :
    radialDiscrepancyOf f β (-γ) m t = radialDiscrepancyOf f β γ m t := by
  unfold radialDiscrepancyOf
  rw [quarterPeriodStep_neg, quarterPeriodScale_neg, quartetRadialCoeff_neg]

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
    congr 1 <;> simp [Complex.normSq_apply]

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
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.sq_norm, Complex.normSq_apply]
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
    rw [if_pos Even.zero]
    simp only [Nat.cast_zero, mul_zero, zero_add, one_mul]
    exact exp_pi_div_two_I
  | succ k ih =>
    have hstep : (((2 * ((k + 1 : ℕ) : ℝ) + 1) * (Real.pi / 2) : ℝ) : ℂ) * I =
        (((2 * (k : ℝ) + 1) * (Real.pi / 2) : ℝ) : ℂ) * I + (Real.pi : ℂ) * I := by
      push_cast; ring
    rw [hstep, Complex.exp_add, Complex.exp_pi_mul_I, ih]
    by_cases hk : Even k
    · have hk1 : ¬ Even (k + 1) := by simpa [Nat.even_add_one] using hk
      rw [if_pos hk, if_neg hk1]; ring
    · have hk1 : Even (k + 1) := by simpa [Nat.even_add_one] using hk
      rw [if_neg hk, if_pos hk1]; ring

private theorem expChar_time_add (μ t h : ℝ) :
    expChar μ (t + h) = Complex.exp (((μ * h : ℝ) : ℂ) * I) * expChar μ t := by
  simp only [expChar, ← Complex.exp_add]
  congr 1; push_cast; ring

private theorem twoIntervalRadius_singleWaveLog_sq (β γ ω : ℝ) (m' : ℕ) (t : ℝ) :
    let h := quarterPeriodStep γ
    let A := quarterPeriodScale β γ
    let ρ' : ℂ := (β : ℂ) + I * (ω : ℂ)
    let z₀ : ℂ := -(((2 * (m' : ℝ) : ℝ) : ℂ)) * (Complex.exp (ρ' * (h : ℂ)) - 1) / ρ'
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
      have h2 : (-(((2 * (m' : ℝ) : ℝ) : ℂ)) * (Complex.exp (ρ' * ((t + h : ℝ) : ℂ)) / ρ') -
          -(((2 * (m' : ℝ) : ℝ) : ℂ)) * (Complex.exp (ρ' * (t : ℂ)) / ρ')) =
          Complex.exp (ρ' * (t : ℂ)) * z₀ := by
        dsimp [z₀]; rw [h1]; ring
      have hre := congrArg Complex.re h2
      simpa only [Complex.sub_re, neg_mul, Complex.neg_re, Complex.re_ofReal_mul] using hre
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
      have h2 : (-(((2 * (m' : ℝ) : ℝ) : ℂ)) * (Complex.exp (ρ' * ((t + h + h : ℝ) : ℂ)) / ρ') -
          -(((2 * (m' : ℝ) : ℝ) : ℂ)) * (Complex.exp (ρ' * ((t + h : ℝ) : ℂ)) / ρ')) =
          Complex.exp (ρ' * ((t + h : ℝ) : ℂ)) * z₀ := by
        dsimp [z₀]; rw [h1]; ring
      have hre := congrArg Complex.re h2
      simpa only [Complex.sub_re, neg_mul, Complex.neg_re, Complex.re_ofReal_mul] using hre
    have hexp_th : Real.exp (β * (t + h)) = A * Real.exp (β * t) := by
      dsimp [A, quarterPeriodScale]; rw [mul_add, Real.exp_add, mul_comm]
    have hchar_th : expChar ω (t + h) = Complex.exp (((ω * h : ℝ) : ℂ) * I) * expChar ω t :=
      expChar_time_add ω t h
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
  set z₀ : ℂ := -(((2 * (m' : ℝ) : ℝ) : ℂ)) * (Complex.exp (ρ' * (h : ℂ)) - 1) / ρ'
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
    have hm'_norm : ‖-(((2 * (m' : ℝ) : ℝ) : ℂ))‖ = 2 * (m' : ℝ) := by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    dsimp [z₀]
    rw [norm_div, norm_mul, hm'_norm, hnum, hden',
      quartetRadialCoeff_eq_sqrt hγ m, show quarterPeriodScale β γ = A from rfl,
      div_pow, div_pow, mul_pow, mul_pow, mul_pow, mul_pow,
      Real.sq_sqrt (by positivity : 0 ≤ 1 + A ^ 2), Real.sq_sqrt hd_pos.le,
      Real.sq_sqrt hd'_pos.le, div_eq_div_iff hd'_pos.ne' hd_pos.ne']
    linear_combination 4 * (1 + A ^ 2) * hpyth
  have hrad_sq := twoIntervalRadius_singleWaveLog_sq β γ ω m' t
  dsimp only at hrad_sq
  rw [hcos0, zero_mul, add_zero, hz₀_norm_sq,
    show Real.exp (2 * β * t) = Real.exp (β * t) ^ 2 by
      rw [show 2 * β * t = β * t + β * t by ring, Real.exp_add, sq]] at hrad_sq
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
    set z₀ : ℂ := -(((2 * (m' : ℝ) : ℝ) : ℂ)) * (Complex.exp (ρ' * (h : ℂ)) - 1) / ρ'
    have hz₀_ne : z₀ ≠ 0 := by
      have hm'_ne : -(((2 * (m' : ℝ) : ℝ) : ℂ)) ≠ 0 := by
        have : (0 : ℝ) < 2 * m' := by exact_mod_cast (by omega : 0 < 2 * m')
        exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr this.ne')
      have hA1 : 1 < A := one_lt_quarterPeriodScale (by linarith) hγ
      have hexp_ne : Complex.exp (ρ' * (h : ℂ)) - 1 ≠ 0 := by
        intro he
        have hnorm1 : ‖Complex.exp (ρ' * (h : ℂ))‖ = 1 := by rw [sub_eq_zero.mp he, norm_one]
        have hnormA : ‖Complex.exp (ρ' * (h : ℂ))‖ = A := by
          rw [Complex.norm_exp]
          dsimp only [ρ', A, quarterPeriodScale, h]
          congr 1
          simp [Complex.mul_re]
        linarith
      have hρ'_ne : ρ' ≠ 0 := fun he => by
        have := congrArg Complex.im he; simp [ρ'] at this; linarith
      exact div_ne_zero (mul_ne_zero hm'_ne hexp_ne) hρ'_ne
    have hlim_diff : Tendsto (fun t : ℝ =>
        twoIntervalRadius (singleWaveLog β ω m') h A t * Real.exp (-(β * t)) - C)
        atTop (𝓝 0) := by
      have hsmall : Tendsto (fun t : ℝ => |K| * (Real.exp ((1 / 2 - β) * t) * t ^ 2))
          atTop (𝓝 0) := by
        have h0 := _root_.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (β - 1 / 2)
          (by linarith)
        have h1 := h0.const_mul |K|
        rw [mul_zero] at h1
        refine h1.congr' ?_
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with t _
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
      have h2 := (h1.pow 2).sub_const (C ^ 2)
      rw [sub_self] at h2
      simpa only [sub_add_cancel] using h2
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
      have hrad : twoIntervalRadius (singleWaveLog β ω m') h A t ^ 2 =
          Real.exp (2 * β * t) *
            (‖z₀‖ ^ 2 + Real.cos (ω * h) * (Complex.exp (((ω * h : ℝ) : ℂ) * I) *
              z₀ ^ 2 * expChar (2 * ω) t).re) :=
        twoIntervalRadius_singleWaveLog_sq β γ ω m' t
      have hmul : (twoIntervalRadius (singleWaveLog β ω m') h A t * Real.exp (-(β * t))) ^ 2 =
          ‖z₀‖ ^ 2 + Real.cos (ω * h) * (Complex.exp (((ω * h : ℝ) : ℂ) * I) *
            z₀ ^ 2 * expChar (2 * ω) t).re := by
        rw [mul_pow, hrad]
        have hexp0 : Real.exp (2 * β * t) * Real.exp (-(β * t)) ^ 2 = 1 := by
          rw [sq, ← Real.exp_add, ← Real.exp_add,
            show 2 * β * t + (-(β * t) + -(β * t)) = 0 by ring, Real.exp_zero]
        rw [mul_right_comm (Real.exp (2 * β * t)) _ (Real.exp (-(β * t)) ^ 2), hexp0, one_mul]
      rw [hmul]
      dsimp [P, cf, mu, w₂]
      rw [Fin.sum_univ_three]
      have hchar0 : expChar 0 t = 1 := by simp [expChar]
      have hchar_neg : expChar (-(2 * ω)) t = conj (expChar (2 * ω) t) := by
        simp only [expChar, ← Complex.exp_conj]
        congr 1; rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring
      have hre_split : ∀ u : ℂ, (u.re : ℂ) = (u + conj u) / 2 := fun u => by
        apply Complex.ext
        · simp
        · simp
      rw [hchar0, hchar_neg]
      simp only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow]
      rw [hre_split]
      simp only [map_mul, map_div₀, Complex.conj_ofReal, map_ofNat, map_pow]
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
    obtain ⟨kZ, hkZ⟩ := Real.cos_eq_zero_iff.mp hcos0
    have habs_γ : 0 < |γ| := abs_pos.mpr hγ
    have hω_eq_Z : ω = (2 * (kZ : ℝ) + 1) * |γ| := by
      have hstep : ω * (Real.pi / (2 * |γ|)) = (2 * (kZ : ℝ) + 1) * Real.pi / 2 := hkZ
      apply mul_right_cancel₀ Real.pi_ne_zero
      have hmul : ω * (Real.pi / (2 * |γ|)) * (2 * |γ|) =
          (2 * (kZ : ℝ) + 1) * Real.pi / 2 * (2 * |γ|) :=
        congrArg (fun x => x * (2 * |γ|)) hstep
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
    have hm'_norm : ‖-(((2 * (m' : ℝ) : ℝ) : ℂ))‖ = 2 * (m' : ℝ) := by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    dsimp [z₀, C] at hnorm_eq
    rw [norm_div, norm_mul, hm'_norm, hnum, hden',
      quartetRadialCoeff_eq_sqrt hγ m, show quarterPeriodScale β γ = A from rfl,
      div_pow, div_pow, mul_pow, mul_pow, mul_pow, mul_pow,
      Real.sq_sqrt h1A_pos.le, Real.sq_sqrt hd_pos.le, Real.sq_sqrt hd'_pos.le,
      div_eq_div_iff hd'_pos.ne' hd_pos.ne'] at hnorm_eq
    have hcanc : 4 * (1 + A ^ 2) * ((m' : ℝ) ^ 2 * (β ^ 2 + γ ^ 2)) =
        4 * (1 + A ^ 2) * ((m : ℝ) ^ 2 * (β ^ 2 + ω ^ 2)) := by
      linear_combination hnorm_eq
    exact mul_left_cancel₀ (by positivity : 4 * (1 + A ^ 2) ≠ 0) hcanc
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
    rcases hcond with hirr | hmeq
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
          ((m' : ℝ) ^ 2 - (m : ℝ) ^ 2) /
            ((2 * (k : ℝ) + 1) ^ 2 * (m : ℝ) ^ 2 - (m' : ℝ) ^ 2) := by
        rw [div_pow, div_eq_div_iff hβ2.ne' hden_ne]
        linarith
      set q : ℚ := ((m' : ℚ) ^ 2 - (m : ℚ) ^ 2) /
        ((2 * (k : ℚ) + 1) ^ 2 * (m : ℚ) ^ 2 - (m' : ℚ) ^ 2)
      exact hirr ⟨q, by dsimp [q]; push_cast; exact hrat_eq.symm⟩
    · subst hmeq
      have hm_pos : (0 : ℝ) < (m' : ℝ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hm')
      have hk1 : (1 : ℝ) < (2 * (k : ℝ) + 1) ^ 2 := by
        have hk_pos : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk_ne
        nlinarith
      have hbg : β ^ 2 + γ ^ 2 = β ^ 2 + (2 * (k : ℝ) + 1) ^ 2 * γ ^ 2 :=
        mul_left_cancel₀ hm_pos.ne' hpyth
      nlinarith [hbg, hk1, hγ2]

/-- **Sub-67 trial ordinate aliased by a high-ordinate (`> 67`) odd harmonic.**
For every `β ∈ (2/3, 1)`, there exist `0 < γ ≤ 67` and `ω = 3γ > 67` satisfying
`IsOddHarmonicPythagoreanAlias β γ 1000 ω 2999 1`, so `singleWaveLog β ω 2999` has identically
zero radial discrepancy at the sub-67 trial `(β, γ, 1000)`. -/
theorem exists_lowOrdinate_oddHarmonicAlias_above_sixtySeven {β : ℝ}
    (hlo : 2 / 3 < β) (hhi : β < 1) :
    ∃ γ ω : ℝ, 0 < γ ∧ γ ≤ 67 ∧ 67 < ω ∧
      IsOddHarmonicPythagoreanAlias β γ 1000 ω 2999 1 ∧
      ∀ t : ℝ, radialDiscrepancyOf (singleWaveLog β ω 2999) β γ 1000 t = 0 := by
  set r : ℝ := Real.sqrt (7994001 / 5999)
  have hr_pos : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have hr_sq : r ^ 2 = 7994001 / 5999 := Real.sq_sqrt (by norm_num)
  have hr_lt37 : r < 37 := by
    have hlt : (7994001 : ℝ) / 5999 < 37 ^ 2 := by norm_num
    nlinarith [hr_sq, hlt, hr_pos]
  have hr_gt34 : 34 < r := by
    have hgt : (34 : ℝ) ^ 2 < 7994001 / 5999 := by norm_num
    nlinarith [hr_sq, hgt, hr_pos]
  set γ : ℝ := β * r
  set ω : ℝ := 3 * γ
  have hβ_pos : 0 < β := by linarith
  have hγ_pos : 0 < γ := mul_pos hβ_pos hr_pos
  have hγ_le : γ ≤ 67 := by
    have : γ < 1 * 37 := mul_lt_mul'' hhi hr_lt37 hβ_pos.le hr_pos.le
    linarith
  have hω_gt : 67 < ω := by
    dsimp [ω, γ]
    have : (2 : ℝ) / 3 * 34 < β * r := mul_lt_mul'' hlo hr_gt34 (by norm_num) (by norm_num)
    linarith
  have halias : IsOddHarmonicPythagoreanAlias β γ 1000 ω 2999 1 := by
    refine ⟨by dsimp [ω]; rw [abs_of_pos hγ_pos]; ring, ?_⟩
    dsimp [ω, γ]
    rw [mul_pow, mul_pow, mul_pow, hr_sq]
    ring
  exact ⟨γ, ω, hγ_pos, hγ_le, hω_gt, halias,
    radialDiscrepancyOf_singleWaveLog_eq_zero_of_alias hγ_pos.ne' halias⟩

/-! ### 3. Bohr-spectral breaking of multi-frequency top layers and shallower sublayers -/

/-- **Multi-frequency breaking of the two-interval circle.**
For any finite set `S ⊂ (0, ∞)` of at least two positive frequencies (`2 ≤ S.card`), nonzero
complex amplitudes `a : ℝ → ℂ` on `S`, step `h : ℝ`, and constant `C : ℝ`, the real trigonometric
polynomial `f(t) = ∑_{ω ∈ S} Re(a_ω e^{iωt})` cannot satisfy `f(t)² + f(t + h)² − C → 0` at `+∞`. -/
theorem multiFrequency_trigPoly_not_const_twoInterval (S : Finset ℝ) (hS_pos : ∀ ω ∈ S, 0 < ω)
    (hS2 : 2 ≤ S.card) (a : ℝ → ℂ) (ha : ∀ ω ∈ S, a ω ≠ 0) (h C : ℝ) :
    let f : ℝ → ℝ := fun t => ∑ ω ∈ S, (a ω * expChar ω t).re
    ¬ Tendsto (fun t : ℝ => f t ^ 2 + f (t + h) ^ 2 - C) atTop (𝓝 0) := by
  classical
  intro f hlim
  set Λ : Finset ℝ := S ∪ S.image Neg.neg
  have hdisj : Disjoint S (S.image Neg.neg) := by
    rw [Finset.disjoint_left]
    intro μ hμS hμNeg
    obtain ⟨ω, hωS, rfl⟩ := Finset.mem_image.mp hμNeg
    linarith [hS_pos (-ω) hμS, hS_pos ω hωS]
  let b : ℝ → ℂ := fun μ =>
    if 0 < μ then (a μ / 2) * (1 + I * Complex.exp (((μ * h : ℝ) : ℂ) * I))
    else (conj (a (-μ)) / 2) * (1 + I * Complex.exp (((μ * h : ℝ) : ℂ) * I))
  have hG_eq : ∀ t : ℝ, ((f t : ℂ) + I * (f (t + h) : ℂ)) = ∑ μ ∈ Λ, b μ * expChar μ t := by
    intro t
    dsimp [Λ]
    rw [Finset.sum_union hdisj, Finset.sum_image (fun x _ y _ hxy => neg_inj.mp hxy)]
    dsimp [f]
    rw [Complex.ofReal_sum, Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ω hω => ?_
    have hω0 : 0 < ω := hS_pos ω hω
    have hneg0 : ¬ 0 < -ω := by linarith
    dsimp [b]
    rw [if_pos hω0, if_neg hneg0, neg_neg]
    have hre_split : ∀ z : ℂ, ((z.re : ℝ) : ℂ) = (z + conj z) / 2 := fun z => by
      apply Complex.ext <;> simp
    have hconj_char : ∀ s : ℝ, conj (expChar ω s) = expChar (-ω) s := fun s => by
      simp only [expChar, ← Complex.exp_conj]
      congr 1
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    have hshift_pos : expChar ω (t + h) = Complex.exp (((ω * h : ℝ) : ℂ) * I) * expChar ω t :=
      expChar_time_add ω t h
    have hshift_neg : expChar (-ω) (t + h) =
        Complex.exp ((((-ω) * h : ℝ) : ℂ) * I) * expChar (-ω) t :=
      expChar_time_add (-ω) t h
    rw [hre_split, hre_split, map_mul, map_mul, hconj_char t, hconj_char (t + h),
      hshift_pos, hshift_neg]
    ring
  set Λp : Finset ℝ := Λ.filter fun μ => b μ ≠ 0
  have hsurj : S ⊆ Λp.image abs := by
    intro ω hω
    have hω0 : 0 < ω := hS_pos ω hω
    have hωΛ : ω ∈ Λ := Finset.mem_union_left _ hω
    have hnegΛ : -ω ∈ Λ := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨ω, hω, rfl⟩)
    by_cases hb_pos : b ω ≠ 0
    · exact Finset.mem_image.mpr ⟨ω, Finset.mem_filter.mpr ⟨hωΛ, hb_pos⟩, abs_of_pos hω0⟩
    · push Not at hb_pos
      have hb_neg : b (-ω) ≠ 0 := by
        intro hb_neg0
        dsimp [b] at hb_pos hb_neg0
        rw [if_pos hω0] at hb_pos
        rw [if_neg (by linarith), neg_neg] at hb_neg0
        have ha0 : a ω / 2 ≠ 0 := div_ne_zero (ha ω hω) two_ne_zero
        have hca0 : conj (a ω) / 2 ≠ 0 :=
          div_ne_zero (map_ne_zero_iff (starRingEnd ℂ) (RingHom.injective _) |>.mpr (ha ω hω))
            two_ne_zero
        have he1 : 1 + I * Complex.exp (((ω * h : ℝ) : ℂ) * I) = 0 :=
          (mul_eq_zero.mp hb_pos).resolve_left ha0
        have he2 : 1 + I * Complex.exp ((((-ω) * h : ℝ) : ℂ) * I) = 0 :=
          (mul_eq_zero.mp hb_neg0).resolve_left hca0
        have hexp1 : Complex.exp (((ω * h : ℝ) : ℂ) * I) = I := by
          have hI1 : I * (1 + I * Complex.exp (((ω * h : ℝ) : ℂ) * I)) = 0 := by
            rw [he1, mul_zero]
          have hI_sq : (I : ℂ) * I = -1 := Complex.I_mul_I
          linear_combination -hI1 + Complex.exp (((ω * h : ℝ) : ℂ) * I) * hI_sq
        have hexp2 : Complex.exp ((((-ω) * h : ℝ) : ℂ) * I) = I := by
          have hI2 : I * (1 + I * Complex.exp ((((-ω) * h : ℝ) : ℂ) * I)) = 0 := by
            rw [he2, mul_zero]
          have hI_sq : (I : ℂ) * I = -1 := Complex.I_mul_I
          linear_combination -hI2 + Complex.exp ((((-ω) * h : ℝ) : ℂ) * I) * hI_sq
        have hprod : Complex.exp (((ω * h : ℝ) : ℂ) * I) *
            Complex.exp ((((-ω) * h : ℝ) : ℂ) * I) = 1 := by
          rw [← Complex.exp_add,
            show ((ω * h : ℝ) : ℂ) * I + (((-ω) * h : ℝ) : ℂ) * I = 0 by push_cast; ring,
            Complex.exp_zero]
        rw [hexp1, hexp2, Complex.I_mul_I] at hprod
        norm_num at hprod
      exact Finset.mem_image.mpr ⟨-ω, Finset.mem_filter.mpr ⟨hnegΛ, hb_neg⟩,
        by rw [abs_neg, abs_of_pos hω0]⟩
  have hcard_Λp : 2 ≤ Λp.card :=
    hS2.trans ((Finset.card_le_card hsurj).trans Finset.card_image_le)
  have hΛp_ne : Λp.Nonempty := Finset.card_pos.mp (by omega)
  set μmax : ℝ := Λp.max' hΛp_ne
  set μmin : ℝ := Λp.min' hΛp_ne
  have hlt_minmax : μmin < μmax := by
    refine lt_of_le_of_ne (Λp.min'_le _ (Λp.max'_mem hΛp_ne)) fun heq => ?_
    have hsub : Λp ⊆ {μmin} := fun μ hμ =>
      Finset.mem_singleton.mpr (le_antisymm (heq ▸ Λp.le_max' μ hμ) (Λp.min'_le μ hμ))
    have := hcard_Λp.trans (Finset.card_le_card hsub)
    simp at this
  set lam : ℝ := μmax - μmin
  have hlam_pos : 0 < lam := sub_pos.mpr hlt_minmax
  -- Sum over `Option (Λp × Λp)` (`none` carries `-C * expChar 0`)
  set idx : Finset (Option (ℝ × ℝ)) := insert none ((Λp ×ˢ Λp).image some)
  let cf : Option (ℝ × ℝ) → ℂ
    | none => -(C : ℂ)
    | some p => b p.1 * conj (b p.2)
  let mu : Option (ℝ × ℝ) → ℝ
    | none => 0
    | some p => p.1 - p.2
  set P : ℝ → ℂ := fun t => ∑ x ∈ idx, cf x * expChar (mu x) t
  have hG_filter : ∀ t : ℝ, ∑ μ ∈ Λ, b μ * expChar μ t = ∑ μ ∈ Λp, b μ * expChar μ t := fun t => by
    dsimp [Λp]
    rw [← Finset.sum_filter_add_sum_filter_not Λ (fun μ => b μ ≠ 0)]
    have hzero : ∑ μ ∈ Λ.filter (fun μ => ¬ b μ ≠ 0), b μ * expChar μ t = 0 :=
      Finset.sum_eq_zero fun μ hμ => by
        have hb0 : b μ = 0 := not_not.mp (Finset.mem_filter.mp hμ).2
        rw [hb0, zero_mul]
    rw [hzero, add_zero]
  have hP_eq : ∀ t : ℝ, P t = (((f t ^ 2 + f (t + h) ^ 2 - C : ℝ) : ℂ)) := fun t => by
    dsimp [P, idx]
    rw [Finset.sum_insert (by simp), Finset.sum_image (fun _ _ _ _ h => Option.some.inj h)]
    dsimp [cf, mu]
    have hchar0 : expChar 0 t = 1 := by simp [expChar]
    rw [hchar0, mul_one]
    have hprod_eq : (∑ x ∈ Λp ×ˢ Λp, b x.1 * conj (b x.2) * expChar (x.1 - x.2) t) =
        ((f t : ℂ) + I * (f (t + h) : ℂ)) * conj ((f t : ℂ) + I * (f (t + h) : ℂ)) := by
      rw [hG_eq t, hG_filter t, map_sum, Finset.sum_mul_sum, ← Finset.sum_product']
      refine Finset.sum_congr rfl fun p _ => ?_
      have hconj_e : conj (expChar p.2 t) = expChar (-p.2) t := by
        simp only [expChar, ← Complex.exp_conj]
        congr 1
        rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
        push_cast; ring
      rw [map_mul, hconj_e, show b p.1 * expChar p.1 t * (conj (b p.2) * expChar (-p.2) t) =
        b p.1 * conj (b p.2) * (expChar p.1 t * expChar (-p.2) t) by ring,
        expChar_add, sub_eq_add_neg]
    have hnorm_re : ((f t : ℂ) + I * (f (t + h) : ℂ)) *
        conj ((f t : ℂ) + I * (f (t + h) : ℂ)) = (((f t ^ 2 + f (t + h) ^ 2 : ℝ) : ℂ)) := by
      apply Complex.ext
      · simp [sq]
      · simp [sq]; ring
    rw [hprod_eq, hnorm_re]
    push_cast; ring
  have hP_ap : HTGeometry.IsBohrAlmostPeriodic P :=
    isBohrAlmostPeriodic_sum idx
      (fun x _ => continuous_const.mul (continuous_expChar (mu x)))
      (fun x _ => isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_expChar (mu x)))
  have hP_tendsto : Tendsto P atTop (𝓝 0) := by
    have hc := (Complex.continuous_ofReal.tendsto 0).comp hlim
    simpa only [Function.comp_def, Complex.ofReal_zero, ← hP_eq] using hc
  have hP_zero : P = fun _ => 0 :=
    funext (HTGeometry.eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero hP_ap hP_tendsto)
  have hb_lam_zero : bohrCoefficient P lam = 0 := by
    rw [hP_zero]; unfold bohrCoefficient; simp [bohrMean_zero]
  have hb_lam_val : bohrCoefficient P lam = b μmax * conj (b μmin) := by
    dsimp [P]
    rw [bohrCoefficient_sum_expChar, Finset.sum_insert (by simp),
      Finset.sum_image (fun _ _ _ _ h => Option.some.inj h)]
    have h0 : mu none ≠ lam := by dsimp [mu]; exact hlam_pos.ne
    rw [if_neg h0, zero_add]
    have huniq : ∀ p ∈ Λp ×ˢ Λp,
        (if p.1 - p.2 = lam then b p.1 * conj (b p.2) else 0) =
          if p = (μmax, μmin) then b μmax * conj (b μmin) else 0 := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      have hle1 : p.1 ≤ μmax := Λp.le_max' p.1 hp1
      have hge2 : μmin ≤ p.2 := Λp.min'_le p.2 hp2
      by_cases heq : p = (μmax, μmin)
      · subst heq; simp [lam]
      · rw [if_neg heq, if_neg]
        intro hdiff
        apply heq
        apply Prod.ext <;> dsimp [lam] at hdiff <;> linarith
    dsimp [cf, mu]
    rw [Finset.sum_congr rfl huniq, Finset.sum_ite_eq',
      if_pos (Finset.mem_product.mpr ⟨Λp.max'_mem hΛp_ne, Λp.min'_mem hΛp_ne⟩)]
  have hmax_ne : b μmax ≠ 0 := (Finset.mem_filter.mp (Λp.max'_mem hΛp_ne)).2
  have hmin_ne : conj (b μmin) ≠ 0 :=
    map_ne_zero_iff (starRingEnd ℂ) (RingHom.injective _) |>.mpr
      (Finset.mem_filter.mp (Λp.min'_mem hΛp_ne)).2
  exact mul_ne_zero hmax_ne hmin_ne (hb_lam_val.symm.trans hb_lam_zero)

/-- **Sublayer non-cancellation under strict contraction `0 < r < 1`.**
For any nonzero top frequency `μ₀ ≠ 0`, nonzero complex weight `b₀ ≠ 0`, contraction factor
`0 < r < 1`, nonempty finite positive frequency set `S₂ ⊂ (0, ∞)`, and nonzero coefficients `c`
on `S₂`, `f₂(t) = ∑_{ν ∈ S₂} Re(c_ν e^{iνt})` cannot satisfy
`Re(b̄₀ e^{-iμ₀ t} (f₂(t) + i r f₂(t + h))) → 0` at `+∞`. -/
theorem sublayer_perturbation_not_tendsto_zero {μ₀ r : ℝ} (hμ₀ : μ₀ ≠ 0) (hr0 : 0 < r)
    (hr1 : r < 1) {b₀ : ℂ} (hb₀ : b₀ ≠ 0) (S₂ : Finset ℝ) (hS₂_ne : S₂.Nonempty)
    (hS₂_pos : ∀ ν ∈ S₂, 0 < ν) (c : ℝ → ℂ) (hc : ∀ ν ∈ S₂, c ν ≠ 0) (h : ℝ) :
    let f₂ : ℝ → ℝ := fun t => ∑ ν ∈ S₂, (c ν * expChar ν t).re
    ¬ Tendsto (fun t : ℝ =>
        (conj b₀ * expChar (-μ₀) t * ((f₂ t : ℂ) + I * ((r * f₂ (t + h) : ℝ) : ℂ))).re)
      atTop (𝓝 0) := by
  classical
  intro f₂ hlim
  set Λ₂ : Finset ℝ := S₂ ∪ S₂.image Neg.neg
  have hdisj : Disjoint S₂ (S₂.image Neg.neg) := by
    rw [Finset.disjoint_left]
    intro μ hμS hμNeg
    obtain ⟨ν, hνS, rfl⟩ := Finset.mem_image.mp hμNeg
    linarith [hS₂_pos (-ν) hμS, hS₂_pos ν hνS]
  let d : ℝ → ℂ := fun μ =>
    if 0 < μ then (c μ / 2) * (1 + I * (r : ℂ) * Complex.exp (((μ * h : ℝ) : ℂ) * I))
    else (conj (c (-μ)) / 2) * (1 + I * (r : ℂ) * Complex.exp (((μ * h : ℝ) : ℂ) * I))
  have hd_ne : ∀ μ ∈ Λ₂, d μ ≠ 0 := by
    intro μ hμ
    have hfac_ne : 1 + I * (r : ℂ) * Complex.exp (((μ * h : ℝ) : ℂ) * I) ≠ 0 := by
      intro h0
      have hnorm : ‖I * (r : ℂ) * Complex.exp (((μ * h : ℝ) : ℂ) * I)‖ = 1 := by
        have heq : I * (r : ℂ) * Complex.exp (((μ * h : ℝ) : ℂ) * I) = -1 := by
          linear_combination h0
        rw [heq, norm_neg, norm_one]
      have hexp_u : ‖Complex.exp (((μ * h : ℝ) : ℂ) * I)‖ = 1 := by
        rw [Complex.norm_exp]; simp
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr0, hexp_u, mul_one] at hnorm
      linarith
    rcases Finset.mem_union.mp hμ with hpos | hneg
    · dsimp [d]
      rw [if_pos (hS₂_pos μ hpos)]
      exact mul_ne_zero (div_ne_zero (hc μ hpos) two_ne_zero) hfac_ne
    · obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hneg
      dsimp [d]
      rw [if_neg (by linarith [hS₂_pos ν hν]), neg_neg]
      exact mul_ne_zero
        (div_ne_zero (map_ne_zero_iff (starRingEnd ℂ) (RingHom.injective _) |>.mpr (hc ν hν))
          two_ne_zero)
        hfac_ne
  have hG₂_eq : ∀ t : ℝ, ((f₂ t : ℂ) + I * ((r * f₂ (t + h) : ℝ) : ℂ)) =
      ∑ μ ∈ Λ₂, d μ * expChar μ t := fun t => by
    dsimp [Λ₂]
    rw [Finset.sum_union hdisj, Finset.sum_image (fun x _ y _ hxy => neg_inj.mp hxy)]
    dsimp [f₂]
    rw [Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ν hν => ?_
    have hν0 : 0 < ν := hS₂_pos ν hν
    dsimp [d]
    rw [if_pos hν0, if_neg (by linarith), neg_neg]
    have hre_split : ∀ z : ℂ, ((z.re : ℝ) : ℂ) = (z + conj z) / 2 := fun z => by
      apply Complex.ext <;> simp
    have hconj_char : ∀ s : ℝ, conj (expChar ν s) = expChar (-ν) s := fun s => by
      simp only [expChar, ← Complex.exp_conj]
      congr 1
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    have hshift_pos : expChar ν (t + h) = Complex.exp (((ν * h : ℝ) : ℂ) * I) * expChar ν t :=
      expChar_time_add ν t h
    have hshift_neg : expChar (-ν) (t + h) =
        Complex.exp ((((-ν) * h : ℝ) : ℂ) * I) * expChar (-ν) t :=
      expChar_time_add (-ν) t h
    rw [hre_split, hre_split, map_mul, map_mul, hconj_char t, hconj_char (t + h),
      hshift_pos, hshift_neg]
    ring
  -- Express `2 * Re(...)` as a sum over `Bool × Λ₂`
  set idx : Finset (Bool × ℝ) := ({true, false} : Finset Bool) ×ˢ Λ₂
  let cf : Bool × ℝ → ℂ := fun p =>
    if p.1 then conj b₀ * d p.2 else b₀ * conj (d p.2)
  let mu : Bool × ℝ → ℝ := fun p =>
    if p.1 then p.2 - μ₀ else μ₀ - p.2
  set P : ℝ → ℂ := fun t => ∑ p ∈ idx, cf p * expChar (mu p) t
  have hP_eq : ∀ t : ℝ, P t =
      (((2 * (conj b₀ * expChar (-μ₀) t *
        ((f₂ t : ℂ) + I * ((r * f₂ (t + h) : ℝ) : ℂ))).re : ℝ)) : ℂ) := fun t => by
    dsimp [P, idx]
    rw [Finset.sum_product]
    have hpair : ({true, false} : Finset Bool) = insert true {false} := rfl
    rw [hpair, Finset.sum_insert (by simp), Finset.sum_singleton]
    dsimp [cf, mu]
    have hW : conj b₀ * expChar (-μ₀) t * ((f₂ t : ℂ) + I * ((r * f₂ (t + h) : ℝ) : ℂ)) =
        ∑ μ ∈ Λ₂, conj b₀ * d μ * expChar (μ - μ₀) t := by
      rw [hG₂_eq t, Finset.mul_sum]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [show conj b₀ * expChar (-μ₀) t * (d μ * expChar μ t) =
        conj b₀ * d μ * (expChar μ t * expChar (-μ₀) t) by ring, expChar_add, sub_eq_add_neg]
    have hre2 : ∀ z : ℂ, (((2 * z.re : ℝ) : ℂ)) = z + conj z := fun z => by
      apply Complex.ext <;> simp [two_mul]
    rw [hre2, hW, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    have hconj_e : conj (expChar (μ - μ₀) t) = expChar (μ₀ - μ) t := by
      simp only [expChar, ← Complex.exp_conj]
      congr 1
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    rw [map_mul, map_mul, Complex.conj_conj, hconj_e]
  have hP_ap : HTGeometry.IsBohrAlmostPeriodic P :=
    isBohrAlmostPeriodic_sum idx
      (fun p _ => continuous_const.mul (continuous_expChar (mu p)))
      (fun p _ => isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_expChar (mu p)))
  have hP_tendsto : Tendsto P atTop (𝓝 0) := by
    have hlim2 : Tendsto (fun t : ℝ =>
        2 * (conj b₀ * expChar (-μ₀) t *
          ((f₂ t : ℂ) + I * ((r * f₂ (t + h) : ℝ) : ℂ))).re) atTop (𝓝 0) := by
      simpa using hlim.const_mul 2
    have hc := (Complex.continuous_ofReal.tendsto 0).comp hlim2
    simpa only [Function.comp_def, Complex.ofReal_zero, ← hP_eq] using hc
  have hP_zero : P = fun _ => 0 :=
    funext (HTGeometry.eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero hP_ap hP_tendsto)
  set νmax : ℝ := S₂.max' hS₂_ne
  have hνmax_mem : νmax ∈ S₂ := S₂.max'_mem hS₂_ne
  have hνmax_pos : 0 < νmax := hS₂_pos νmax hνmax_mem
  have habs_le : ∀ μ ∈ Λ₂, |μ| ≤ νmax := by
    intro μ hμ
    rcases Finset.mem_union.mp hμ with hp | hn
    · rw [abs_of_pos (hS₂_pos μ hp)]; exact S₂.le_max' μ hp
    · obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hn
      rw [abs_neg, abs_of_pos (hS₂_pos ν hν)]; exact S₂.le_max' ν hν
  set μstar : ℝ := if 0 < μ₀ then -νmax else νmax
  have hμstar_mem : μstar ∈ Λ₂ := by
    dsimp [μstar, Λ₂]
    split_ifs
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨νmax, hνmax_mem, rfl⟩)
    · exact Finset.mem_union_left _ hνmax_mem
  set σ : ℝ := μstar - μ₀
  have hb_σ_zero : bohrCoefficient P σ = 0 := by
    rw [hP_zero]; unfold bohrCoefficient; simp [bohrMean_zero]
  have hb_σ_val : bohrCoefficient P σ = conj b₀ * d μstar := by
    dsimp [P]
    rw [bohrCoefficient_sum_expChar]
    have huniq : ∀ p ∈ idx,
        (if mu p = σ then cf p else 0) =
          if p = (true, μstar) then conj b₀ * d μstar else 0 := by
      rintro ⟨bflag, μ⟩ hp
      have hμΛ : μ ∈ Λ₂ := (Finset.mem_product.mp hp).2
      have habs := abs_le.mp (habs_le μ hμΛ)
      cases bflag
      · -- `false`: `μ₀ - μ` never equals `μstar - μ₀`
        have hne_p : ((false, μ) : Bool × ℝ) ≠ (true, μstar) :=
          fun h => Bool.false_ne_true (Prod.mk.inj h).1
        have hne_mu : mu (false, μ) ≠ σ := by
          dsimp [mu, σ, μstar]
          rcases lt_or_gt_of_ne hμ₀ with hneg | hpos
          · rw [if_neg (not_lt.mpr hneg.le)]; linarith [habs.1]
          · rw [if_pos hpos]; linarith [habs.2]
        rw [if_neg hne_mu, if_neg hne_p]
      · -- `true`: `μ - μ₀ = μstar - μ₀ ↔ μ = μstar`
        dsimp [mu, cf, σ]
        by_cases heq : μ = μstar
        · subst heq; simp
        · rw [if_neg (fun hz => heq (by linarith)), if_neg (fun hz => heq (Prod.mk.inj hz).2)]
    rw [Finset.sum_congr rfl huniq, Finset.sum_ite_eq',
      if_pos (Finset.mem_product.mpr ⟨by simp, hμstar_mem⟩)]
  have hconj_b₀ : conj b₀ ≠ 0 :=
    map_ne_zero_iff (starRingEnd ℂ) (RingHom.injective _) |>.mpr hb₀
  exact mul_ne_zero hconj_b₀ (hd_ne μstar hμstar_mem) (hb_σ_val.symm.trans hb_σ_zero)

/-! ### 4. Universal `{0, 1}`-occupancy coprime integer-set realization -/

private def waveTarget (β γ : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  x - 2 * (m : ℝ) * (((x : ℂ) ^ (((β : ℂ) + I * (γ : ℂ))) /
    (((β : ℂ) + I * (γ : ℂ)))).re)

private theorem waveTarget_diff_bounds {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (m : ℕ)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    |waveTarget β γ m y - waveTarget β γ m x - (y - x)| ≤
      2 * (m : ℝ) * (y - x) * x ^ (β - 1) := by
  set ρ : ℂ := (β : ℂ) + I * (γ : ℂ)
  have hρ_re0 : 0 < ρ.re := by simp [ρ, hβ0]
  have hρ_re1 : ρ.re ≤ 1 := by simp [ρ, hβ1.le]
  have hρ_ne : ρ ≠ 0 := fun he => by rw [he, Complex.zero_re] at hρ_re0; exact lt_irrefl 0 hρ_re0
  have hρ_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ_ne
  have hmvt := RHTower.norm_ofReal_cpow_sub_cpow_le hx hxy hρ_re0 hρ_re1
  have hdiv : ‖(y : ℂ) ^ ρ / ρ - (x : ℂ) ^ ρ / ρ‖ ≤ (y - x) * x ^ (β - 1) := by
    rw [← sub_div, norm_div, div_le_iff₀ hρ_pos]
    have hre_eq : ρ.re = β := by simp [ρ]
    rw [hre_eq] at hmvt
    linarith
  have hre_le := (Complex.abs_re_le_norm ((y : ℂ) ^ ρ / ρ - (x : ℂ) ^ ρ / ρ)).trans hdiv
  rw [Complex.sub_re] at hre_le
  have hid : waveTarget β γ m y - waveTarget β γ m x - (y - x) =
      -(2 * (m : ℝ) * (((y : ℂ) ^ ρ / ρ).re - ((x : ℂ) ^ ρ / ρ).re)) := by
    dsimp [waveTarget, ρ]; ring
  rw [hid, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * m)]
  calc 2 * (m : ℝ) * |((y : ℂ) ^ ρ / ρ).re - ((x : ℂ) ^ ρ / ρ).re|
      ≤ 2 * (m : ℝ) * ((y - x) * x ^ (β - 1)) :=
        mul_le_mul_of_nonneg_left hre_le (by positivity)
    _ = 2 * (m : ℝ) * (y - x) * x ^ (β - 1) := by ring

private def greedyCoprimeSum (β γ : ℝ) (m Q k₀ : ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 =>
    let s := greedyCoprimeSum β γ m Q k₀ k
    if k₀ ≤ k ∧ s < waveTarget β γ m (((k + 1) * Q : ℕ) : ℝ) then
      s + Real.log ((k * Q + 1 : ℕ) : ℝ)
    else s

private def coprimeWaveIndicator (β γ : ℝ) (m Q k₀ n : ℕ) : ℕ :=
  open Classical in
  if ∃ k : ℕ, k₀ ≤ k ∧
      greedyCoprimeSum β γ m Q k₀ k < waveTarget β γ m (((k + 1) * Q : ℕ) : ℝ) ∧
      n = k * Q + 1 then 1 else 0

private theorem sum_coprimeWaveIndicator_block (β γ : ℝ) (m : ℕ) {Q : ℕ} (hQ : 1 ≤ Q)
    (k₀ K : ℕ) :
    ∑ n ∈ Icc 1 (K * Q), (coprimeWaveIndicator β γ m Q k₀ n : ℝ) * Real.log n =
      greedyCoprimeSum β γ m Q k₀ K := by
  induction K with
  | zero => simp [greedyCoprimeSum]
  | succ K ih =>
    have hsplit : Icc 1 ((K + 1) * Q) = Icc 1 (K * Q) ∪ Ioc (K * Q) ((K + 1) * Q) := by
      ext n; simp only [mem_Icc, mem_union, mem_Ioc]
      have : K * Q ≤ (K + 1) * Q := Nat.mul_le_mul_right Q (Nat.le_succ K)
      omega
    have hdisj : Disjoint (Icc 1 (K * Q)) (Ioc (K * Q) ((K + 1) * Q)) :=
      Finset.disjoint_left.mpr fun _ h1 h2 => (mem_Ioc.mp h2).1.not_ge (mem_Icc.mp h1).2
    rw [hsplit, Finset.sum_union hdisj, ih]
    have hblock : ∑ n ∈ Ioc (K * Q) ((K + 1) * Q),
        (coprimeWaveIndicator β γ m Q k₀ n : ℝ) * Real.log n =
        if k₀ ≤ K ∧ greedyCoprimeSum β γ m Q k₀ K < waveTarget β γ m (((K + 1) * Q : ℕ) : ℝ) then
          Real.log ((K * Q + 1 : ℕ) : ℝ)
        else 0 := by
      have hmem1 : K * Q + 1 ∈ Ioc (K * Q) ((K + 1) * Q) := by
        rw [mem_Ioc]; refine ⟨by omega, ?_⟩; rw [Nat.succ_mul]; omega
      have hother : ∀ n ∈ Ioc (K * Q) ((K + 1) * Q), n ≠ K * Q + 1 →
          (coprimeWaveIndicator β γ m Q k₀ n : ℝ) * Real.log n = 0 := by
        intro n hn hne
        obtain ⟨hn_lo, hn_hi⟩ := mem_Ioc.mp hn
        have hw0 : coprimeWaveIndicator β γ m Q k₀ n = 0 := by
          unfold coprimeWaveIndicator
          rw [if_neg]
          rintro ⟨k, _, _, rfl⟩
          rcases lt_trichotomy k K with hlt | rfl | hgt
          · have : (k + 1) * Q ≤ K * Q := Nat.mul_le_mul_right Q hlt
            rw [Nat.succ_mul] at this
            omega
          · exact hne rfl
          · have : (K + 1) * Q ≤ k * Q := Nat.mul_le_mul_right Q hgt
            omega
        rw [hw0]; simp
      rw [Finset.sum_eq_single (K * Q + 1) (fun n hn hne => hother n hn hne)
        (fun hnot => absurd hmem1 hnot)]
      unfold coprimeWaveIndicator
      by_cases hcond : k₀ ≤ K ∧
          greedyCoprimeSum β γ m Q k₀ K < waveTarget β γ m (((K + 1) * Q : ℕ) : ℝ)
      · rw [if_pos ⟨K, hcond.1, hcond.2, rfl⟩, if_pos hcond]; simp
      · rw [if_neg, if_neg hcond]; simp
        rintro ⟨k, hk1, hk2, heq⟩
        have hkK : k = K := Nat.eq_of_mul_eq_mul_right (by omega : 0 < Q) (by omega)
        subst hkK
        exact hcond ⟨hk1, hk2⟩
    rw [hblock, greedyCoprimeSum]
    split_ifs <;> ring

private theorem cpow_exp_eq (s : ℝ) (ρ : ℂ) :
    (Real.exp s : ℂ) ^ ρ = Complex.exp (ρ * (s : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos s).ne'),
    ← Complex.ofReal_log (Real.exp_pos s).le, Real.log_exp, mul_comm]

private theorem mode_log_bound_consequences {θ_w : ℝ → ℝ} {β γ C₀ : ℝ} {m : ℕ}
    (hβ0 : 0 < β) (hγ : γ ≠ 0) (hm : 1 ≤ m) (hC₀ : 0 ≤ C₀)
    (hθ_bound : ∀ x : ℝ, 1 ≤ x →
      |θ_w x - x + 2 * (m : ℝ) *
        (((x : ℂ) ^ (((β : ℂ) + I * (γ : ℂ))) / (((β : ℂ) + I * (γ : ℂ)))).re)| ≤
        C₀ * (1 + Real.log x)) :
    let E_w : ℝ → ℝ := fun t => θ_w (Real.exp t) - Real.exp t
    (∃ C' : ℝ, 0 ≤ C' ∧ ∀ t : ℝ, 0 ≤ t →
      |radialDiscrepancyOf E_w β γ m t| ≤ C' * (1 + t)) ∧
    Tendsto (fun t : ℝ =>
      |radialDiscrepancyOf E_w β γ m t| / (Real.exp (t / 2) * (1 + t) ^ 2)) atTop (𝓝 0) ∧
    ¬ IsLogSqrtSqUnbounded (radialDiscrepancyOf E_w β γ m) ∧
    HasPositivePowerLimsup (fun x => θ_w x - x) β ∧
    (∀ a : ℝ, 1 ≤ a → ¬ IsSqrtLogSqUnbounded (dilationRecurrenceOp a β |γ| (fun x => θ_w x - x))) := by
  intro E_w
  set ρ : ℂ := (β : ℂ) + I * (γ : ℂ)
  set h := quarterPeriodStep γ
  have hh_pos : 0 < h := quarterPeriodStep_pos hγ
  set C' : ℝ := 4 * C₀ * (1 + 2 * h)
  have hC'_nn : 0 ≤ C' := by dsimp [C']; positivity
  have hrad_bound : ∀ t : ℝ, 0 ≤ t → |radialDiscrepancyOf E_w β γ m t| ≤ C' * (1 + t) := by
    intro t ht
    have hmode : ∀ s : ℝ, 0 ≤ s → s ≤ t + 2 * h →
        |E_w s + 2 * (m : ℝ) * (Complex.exp (ρ * (s : ℂ)) / ρ).re| ≤
          C₀ * (1 + 2 * h) * (1 + t) := by
      intro s hs hst
      have hb := hθ_bound (Real.exp s) (Real.one_le_exp hs)
      rw [cpow_exp_eq s ρ, Real.log_exp] at hb
      refine hb.trans ?_
      have h1s : 1 + s ≤ (1 + 2 * h) * (1 + t) := by nlinarith [hh_pos, ht, hst]
      calc C₀ * (1 + s) ≤ C₀ * ((1 + 2 * h) * (1 + t)) :=
            mul_le_mul_of_nonneg_left h1s hC₀
        _ = C₀ * (1 + 2 * h) * (1 + t) := by ring
    have hr := abs_radialDiscrepancyOf_le_of_mode_error hβ0.le hγ m
      (hmode t ht (by linarith))
      (hmode (t + h) (by linarith) (by linarith))
      (hmode (t + 2 * h) (by linarith) le_rfl)
    exact hr.trans_eq (by dsimp [C']; ring)
  have hrad_tendsto : Tendsto (fun t : ℝ =>
      |radialDiscrepancyOf E_w β γ m t| / (Real.exp (t / 2) * (1 + t) ^ 2)) atTop (𝓝 0) := by
    have hexp_inv : Tendsto (fun t : ℝ => C' * Real.exp (-(t / 2))) atTop (𝓝 0) := by
      have h0 := _root_.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (1 / 2) (by norm_num)
      have h1 := h0.const_mul C'
      rw [mul_zero] at h1
      refine h1.congr fun t => ?_
      rw [Real.rpow_zero, one_mul]
      congr 2; ring
    refine squeeze_zero_norm' ?_ hexp_inv
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (abs_nonneg _) (by positivity))]
    have h1t_pos : 0 < 1 + t := by linarith
    calc |radialDiscrepancyOf E_w β γ m t| / (Real.exp (t / 2) * (1 + t) ^ 2)
        ≤ (C' * (1 + t)) / (Real.exp (t / 2) * (1 + t) ^ 2) :=
          div_le_div_of_nonneg_right (hrad_bound t ht) (by positivity)
      _ = C' / (Real.exp (t / 2) * (1 + t)) := by
          rw [sq]; field_simp [h1t_pos.ne', (Real.exp_pos (t / 2)).ne']
      _ ≤ C' / (Real.exp (t / 2) * 1) := by
          refine div_le_div_of_nonneg_left hC'_nn (by positivity) ?_
          exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = C' * Real.exp (-(t / 2)) := by rw [mul_one, Real.exp_neg, div_eq_mul_inv]
  have hnot_unb : ¬ IsLogSqrtSqUnbounded (radialDiscrepancyOf E_w β γ m) := by
    rw [isLogSqrtSqUnbounded_iff_not_eventually_le, not_not]
    obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hrad_tendsto.eventually (gt_mem_nhds one_pos))
    refine ⟨1, max T₀ 0, fun t ht => ?_⟩
    have htT : T₀ ≤ t := (le_max_left _ _).trans ht
    have h1t_pos : 0 < 1 + t := by linarith [(le_max_right T₀ 0).trans ht]
    have hden : 0 < Real.exp (t / 2) * (1 + t) ^ 2 := by positivity
    have hmul := (div_lt_iff₀ hden).mp (hT₀ t htT)
    linarith
  have hlimsup : HasPositivePowerLimsup (fun x => θ_w x - x) β := by
    set C_rad := quartetRadialCoeff β γ m
    have hC_rad_pos : 0 < C_rad := quartetRadialCoeff_pos hγ hm
    set A := quarterPeriodScale β γ
    have hA1 : 1 ≤ A := (one_lt_quarterPeriodScale hβ0 hγ).le
    have hA0 : 0 < A := zero_lt_one.trans_le hA1
    have hsmall : Tendsto (fun t : ℝ => C' * (1 + t) * Real.exp (-(β * t))) atTop (𝓝 0) := by
      have h0 := _root_.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 β hβ0
      have h1 := h0.const_mul (2 * C')
      rw [mul_zero] at h1
      refine squeeze_zero_norm' ?_ h1
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_one]
      have h1t : 1 + t ≤ 2 * t := by linarith
      calc C' * (1 + t) * Real.exp (-(β * t))
          ≤ C' * (2 * t) * Real.exp (-(β * t)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1t hC'_nn) (Real.exp_pos _).le
        _ = 2 * C' * (t * Real.exp (-β * t)) := by rw [neg_mul]; ring
    obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp
      (hsmall.eventually (gt_mem_nhds (half_pos hC_rad_pos)))
    set c₀ : ℝ := C_rad / (8 * Real.exp (2 * β * h))
    have hc₀_pos : 0 < c₀ := div_pos hC_rad_pos (mul_pos (by norm_num) (Real.exp_pos _))
    refine ⟨c₀, hc₀_pos, fun X₀ => ?_⟩
    set t : ℝ := max (max T₁ 1) (Real.log (max X₀ 1))
    have htT₁ : T₁ ≤ t := (le_max_left T₁ 1).trans (le_max_left _ _)
    have ht1 : 1 ≤ t := (le_max_right T₁ 1).trans (le_max_left _ _)
    have hmaxX : 0 < max X₀ 1 := lt_max_of_lt_right zero_lt_one
    have htX : X₀ ≤ Real.exp t := by
      calc X₀ ≤ max X₀ 1 := le_max_left _ _
        _ = Real.exp (Real.log (max X₀ 1)) := (Real.exp_log hmaxX).symm
        _ ≤ Real.exp t := Real.exp_le_exp.mpr (le_max_right _ _)
    have hdisc := hrad_bound t (zero_le_one.trans ht1)
    have hsmall_t := hT₁ t htT₁
    have hrad_ge : C_rad / 2 * Real.exp (β * t) ≤ twoIntervalRadius E_w h A t := by
      have hmul := mul_lt_mul_of_pos_right hsmall_t (Real.exp_pos (β * t))
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at hmul
      have hl := (abs_le.mp hdisc).1
      unfold radialDiscrepancyOf at hl
      linarith
    have hsum3 : twoIntervalRadius E_w h A t ≤
        |E_w t| + 2 * |E_w (t + h)| + |E_w (t + 2 * h)| := by
      rw [twoIntervalRadius_eq_complex_norm hA0]
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      dsimp only [logStepIncrement]
      have h1 : |E_w (t + h) - E_w t| ≤ |E_w (t + h)| + |E_w t| := abs_sub _ _
      have h2 : |(E_w (t + h + h) - E_w (t + h)) / A| ≤ |E_w (t + 2 * h)| + |E_w (t + h)| := by
        rw [abs_div, abs_of_pos hA0]
        refine (div_le_self (abs_nonneg _) hA1).trans ?_
        rw [show t + h + h = t + 2 * h by ring]
        exact abs_sub _ _
      linarith
    have hmax3 : C_rad / 8 * Real.exp (β * t) ≤ |E_w t| ∨
        C_rad / 8 * Real.exp (β * t) ≤ |E_w (t + h)| ∨
        C_rad / 8 * Real.exp (β * t) ≤ |E_w (t + 2 * h)| := by
      by_contra! hall
      linarith [hrad_ge, hsum3, hall.1, hall.2.1, hall.2.2]
    have hpick : ∀ s : ℝ, t ≤ s → s ≤ t + 2 * h → C_rad / 8 * Real.exp (β * t) ≤ |E_w s| →
        ∃ x : ℝ, X₀ ≤ x ∧ c₀ * x ^ β ≤ |θ_w x - x| := by
      intro s hs1 hs2 hEs
      refine ⟨Real.exp s, htX.trans (Real.exp_le_exp.mpr hs1), ?_⟩
      have hrpow : (Real.exp s) ^ β = Real.exp (β * s) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos s), Real.log_exp]; ring
      have hexp_le : Real.exp (β * s) ≤ Real.exp (2 * β * h) * Real.exp (β * t) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith [hβ0, hs2])
      rw [hrpow]
      calc c₀ * Real.exp (β * s)
          ≤ c₀ * (Real.exp (2 * β * h) * Real.exp (β * t)) :=
            mul_le_mul_of_nonneg_left hexp_le hc₀_pos.le
        _ = C_rad / 8 * Real.exp (β * t) := by
            dsimp [c₀]; field_simp [(Real.exp_pos (2 * β * h)).ne']
        _ ≤ |θ_w (Real.exp s) - Real.exp s| := hEs
    rcases hmax3 with h0 | h1 | h2
    · exact hpick t le_rfl (by linarith) h0
    · exact hpick (t + h) (by linarith) (by linarith) h1
    · exact hpick (t + 2 * h) (by linarith) le_rfl h2
  have hall_rec : ∀ a : ℝ, 1 ≤ a →
      ¬ IsSqrtLogSqUnbounded (dilationRecurrenceOp a β |γ| (fun x => θ_w x - x)) := by
    intro a ha
    have ha0 : 0 < a := zero_lt_one.trans_le ha
    let W : ℝ → ℝ := fun x => -(2 * (m : ℝ) * (((x : ℂ) ^ ρ / ρ).re))
    let η : ℝ → ℝ := fun x => (θ_w x - x) - W x
    have hη : ∀ x : ℝ, 16 ≤ x → |η x| ≤ (2 * C₀) * Real.sqrt x * Real.log x ^ 2 := by
      intro x hx
      have hx1 : 1 ≤ x := by linarith
      have hlog2 : 2 ≤ Real.log x := RHTower.two_le_log_of_sixteen_le hx
      have hsqrt1 : 1 ≤ Real.sqrt x := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hx1
      have hb := hθ_bound x hx1
      have heq_η : η x = θ_w x - x + 2 * (m : ℝ) * (((x : ℂ) ^ ρ / ρ).re) := by
        dsimp [η, W]; ring
      rw [heq_η]
      refine hb.trans ?_
      have hpoly : 1 + Real.log x ≤ 2 * (Real.sqrt x * Real.log x ^ 2) := by
        have h1 : 1 + Real.log x ≤ 2 * Real.log x ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hsqrt1 (sq_nonneg (Real.log x))]
      nlinarith [hC₀, hpoly]
    obtain ⟨C₁, X₁, _, hC₁⟩ := abs_dilationRecurrenceOp_le_of_sqrt_log_sq (β := β) (γ := |γ|)
      ha (mul_nonneg zero_le_two hC₀) hη
    rw [isSqrtLogSqUnbounded_iff_not_eventually_le, not_not]
    refine ⟨C₁, max X₁ 16, fun x hx => ?_⟩
    have hxX₁ : X₁ ≤ x := (le_max_left _ _).trans hx
    have hx_pos : 0 < x := by linarith [(le_max_right X₁ 16).trans hx]
    have hW_eq : ∀ y : ℝ, W y =
        ((-(((2 * (m : ℝ) : ℝ) : ℂ)) / ρ) * (y : ℂ) ^ ((β : ℂ) + I * (γ : ℂ))).re := by
      intro y; dsimp [W, ρ]
      rw [show -(((2 * (m : ℝ) : ℝ) : ℂ)) / ((β : ℂ) + I * (γ : ℂ)) *
          (y : ℂ) ^ ((β : ℂ) + I * (γ : ℂ)) =
        -(((2 * (m : ℝ) : ℝ) : ℂ) *
          ((y : ℂ) ^ ((β : ℂ) + I * (γ : ℂ)) / ((β : ℂ) + I * (γ : ℂ)))) by ring,
        Complex.neg_re, Complex.re_ofReal_mul]
    have hW_zero : dilationRecurrenceOp a β |γ| W x = 0 := by
      rw [funext hW_eq]
      have hcos_eq : Real.cos (γ * Real.log a) = Real.cos (|γ| * Real.log a) := by
        rcases abs_choice γ with hc | hc <;> rw [hc]
        simp [neg_mul, Real.cos_neg]
      exact dilationRecurrenceOp_re_cpow_eq_zero ha0 hx_pos hcos_eq
        (-(((2 * (m : ℝ) : ℝ) : ℂ)) / ρ)
    have hsplit : (fun y => θ_w y - y) = fun y => η y + W y := by
      funext y; dsimp [η]; ring
    rw [hsplit, dilationRecurrenceOp_add, hW_zero, add_zero]
    exact hC₁ x hxX₁
  exact ⟨⟨C', hC'_nn, hrad_bound⟩, hrad_tendsto, hnot_unb, hlimsup, hall_rec⟩

private theorem exists_coprimeZeroOneSet_wave_approx {β γ : ℝ} {m Q : ℕ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hQ : 1 ≤ Q) :
    ∃ w : ℕ → ℕ,
      (∀ n : ℕ, (w n = 0 ∨ w n = 1) ∧ (w n = 1 → 2 ≤ n ∧ Nat.Coprime n Q)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
        |(∑ n ∈ Icc 1 ⌊x⌋₊, (w n : ℝ) * Real.log n) - x + 2 * (m : ℝ) *
          (((x : ℂ) ^ (((β : ℂ) + I * (γ : ℂ))) / (((β : ℂ) + I * (γ : ℂ)))).re)| ≤
          C * (1 + Real.log x) := by
  have h1β : 0 < 1 - β := by linarith
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have htend_pow : Tendsto (fun k : ℕ => 2 * (m : ℝ) * ((k * Q : ℕ) : ℝ) ^ (β - 1))
      atTop (𝓝 0) := by
    have h1 := (tendsto_rpow_neg_atTop h1β).comp
      (tendsto_natCast_atTop_atTop.atTop_mul_const hQ0)
    have h2 := h1.const_mul (2 * (m : ℝ))
    rw [mul_zero] at h2
    refine h2.congr fun k => ?_
    simp only [Function.comp_apply, Nat.cast_mul, show -(1 - β) = β - 1 by ring]
  obtain ⟨K₁, hK₁⟩ := eventually_atTop.mp
    (htend_pow.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  obtain ⟨K₂, hK₂⟩ := exists_nat_gt (Real.exp (3 * (Q : ℝ) / 2))
  let k₀ : ℕ := max (max K₁ K₂) 1
  have hk₀1 : 1 ≤ k₀ := le_max_right _ _
  have hstep_small : ∀ k : ℕ, k₀ ≤ k →
      0 ≤ waveTarget β γ m (((k + 1) * Q : ℕ) : ℝ) - waveTarget β γ m ((k * Q : ℕ) : ℝ) ∧
        waveTarget β γ m (((k + 1) * Q : ℕ) : ℝ) - waveTarget β γ m ((k * Q : ℕ) : ℝ) ≤
          Real.log ((k * Q + 1 : ℕ) : ℝ) := by
    intro k hk
    have hk1 : 1 ≤ k := hk₀1.trans hk
    have hkK₁ : K₁ ≤ k := ((le_max_left K₁ K₂).trans (le_max_left _ 1)).trans hk
    have hkK₂ : K₂ ≤ k := ((le_max_right K₁ K₂).trans (le_max_left _ 1)).trans hk
    have hx_pos : (0 : ℝ) < ((k * Q : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hk1 hQ
    have hxy : ((k * Q : ℕ) : ℝ) ≤ (((k + 1) * Q : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_right Q (Nat.le_succ k)
    have hdiff_Q : (((k + 1) * Q : ℕ) : ℝ) - ((k * Q : ℕ) : ℝ) = (Q : ℝ) := by
      push_cast; ring
    have hmvt := waveTarget_diff_bounds (γ := γ) hβ0 hβ1 m hx_pos hxy
    rw [hdiff_Q] at hmvt
    have hsmall : 2 * (m : ℝ) * ((k * Q : ℕ) : ℝ) ^ (β - 1) < 1 / 2 := hK₁ k hkK₁
    have hmul_small : 2 * (m : ℝ) * (Q : ℝ) * ((k * Q : ℕ) : ℝ) ^ (β - 1) ≤ (Q : ℝ) / 2 := by
      nlinarith [hsmall, hQ0]
    have habs := abs_le.mp (hmvt.trans hmul_small)
    have hlog_ge : 3 * (Q : ℝ) / 2 ≤ Real.log ((k * Q + 1 : ℕ) : ℝ) := by
      have hexp_lt : Real.exp (3 * (Q : ℝ) / 2) < ((k * Q + 1 : ℕ) : ℝ) := by
        have hkQ : K₂ ≤ k * Q := hkK₂.trans (Nat.le_mul_of_pos_right k hQ)
        have hkQ1 : (K₂ : ℝ) < ((k * Q + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_of_le hkQ
        exact hK₂.trans hkQ1
      exact (Real.le_log_iff_exp_le (by positivity)).mpr hexp_lt.le
    exact ⟨by linarith, by linarith⟩
  let M₀ : ℝ := |waveTarget β γ m ((k₀ * Q : ℕ) : ℝ)|
  have hM₀ : 0 ≤ M₀ := abs_nonneg _
  have hzero_below : ∀ K : ℕ, K ≤ k₀ → greedyCoprimeSum β γ m Q k₀ K = 0 := by
    intro K hK
    induction K with
    | zero => rfl
    | succ K ih =>
      unfold greedyCoprimeSum
      rw [ih (Nat.le_of_succ_le hK), if_neg]
      rintro ⟨hk, _⟩; omega
  have hinv : ∀ K : ℕ, k₀ ≤ K →
      -M₀ ≤ greedyCoprimeSum β γ m Q k₀ K - waveTarget β γ m ((K * Q : ℕ) : ℝ) ∧
        greedyCoprimeSum β γ m Q k₀ K - waveTarget β γ m ((K * Q : ℕ) : ℝ) ≤
          M₀ + Real.log ((K * Q + 1 : ℕ) : ℝ) := by
    intro K hK
    induction K, hK using Nat.le_induction with
    | base =>
      rw [hzero_below k₀ le_rfl, zero_sub]
      have hlog_pos : 0 ≤ Real.log ((k₀ * Q + 1 : ℕ) : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ k₀ * Q + 1 by omega))
      exact ⟨neg_le_neg (le_abs_self _), (neg_le_abs _).trans (by linarith)⟩
    | succ K hK ih =>
      obtain ⟨hΔ_lo, hΔ_hi⟩ := hstep_small K hK
      have hlog_mono : Real.log ((K * Q + 1 : ℕ) : ℝ) ≤ Real.log (((K + 1) * Q + 1 : ℕ) : ℝ) := by
        refine Real.log_le_log (by positivity) ?_
        exact_mod_cast (show K * Q + 1 ≤ (K + 1) * Q + 1 by
          have : K * Q ≤ (K + 1) * Q := Nat.mul_le_mul_right Q (Nat.le_succ K); omega)
      unfold greedyCoprimeSum
      dsimp only
      by_cases hlt : greedyCoprimeSum β γ m Q k₀ K < waveTarget β γ m (((K + 1) * Q : ℕ) : ℝ)
      · rw [if_pos ⟨hK, hlt⟩]
        exact ⟨by linarith [ih.1], by linarith [hM₀, hlog_mono]⟩
      · rw [if_neg (fun h => hlt h.2)]
        push Not at hlt
        exact ⟨by linarith [hM₀], by linarith [ih.2, hlog_mono]⟩
  have hw_props : ∀ n : ℕ, (coprimeWaveIndicator β γ m Q k₀ n = 0 ∨
      coprimeWaveIndicator β γ m Q k₀ n = 1) ∧
      (coprimeWaveIndicator β γ m Q k₀ n = 1 → 2 ≤ n ∧ Nat.Coprime n Q) := by
    intro n
    unfold coprimeWaveIndicator
    split_ifs with h
    · refine ⟨Or.inr rfl, fun _ => ?_⟩
      obtain ⟨k, hk, _, rfl⟩ := h
      have hk1 : 1 ≤ k := hk₀1.trans hk
      have hge2 : 2 ≤ k * Q + 1 := by
        have : 1 ≤ k * Q := Nat.mul_pos hk1 hQ
        omega
      have hcop : Nat.Coprime (k * Q + 1) Q :=
        Nat.coprime_of_dvd fun p hp hd1 hd2 =>
          hp.not_dvd_one ((Nat.dvd_add_right (dvd_mul_of_dvd_right hd2 k)).mp hd1)
      exact ⟨hge2, hcop⟩
    · exact ⟨Or.inl rfl, fun h01 => nomatch h01⟩
  refine ⟨coprimeWaveIndicator β γ m Q k₀, hw_props, ?_⟩
  set ρ : ℂ := (β : ℂ) + I * (γ : ℂ)
  have hρ_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr fun he => by
    have := congrArg Complex.re he; simp [ρ] at this; linarith
  have hln_k0 : 0 ≤ Real.log (((k₀ + 1 : ℕ) * Q + 2 : ℕ) : ℝ) :=
    Real.log_nonneg (Nat.one_le_cast.mpr (by omega))
  have hq_nn : 0 ≤ ((Q : ℝ) + 1) * (1 + 2 * (m : ℝ)) := by positivity
  let B_init : ℝ := ((k₀ + 1 : ℝ) * Q + 1) * (1 + 2 * (m : ℝ) / ‖ρ‖) +
    M₀ + Real.log (((k₀ + 1 : ℕ) * Q + 2 : ℕ) : ℝ) +
    ((Q : ℝ) + 1) * (1 + 2 * (m : ℝ))
  have hB_init : 0 ≤ B_init := by
    have h1 : 0 ≤ ((k₀ + 1 : ℝ) * Q + 1) * (1 + 2 * (m : ℝ) / ‖ρ‖) := by positivity
    dsimp [B_init]
    linarith [h1, hM₀, hln_k0, hq_nn]
  refine ⟨B_init + 2, by linarith, fun x hx => ?_⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hlogx_nn : 0 ≤ Real.log x := Real.log_nonneg hx
  have hid_wt : (∑ n ∈ Icc 1 ⌊x⌋₊, (coprimeWaveIndicator β γ m Q k₀ n : ℝ) * Real.log n) -
      x + 2 * (m : ℝ) * (((x : ℂ) ^ ρ / ρ).re) =
      (∑ n ∈ Icc 1 ⌊x⌋₊, (coprimeWaveIndicator β γ m Q k₀ n : ℝ) * Real.log n) -
        waveTarget β γ m x := by
    dsimp [waveTarget, ρ]; ring
  rw [hid_wt]
  have hT_crude : ∀ y : ℝ, 1 ≤ y → |waveTarget β γ m y| ≤ y * (1 + 2 * (m : ℝ) / ‖ρ‖) := by
    intro y hy
    have hy0 : 0 < y := zero_lt_one.trans_le hy
    have hc : |(((y : ℂ) ^ ρ / ρ).re)| ≤ y / ‖ρ‖ := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
      have hre : ρ.re = β := by simp [ρ]
      rw [hre]
      exact div_le_div_of_nonneg_right
        ((Real.rpow_le_rpow_of_exponent_le hy hβ1.le).trans_eq (Real.rpow_one y)) hρ_pos.le
    unfold waveTarget
    calc |y - 2 * (m : ℝ) * (((y : ℂ) ^ ρ / ρ).re)|
        ≤ |y| + |2 * (m : ℝ) * (((y : ℂ) ^ ρ / ρ).re)| := abs_sub _ _
      _ = y + 2 * (m : ℝ) * |(((y : ℂ) ^ ρ / ρ).re)| := by
          rw [abs_of_pos hy0, abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ y + 2 * (m : ℝ) * (y / ‖ρ‖) := by gcongr
      _ = y * (1 + 2 * (m : ℝ) / ‖ρ‖) := by ring
  let K : ℕ := ⌊x⌋₊ / Q
  by_cases hKk₀ : K < k₀
  · have hfl_lt : ⌊x⌋₊ < k₀ * Q := (Nat.div_lt_iff_lt_mul hQ).mp hKk₀
    have hθ0 : (∑ n ∈ Icc 1 ⌊x⌋₊, (coprimeWaveIndicator β γ m Q k₀ n : ℝ) * Real.log n) = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      have hn_hi : n ≤ ⌊x⌋₊ := (mem_Icc.mp hn).2
      have hw0 : coprimeWaveIndicator β γ m Q k₀ n = 0 := by
        unfold coprimeWaveIndicator
        rw [if_neg]
        rintro ⟨k, hk, _, rfl⟩
        have : k₀ * Q ≤ k * Q := Nat.mul_le_mul_right Q hk
        omega
      rw [hw0]; simp
    have hx_lt : x < (k₀ + 1 : ℝ) * Q + 1 := by
      have h1 := Nat.lt_floor_add_one x
      have h2 : (⌊x⌋₊ : ℝ) ≤ (k₀ * Q : ℕ) := by exact_mod_cast hfl_lt.le
      push_cast at h2
      linarith
    rw [hθ0, zero_sub, abs_neg]
    calc |waveTarget β γ m x| ≤ x * (1 + 2 * (m : ℝ) / ‖ρ‖) := hT_crude x hx
      _ ≤ ((k₀ + 1 : ℝ) * Q + 1) * (1 + 2 * (m : ℝ) / ‖ρ‖) :=
          mul_le_mul_of_nonneg_right hx_lt.le (by positivity)
      _ ≤ B_init + 2 := by dsimp [B_init]; linarith [hM₀, hln_k0, hq_nn]
      _ ≤ (B_init + 2) * (1 + Real.log x) :=
          le_mul_of_one_le_right (by linarith [hB_init]) (by linarith)
  · push Not at hKk₀
    have hKQ_le_fl : K * Q ≤ ⌊x⌋₊ := by
      rw [mul_comm]; exact Nat.mul_div_le ⌊x⌋₊ Q
    have hfl_lt_succ : ⌊x⌋₊ < (K + 1) * Q := by
      calc ⌊x⌋₊ < K * Q + Q := Nat.lt_div_mul_add hQ
        _ = (K + 1) * Q := (Nat.succ_mul K Q).symm
    have hKQ_pos : 1 ≤ K * Q := Nat.mul_pos (hk₀1.trans hKk₀) hQ
    have hKQ_le_x : ((K * Q : ℕ) : ℝ) ≤ x :=
      (by exact_mod_cast hKQ_le_fl : ((K * Q : ℕ) : ℝ) ≤ ⌊x⌋₊).trans (Nat.floor_le hx0.le)
    have hx_lt_succ : x ≤ ((K * Q : ℕ) : ℝ) + (Q : ℝ) + 1 := by
      have h1 := Nat.lt_floor_add_one x
      have h2 : (⌊x⌋₊ : ℝ) ≤ (((K + 1) * Q : ℕ) : ℝ) := by exact_mod_cast hfl_lt_succ.le
      push_cast at h2 ⊢
      linarith
    have hsplit : Icc 1 ⌊x⌋₊ = Icc 1 (K * Q) ∪ Ioc (K * Q) ⌊x⌋₊ := by
      ext n; simp only [mem_Icc, mem_union, mem_Ioc]; omega
    have hdisj : Disjoint (Icc 1 (K * Q)) (Ioc (K * Q) ⌊x⌋₊) :=
      Finset.disjoint_left.mpr fun _ h1 h2 => (mem_Ioc.mp h2).1.not_ge (mem_Icc.mp h1).2
    have htail_le : |∑ n ∈ Ioc (K * Q) ⌊x⌋₊,
        (coprimeWaveIndicator β γ m Q k₀ n : ℝ) * Real.log n| ≤
        Real.log (((K * Q + 1 : ℕ) : ℝ)) := by
      have hnn : 0 ≤ ∑ n ∈ Ioc (K * Q) ⌊x⌋₊,
          (coprimeWaveIndicator β γ m Q k₀ n : ℝ) * Real.log n := by
        refine Finset.sum_nonneg fun n hn => mul_nonneg (Nat.cast_nonneg _) ?_
        have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
        exact Real.log_nonneg (Nat.one_le_cast.mpr hn1)
      rw [abs_of_nonneg hnn]
      by_cases hmem : K * Q + 1 ≤ ⌊x⌋₊
      · have hother : ∀ n ∈ Ioc (K * Q) ⌊x⌋₊, n ≠ K * Q + 1 →
            (coprimeWaveIndicator β γ m Q k₀ n : ℝ) * Real.log n = 0 := by
          intro n hn hne
          obtain ⟨hn_lo, hn_hi⟩ := mem_Ioc.mp hn
          have hw0 : coprimeWaveIndicator β γ m Q k₀ n = 0 := by
            unfold coprimeWaveIndicator
            rw [if_neg]
            rintro ⟨k, _, _, rfl⟩
            rcases lt_trichotomy k K with hlt | rfl | hgt
            · have : (k + 1) * Q ≤ K * Q := Nat.mul_le_mul_right Q hlt
              rw [Nat.succ_mul] at this; omega
            · exact hne rfl
            · have : (K + 1) * Q ≤ k * Q := Nat.mul_le_mul_right Q hgt
              omega
          rw [hw0]; simp
        rw [Finset.sum_eq_single (K * Q + 1) (fun n hn hne => hother n hn hne)
          (fun hnot => absurd (mem_Ioc.mpr ⟨by omega, hmem⟩) hnot)]
        have hw1 : (coprimeWaveIndicator β γ m Q k₀ (K * Q + 1) : ℝ) ≤ 1 := by
          rcases (hw_props (K * Q + 1)).1 with h0 | h1
          · rw [h0]; simp
          · rw [h1]; simp
        exact mul_le_of_le_one_left
          (Real.log_nonneg (by exact_mod_cast (show 1 ≤ K * Q + 1 by omega))) hw1
      · have hemp : Ioc (K * Q) ⌊x⌋₊ = ∅ := Finset.Ioc_eq_empty (by omega)
        rw [hemp, Finset.sum_empty]
        exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ K * Q + 1 by omega))
    have hθ_eq : (∑ n ∈ Icc 1 ⌊x⌋₊, (coprimeWaveIndicator β γ m Q k₀ n : ℝ) * Real.log n) =
        greedyCoprimeSum β γ m Q k₀ K +
          ∑ n ∈ Ioc (K * Q) ⌊x⌋₊, (coprimeWaveIndicator β γ m Q k₀ n : ℝ) * Real.log n := by
      rw [hsplit, Finset.sum_union hdisj, sum_coprimeWaveIndicator_block β γ m hQ k₀ K]
    obtain ⟨hinv_lo, hinv_hi⟩ := hinv K hKk₀
    have hinv_abs : |greedyCoprimeSum β γ m Q k₀ K - waveTarget β γ m ((K * Q : ℕ) : ℝ)| ≤
        M₀ + Real.log (((K * Q + 1 : ℕ) : ℝ)) := by
      rw [abs_le]
      have hlog_nn : 0 ≤ Real.log (((K * Q + 1 : ℕ) : ℝ)) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ K * Q + 1 by omega))
      exact ⟨by linarith, hinv_hi⟩
    have hT_step : |waveTarget β γ m x - waveTarget β γ m ((K * Q : ℕ) : ℝ)| ≤
        ((Q : ℝ) + 1) * (1 + 2 * (m : ℝ)) := by
      have hKQ1 : (1 : ℝ) ≤ ((K * Q : ℕ) : ℝ) := by exact_mod_cast hKQ_pos
      have hmvt := waveTarget_diff_bounds (γ := γ) hβ0 hβ1 m (zero_lt_one.trans_le hKQ1) hKQ_le_x
      have hrpow_le : ((K * Q : ℕ) : ℝ) ^ (β - 1) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hKQ1 (by linarith)
      have hdx : x - ((K * Q : ℕ) : ℝ) ≤ (Q : ℝ) + 1 := by linarith
      have hdx0 : 0 ≤ x - ((K * Q : ℕ) : ℝ) := by linarith
      have h1 : |waveTarget β γ m x - waveTarget β γ m ((K * Q : ℕ) : ℝ)| ≤
          (x - ((K * Q : ℕ) : ℝ)) +
            2 * (m : ℝ) * (x - ((K * Q : ℕ) : ℝ)) * ((K * Q : ℕ) : ℝ) ^ (β - 1) := by
        have htri := (abs_add_le (waveTarget β γ m x - waveTarget β γ m ((K * Q : ℕ) : ℝ) -
          (x - ((K * Q : ℕ) : ℝ))) (x - ((K * Q : ℕ) : ℝ))).trans
          (add_le_add hmvt (le_of_eq (abs_of_nonneg hdx0)))
        rw [sub_add_cancel] at htri
        linarith [htri]
      have h2 : 2 * (m : ℝ) * (x - ((K * Q : ℕ) : ℝ)) * ((K * Q : ℕ) : ℝ) ^ (β - 1) ≤
          2 * (m : ℝ) * (x - ((K * Q : ℕ) : ℝ)) :=
        mul_le_of_le_one_right (by positivity) hrpow_le
      nlinarith
    have hlog_KQ : Real.log (((K * Q + 1 : ℕ) : ℝ)) ≤ Real.log x + 1 := by
      have hle2x : (((K * Q + 1 : ℕ) : ℝ)) ≤ 2 * x := by
        have hKQ_r : (K : ℝ) * (Q : ℝ) ≤ x := by exact_mod_cast hKQ_le_x
        push_cast
        linarith [hKQ_r, hx]
      calc Real.log (((K * Q + 1 : ℕ) : ℝ)) ≤ Real.log (2 * x) :=
            Real.log_le_log (by positivity) hle2x
        _ = Real.log 2 + Real.log x := Real.log_mul two_ne_zero hx0.ne'
        _ ≤ Real.log x + 1 := by linarith [Real.log_two_lt_d9]
    calc |(∑ n ∈ Icc 1 ⌊x⌋₊, (coprimeWaveIndicator β γ m Q k₀ n : ℝ) * Real.log n) -
            waveTarget β γ m x|
        = |(greedyCoprimeSum β γ m Q k₀ K - waveTarget β γ m ((K * Q : ℕ) : ℝ)) +
            (∑ n ∈ Ioc (K * Q) ⌊x⌋₊, (coprimeWaveIndicator β γ m Q k₀ n : ℝ) * Real.log n) -
            (waveTarget β γ m x - waveTarget β γ m ((K * Q : ℕ) : ℝ))| := by
          rw [hθ_eq]; congr 1; ring
      _ ≤ |greedyCoprimeSum β γ m Q k₀ K - waveTarget β γ m ((K * Q : ℕ) : ℝ)| +
            |∑ n ∈ Ioc (K * Q) ⌊x⌋₊, (coprimeWaveIndicator β γ m Q k₀ n : ℝ) * Real.log n| +
            |waveTarget β γ m x - waveTarget β γ m ((K * Q : ℕ) : ℝ)| :=
          (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (M₀ + Real.log (((K * Q + 1 : ℕ) : ℝ))) + Real.log (((K * Q + 1 : ℕ) : ℝ)) +
            ((Q : ℝ) + 1) * (1 + 2 * (m : ℝ)) :=
          add_le_add (add_le_add hinv_abs htail_le) hT_step
      _ ≤ (B_init + 2) * (1 + Real.log x) := by
          have hpos_term : 0 ≤ ((k₀ + 1 : ℝ) * Q + 1) * (1 + 2 * (m : ℝ) / ‖ρ‖) := by positivity
          dsimp [B_init]
          nlinarith [hlog_KQ, hlogx_nn, hB_init, hpos_term, hln_k0]

/-- **Universal `{0, 1}`-occupancy coprime integer-set realization.**
For every `1/2 < β < 1`, `γ ≠ 0`, `m ≥ 1`, and coprimality modulus `Q ≥ 1`, there exists an
explicit `{0, 1}`-valued weight `w : ℕ → ℕ` supported on `{n ≥ 2 : gcd(n, Q) = 1}` such that
`θ_w(x) = ∑_{1 ≤ n ≤ ⌊x⌋} w(n) log n` satisfies:
1. `|θ_w(x) − x + 2 m Re(x^{β + iγ}/(β + iγ))| ≤ C (1 + log x)` for all `x ≥ 1`;
2. `|radialDiscrepancyOf (fun t => θ_w(e^t) − e^t) β γ m t| ≤ C' (1 + t)` for all `t ≥ 0`, so
   its ratio against `e^{t/2}(1 + t)²` tends to `0` at `+∞` (`¬ IsLogSqrtSqUnbounded`);
3. `HasPositivePowerLimsup (fun x => θ_w x − x) β` holds, and every dilation residual
   `dilationRecurrenceOp a β |γ| (fun x => θ_w x − x)` (`a ≥ 1`, in particular `2, 3, 6`) is
   `O(1 + log x)` (`¬ IsSqrtLogSqUnbounded`). -/
theorem exists_coprimeZeroOneSet_realizing_twoIntervalRadius {β γ : ℝ} {m Q : ℕ}
    (hβ : 1 / 2 < β) (hβ1 : β < 1) (hγ : γ ≠ 0) (hm : 1 ≤ m) (hQ : 1 ≤ Q) :
    ∃ w : ℕ → ℕ,
      (∀ n : ℕ, (w n = 0 ∨ w n = 1) ∧ (w n = 1 → 2 ≤ n ∧ Nat.Coprime n Q)) ∧
      let θ_w : ℝ → ℝ := fun x => ∑ n ∈ Icc 1 ⌊x⌋₊, (w n : ℝ) * Real.log n
      let E_w : ℝ → ℝ := fun t => θ_w (Real.exp t) - Real.exp t
      (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
        |θ_w x - x + 2 * (m : ℝ) *
          (((x : ℂ) ^ (((β : ℂ) + I * (γ : ℂ))) / (((β : ℂ) + I * (γ : ℂ)))).re)| ≤
          C * (1 + Real.log x)) ∧
      (∃ C' : ℝ, 0 ≤ C' ∧ ∀ t : ℝ, 0 ≤ t →
        |radialDiscrepancyOf E_w β γ m t| ≤ C' * (1 + t)) ∧
      Tendsto (fun t : ℝ =>
        |radialDiscrepancyOf E_w β γ m t| / (Real.exp (t / 2) * (1 + t) ^ 2)) atTop (𝓝 0) ∧
      ¬ IsLogSqrtSqUnbounded (radialDiscrepancyOf E_w β γ m) ∧
      HasPositivePowerLimsup (fun x => θ_w x - x) β ∧
      (∀ a : ℝ, 1 ≤ a → ¬ IsSqrtLogSqUnbounded (dilationRecurrenceOp a β |γ| (fun x => θ_w x - x))) := by
  have hβ0 : 0 < β := by linarith
  obtain ⟨w, hw_props, C₀, hC₀, hθ_bound⟩ :=
    exists_coprimeZeroOneSet_wave_approx (γ := γ) (m := m) hβ0 hβ1 hQ
  refine ⟨w, hw_props, ?_⟩
  intro θ_w E_w
  have hcons := mode_log_bound_consequences (θ_w := θ_w) hβ0 hγ hm hC₀ hθ_bound
  exact ⟨⟨C₀, hC₀, hθ_bound⟩, hcons⟩

#print axioms not_isLogSqrtSqUnbounded_singleWaveLog_iff_alias
#print axioms exists_lowOrdinate_oddHarmonicAlias_above_sixtySeven
#print axioms multiFrequency_trigPoly_not_const_twoInterval
#print axioms sublayer_perturbation_not_tendsto_zero
#print axioms exists_coprimeZeroOneSet_realizing_twoIntervalRadius

end GaloisForLFunctions.ZeroConfigurationGeometry
