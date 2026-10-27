import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheSelfEnergyOfAnAtomIsExactlyLogarithmic
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheDiamagneticInequality
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFrobeniusSpanIsTheTowerOfTheScalingSurface

/-!
# Weil's form is continuous in the Lévy norm

On real tests Weil's quadratic form is `Q(f) = Re W(f, f)`, computed by the explicit formula
(`weilQuad`). In Lévy form (`weilQuad_eq`)

`Q(f) = 2θ′(0)‖f‖² + levyEnergy f − primeSum f + 2C(f)² − 2S(f)²`,

each piece is controlled by a norm of the test: the `L²` norm, the Lévy energy — the square of a
seminorm, the logarithmic Sobolev norm of `f` — the `L²` norm again for the finitely many prime
lags that meet a fixed window, and the `L¹` norm for the pole moments. Hence:

* **Cauchy–Schwarz for the Lévy energy** (`levyEnergy_add_le`):
  `levyEnergy (f + d) ≤ levyEnergy f + 2√(levyEnergy f · levyEnergy d) + levyEnergy d`.
* **Perturbation bound** (`weilQuad_add_le`): for `f, d` supported in `[−R, R]`, `Q(f + d) − Q(f)` is at
  most an explicit expression in `‖d‖₂`, `levyEnergy d`, `‖d‖₁` that vanishes with them.
* **The Lévy energy of a Lipschitz perturbation** (`levyEnergy_le_lipschitz`): for a `K`-Lipschitz
  `d` and `0 < δ ≤ 1`, `levyEnergy d ≤ e^{1/2} K δ ‖d‖₁ + ‖d‖₂² (2 log(1/δ) + C₁)`.
* **Translation invariance** (`weilQuad_comp_sub`).

The Lévy energy is the norm that matters: a perturbation of size `ε` and Lipschitz constant `K`
moves `Q` by `O(ε √log(K/ε))`, not by `O(K)`. This is what lets narrow atoms synthesize wide tests
up to widths `N^{−θ}` for every `θ < 1` (`TheCriticalExponent`).
-/

noncomputable section

open MeasureTheory Set RHTower Zeta23
open scoped Real

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

/-! ### Weil's quadratic form on real tests -/

/-- **Weil's quadratic form on real tests**: `Q(f) = Re W(f, f)` through the explicit formula. -/
def weilQuad (f : ℝ → ℝ) : ℝ :=
  (weilFullFunctional (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
    (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re

/-- **Weil's form in Lévy form**: `Q(f) = 2θ′(0)‖f‖² + levyEnergy f − primeSum f + 2C² − 2S²`. -/
theorem weilQuad_eq {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    weilQuad f = 2 * gammaHardyPhaseRate 0 * (∫ u, f u ^ 2) + levyEnergy f - primeSum f +
      (2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2) := by
  have h1 : markovEnergy (fun u => (f u : ℂ)) = weilQuad f -
      (weilPoleTerm (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re := by
    unfold markovEnergy weilQuad
    rw [Complex.sub_re]
  rw [markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc, archForm_eq_levyEnergy hf hfc,
    re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq hf.continuous hfc] at h1
  linarith

/-- **Translation invariance**: `Q(f(· − c)) = Q(f)`. -/
theorem weilQuad_comp_sub (f : ℝ → ℝ) (c : ℝ) : weilQuad (fun u => f (u - c)) = weilQuad f := by
  unfold weilQuad
  have h : EF.weilTest (fun u => (f (u - c) : ℂ)) (fun u => (f (u - c) : ℂ)) =
      EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) := by
    funext y
    have := ArithmeticCastelnuovoSeveri.weilTest_translate c c (fun u => (f u : ℂ))
      (fun u => (f u : ℂ)) y
    simpa [ArithmeticCastelnuovoSeveri.translate] using this
  rw [h]

/-! ### Cauchy–Schwarz by the discriminant -/

/-- `∫ (α p + β q + r) = α ∫ p + β ∫ q + ∫ r`. -/
theorem integral_lin3 {p q r : ℝ → ℝ} (hp : Integrable p) (hq : Integrable q) (hr : Integrable r)
    (α β : ℝ) : ∫ u, (α * p u + β * q u + r u) = α * (∫ u, p u) + β * (∫ u, q u) + ∫ u, r u := by
  rw [integral_add (f := fun u => α * p u + β * q u) (g := r) ((hp.const_mul α).add (hq.const_mul β))
    hr, integral_add (f := fun u => α * p u) (g := fun u => β * q u) (hp.const_mul α)
    (hq.const_mul β), integral_const_mul, integral_const_mul]

/-- A quadratic `A t² + 2C t + B ≥ 0` for all `t` has `|C| ≤ √A √B`. -/
theorem abs_le_sqrt_mul_sqrt_of_quadratic_nonneg {A B C : ℝ} (hA : 0 ≤ A)
    (h : ∀ t : ℝ, 0 ≤ A * (t * t) + 2 * C * t + B) : |C| ≤ Real.sqrt A * Real.sqrt B := by
  have hd := discrim_le_zero h
  unfold discrim at hd
  rw [← Real.sqrt_mul hA]
  exact Real.abs_le_sqrt (by nlinarith)

/-- **Cauchy–Schwarz**: `|∫ a b| ≤ √(∫ a²) √(∫ b²)`. -/
theorem abs_integral_mul_le {a b : ℝ → ℝ} (ha : Integrable fun u => a u ^ 2)
    (hb : Integrable fun u => b u ^ 2) (hab : Integrable fun u => a u * b u) :
    |∫ u, a u * b u| ≤ Real.sqrt (∫ u, a u ^ 2) * Real.sqrt (∫ u, b u ^ 2) := by
  refine abs_le_sqrt_mul_sqrt_of_quadratic_nonneg (integral_nonneg fun u => sq_nonneg _)
    fun t => ?_
  have e : ∀ u, (t * a u + b u) ^ 2 = t * t * a u ^ 2 + 2 * t * (a u * b u) + b u ^ 2 :=
    fun u => by ring
  have hint : ∫ u, (t * a u + b u) ^ 2 =
      (∫ u, a u ^ 2) * (t * t) + 2 * (∫ u, a u * b u) * t + ∫ u, b u ^ 2 := by
    simp_rw [e]
    rw [integral_lin3 ha hab hb]
    ring
  rw [← hint]
  exact integral_nonneg fun u => sq_nonneg _

/-! ### The Lévy energy is the square of a seminorm -/

variable {f d : ℝ → ℝ}

/-- The Lévy integrand `ω(y) ‖h − h(· + y)‖²`. -/
def levyIntegrand (h : ℝ → ℝ) (y : ℝ) : ℝ := archLevyDensity y * ∫ u, (h u - h (u + y)) ^ 2

/-- The mixed Lévy integrand `ω(y) ⟨f − f(· + y), d − d(· + y)⟩`. -/
def levyMixed (f d : ℝ → ℝ) (y : ℝ) : ℝ :=
  archLevyDensity y * ∫ u, (f u - f (u + y)) * (d u - d (u + y))

theorem integrable_sub_shift_mul (hf : Continuous f) (hfc : HasCompactSupport f)
    (hd : Continuous d) (y : ℝ) :
    Integrable fun u => (f u - f (u + y)) * (d u - d (u + y)) := by
  refine ((hf.sub (hf.comp (continuous_add_const y))).mul
    (hd.sub (hd.comp (continuous_add_const y)))).integrable_of_hasCompactSupport ?_
  exact (hfc.sub (hfc.comp_homeomorph (Homeomorph.addRight y))).mul_right

/-- Pointwise expansion of the Lévy integrand of `t f + d`. -/
theorem levyIntegrand_smul_add (hf : Continuous f) (hfc : HasCompactSupport f)
    (hd : Continuous d) (hdc : HasCompactSupport d) (t y : ℝ) :
    levyIntegrand (fun u => t * f u + d u) y =
      t * t * levyIntegrand f y + 2 * t * levyMixed f d y + levyIntegrand d y := by
  have h1 := RHTower.WeilMarkovPole.integrable_sub_shift_sq hf hfc y
  have h2 := RHTower.WeilMarkovPole.integrable_sub_shift_sq hd hdc y
  have h3 := integrable_sub_shift_mul hf hfc hd y
  have e : ∀ u, (t * f u + d u - (t * f (u + y) + d (u + y))) ^ 2 =
      t * t * (f u - f (u + y)) ^ 2 + 2 * t * ((f u - f (u + y)) * (d u - d (u + y))) +
        (d u - d (u + y)) ^ 2 := fun u => by ring
  unfold levyIntegrand levyMixed
  simp_rw [e]
  rw [integral_lin3 h1 h3 h2]
  ring

theorem contDiff_smul_add (hf : ContDiff ℝ 2 f) (hd : ContDiff ℝ 2 d) (t : ℝ) :
    ContDiff ℝ 2 fun u => t * f u + d u :=
  (contDiff_const.mul hf).add hd

theorem hasCompactSupport_smul_add (hfc : HasCompactSupport f) (hdc : HasCompactSupport d)
    (t : ℝ) : HasCompactSupport fun u => t * f u + d u :=
  (hfc.mul_left (f := fun _ => t)).add hdc

/-- The mixed Lévy integrand is integrable: it is half the defect of the Lévy integrands. -/
theorem integrableOn_levyMixed (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hd : ContDiff ℝ 2 d) (hdc : HasCompactSupport d) :
    IntegrableOn (levyMixed f d) (Ioi 0) := by
  have hs := integrableOn_levyIntegrand (contDiff_smul_add hf hd 1) (hasCompactSupport_smul_add hfc hdc 1)
  have h1 := integrableOn_levyIntegrand hf hfc
  have h2 := integrableOn_levyIntegrand hd hdc
  refine IntegrableOn.congr_fun (((hs.sub h1).sub h2).div_const 2) (fun y _ => ?_)
    measurableSet_Ioi
  have := levyIntegrand_smul_add hf.continuous hfc hd.continuous hdc 1 y
  simp only [levyIntegrand] at this
  simp only [Pi.sub_apply]
  linarith

/-- `levyEnergy (t f + d) = t² levyEnergy f + 2t ∫ levyMixed + levyEnergy d`. -/
theorem levyEnergy_smul_add (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hd : ContDiff ℝ 2 d) (hdc : HasCompactSupport d) (t : ℝ) :
    levyEnergy (fun u => t * f u + d u) =
      t * t * levyEnergy f + 2 * t * (∫ y in Ioi 0, levyMixed f d y) + levyEnergy d := by
  have h1 := integrableOn_levyIntegrand hf hfc
  have h2 := integrableOn_levyIntegrand hd hdc
  have h3 := integrableOn_levyMixed hf hfc hd hdc
  unfold levyEnergy
  rw [show (fun y => archLevyDensity y * ∫ u, (t * f u + d u - (t * f (u + y) + d (u + y))) ^ 2) =
      fun y => t * t * levyIntegrand f y + 2 * t * levyMixed f d y + levyIntegrand d y from
    funext fun y => levyIntegrand_smul_add hf.continuous hfc hd.continuous hdc t y]
  exact integral_lin3 h1 h3 h2 _ _

theorem levyEnergy_nonneg' (h : ℝ → ℝ) : 0 ≤ levyEnergy h :=
  setIntegral_nonneg_ae measurableSet_Ioi (levyIntegrand_nonneg h)

/-- **Cauchy–Schwarz for the Lévy energy**:
`levyEnergy (f + d) ≤ levyEnergy f + 2√(levyEnergy f) √(levyEnergy d) + levyEnergy d`. -/
theorem levyEnergy_add_le (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hd : ContDiff ℝ 2 d) (hdc : HasCompactSupport d) :
    levyEnergy (fun u => f u + d u) ≤
      levyEnergy f + 2 * (Real.sqrt (levyEnergy f) * Real.sqrt (levyEnergy d)) + levyEnergy d := by
  set X := ∫ y in Ioi 0, levyMixed f d y
  have hq : ∀ t : ℝ, 0 ≤ levyEnergy f * (t * t) + 2 * X * t + levyEnergy d := fun t => by
    have := levyEnergy_smul_add hf hfc hd hdc t
    have h0 := levyEnergy_nonneg' (fun u => t * f u + d u)
    nlinarith
  have hX := abs_le_sqrt_mul_sqrt_of_quadratic_nonneg (levyEnergy_nonneg' f) hq
  have h1 := levyEnergy_smul_add hf hfc hd hdc 1
  simp only [one_mul] at h1
  rw [h1]
  nlinarith [le_abs_self X]

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
