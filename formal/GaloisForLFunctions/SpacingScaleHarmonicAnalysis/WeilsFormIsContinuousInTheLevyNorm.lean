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
    simp only [sub_self, sub_zero] at this
    exact this
  rw [h]

/-! ### Cauchy–Schwarz by the discriminant -/

/-- `∫ (α p + β q + r) = α ∫ p + β ∫ q + ∫ r`. -/
theorem integral_lin3 {μ : Measure ℝ} {p q r : ℝ → ℝ} (hp : Integrable p μ) (hq : Integrable q μ)
    (hr : Integrable r μ) (α β : ℝ) :
    ∫ u, (α * p u + β * q u + r u) ∂μ = α * (∫ u, p u ∂μ) + β * (∫ u, q u ∂μ) + ∫ u, r u ∂μ := by
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
  integral_nonneg_of_ae (levyIntegrand_nonneg h)

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

/-! ### The `L²` pieces -/

/-- `|∫ a(t) b(t + c) dt| ≤ ‖a‖₂ ‖b‖₂`. -/
theorem abs_integral_mul_shift_le {a b : ℝ → ℝ} (ha : Continuous a) (hac : HasCompactSupport a)
    (hb : Continuous b) (hbc : HasCompactSupport b) (c : ℝ) :
    |∫ t, a t * b (t + c)| ≤ Real.sqrt (∫ t, a t ^ 2) * Real.sqrt (∫ t, b t ^ 2) := by
  have h1 := integrable_sq_of_continuous ha hac
  have h2 : Integrable fun t => b (t + c) ^ 2 := (integrable_sq_of_continuous hb hbc).comp_add_right c
  have h3 : Integrable fun t => a t * b (t + c) :=
    (ha.mul (hb.comp (continuous_add_const c))).integrable_of_hasCompactSupport hac.mul_right
  have := abs_integral_mul_le h1 h2 h3
  rwa [integral_add_right_eq_self (fun t => b t ^ 2) c] at this

/-- A test supported in `[−R, R]`. -/
def SupportedIn (R : ℝ) (h : ℝ → ℝ) : Prop := ∀ u, R < |u| → h u = 0

theorem supportedIn_add {R : ℝ} {a b : ℝ → ℝ} (ha : SupportedIn R a) (hb : SupportedIn R b) :
    SupportedIn R fun u => a u + b u := fun u hu => by
  show a u + b u = 0
  rw [ha u hu, hb u hu, add_zero]

/-- Lags beyond `2R` move a test supported in `[−R, R]` off any other such test. -/
theorem mul_shift_eq_zero_of_supportedIn {R : ℝ} {a b : ℝ → ℝ} (ha : SupportedIn R a)
    (hb : SupportedIn R b) {c : ℝ} (hc : 2 * R < |c|) (t : ℝ) : a t * b (t + c) = 0 := by
  by_cases ht : R < |t|
  · rw [ha t ht, zero_mul]
  · push Not at ht
    have : R < |t + c| := by
      have := abs_sub_abs_le_abs_sub c (-t)
      rw [abs_neg, sub_neg_eq_add, add_comm] at this
      linarith
    rw [hb _ this, mul_zero]

/-- The number of prime lags meeting the window `[−R, R]`. -/
def lagRange (R : ℝ) : ℕ := ⌈Real.exp (2 * R)⌉₊ + 1

/-- The prime mass `Σ_{k < K_R} Λ(k)/√k` of the lags meeting the window. -/
def primeMass (R : ℝ) : ℝ := ∑ k ∈ Finset.range (lagRange R), vonMangoldtAtom k

theorem vonMangoldtAtom_nonneg' (k : ℕ) : 0 ≤ vonMangoldtAtom k := by
  unfold vonMangoldtAtom
  split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · exact le_rfl

theorem primeMass_nonneg (R : ℝ) : 0 ≤ primeMass R :=
  Finset.sum_nonneg fun k _ => vonMangoldtAtom_nonneg' k

theorem two_mul_lt_abs_log_of_lagRange_le {R : ℝ} {k : ℕ} (hk : lagRange R ≤ k) :
    2 * R < |Real.log k| := by
  have hk' : Real.exp (2 * R) < k := by
    have := Nat.le_ceil (Real.exp (2 * R))
    have : (⌈Real.exp (2 * R)⌉₊ : ℝ) + 1 ≤ k := by exact_mod_cast hk
    linarith
  have hk0 : (0 : ℝ) < k := lt_trans (Real.exp_pos _) hk'
  have := Real.log_lt_log (Real.exp_pos _) hk'
  rw [Real.log_exp] at this
  exact this.trans_le (le_abs_self _)

/-- A prime sum over a window is a finite sum over the lags meeting it. -/
theorem primeSum_eq_sum_of_supportedIn {R : ℝ} {h : ℝ → ℝ} (hh : SupportedIn R h) :
    primeSum h = ∑ k ∈ Finset.range (lagRange R), vonMangoldtAtom k *
      ((∫ t, h t * h (t - Real.log k)) + ∫ t, h t * h (t + Real.log k)) := by
  rw [primeSum]
  refine tsum_eq_sum fun k hk => ?_
  have hk' : lagRange R ≤ k := by simpa using hk
  have hl := two_mul_lt_abs_log_of_lagRange_le hk'
  have e1 : ∀ t, h t * h (t - Real.log k) = 0 := fun t => by
    rw [sub_eq_add_neg]
    exact mul_shift_eq_zero_of_supportedIn hh hh (by rwa [abs_neg]) t
  have e2 : ∀ t, h t * h (t + Real.log k) = 0 := fun t => mul_shift_eq_zero_of_supportedIn hh hh hl t
  simp [e1, e2]

/-- **The prime sum moves by `L²` amounts**:
`|primeSum (f + d) − primeSum f| ≤ 2 P_R (2‖f‖₂‖d‖₂ + ‖d‖₂²)`. -/
theorem abs_primeSum_add_sub_le {R : ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hd : Continuous d) (hdc : HasCompactSupport d) (hfR : SupportedIn R f) (hdR : SupportedIn R d) :
    |primeSum (fun u => f u + d u) - primeSum f| ≤
      2 * primeMass R * (2 * (Real.sqrt (∫ u, f u ^ 2) * Real.sqrt (∫ u, d u ^ 2)) +
        ∫ u, d u ^ 2) := by
  set nf := Real.sqrt (∫ u, f u ^ 2)
  set nd := Real.sqrt (∫ u, d u ^ 2)
  have hnd2 : nd * nd = ∫ u, d u ^ 2 := Real.mul_self_sqrt (integral_nonneg fun u => sq_nonneg _)
  rw [primeSum_eq_sum_of_supportedIn (supportedIn_add hfR hdR), primeSum_eq_sum_of_supportedIn hfR,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [primeMass, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  -- one lag: `∫ (f+d)(f+d)_c − ∫ f f_c = ∫ f d_c + ∫ d f_c + ∫ d d_c`
  have hlag : ∀ c : ℝ, |(∫ t, (f t + d t) * (f (t + c) + d (t + c))) - ∫ t, f t * f (t + c)| ≤
      2 * (nf * nd) + nd * nd := by
    intro c
    have i1 : Integrable fun t => f t * d (t + c) :=
      (hf.mul (hd.comp (continuous_add_const c))).integrable_of_hasCompactSupport hfc.mul_right
    have i2 : Integrable fun t => d t * f (t + c) :=
      (hd.mul (hf.comp (continuous_add_const c))).integrable_of_hasCompactSupport hdc.mul_right
    have i3 : Integrable fun t => d t * d (t + c) :=
      (hd.mul (hd.comp (continuous_add_const c))).integrable_of_hasCompactSupport hdc.mul_right
    have i0 : Integrable fun t => f t * f (t + c) :=
      (hf.mul (hf.comp (continuous_add_const c))).integrable_of_hasCompactSupport hfc.mul_right
    have e : (∫ t, (f t + d t) * (f (t + c) + d (t + c))) - ∫ t, f t * f (t + c) =
        (∫ t, f t * d (t + c)) + (∫ t, d t * f (t + c)) + ∫ t, d t * d (t + c) := by
      rw [show (fun t => (f t + d t) * (f (t + c) + d (t + c))) =
          fun t => f t * f (t + c) + (f t * d (t + c) + d t * f (t + c) + d t * d (t + c)) by
        funext t; ring,
        integral_add (f := fun t => f t * f (t + c))
          (g := fun t => f t * d (t + c) + d t * f (t + c) + d t * d (t + c)) i0 ((i1.add i2).add i3),
        integral_add (f := fun t => f t * d (t + c) + d t * f (t + c))
          (g := fun t => d t * d (t + c)) (i1.add i2) i3,
        integral_add (f := fun t => f t * d (t + c)) (g := fun t => d t * f (t + c)) i1 i2]
      ring
    rw [e]
    have b1 := abs_integral_mul_shift_le hf hfc hd hdc c
    have b2 := abs_integral_mul_shift_le hd hdc hf hfc c
    have b3 := abs_integral_mul_shift_le hd hdc hd hdc c
    calc _ ≤ |∫ t, f t * d (t + c)| + |∫ t, d t * f (t + c)| + |∫ t, d t * d (t + c)| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ nf * nd + nd * nf + nd * nd := add_le_add (add_le_add b1 b2) b3
      _ = 2 * (nf * nd) + nd * nd := by ring
  have hk0 := vonMangoldtAtom_nonneg' k
  have hm := hlag (-Real.log k)
  have hp := hlag (Real.log k)
  simp only [← sub_eq_add_neg] at hm
  rw [← mul_sub, abs_mul, abs_of_nonneg hk0]
  rw [hnd2] at hm hp
  calc vonMangoldtAtom k * |(∫ t, (f t + d t) * (f (t - Real.log k) + d (t - Real.log k))) +
        (∫ t, (f t + d t) * (f (t + Real.log k) + d (t + Real.log k))) -
        ((∫ t, f t * f (t - Real.log k)) + ∫ t, f t * f (t + Real.log k))|
      ≤ vonMangoldtAtom k * ((2 * (nf * nd) + ∫ u, d u ^ 2) + (2 * (nf * nd) + ∫ u, d u ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hk0
        rw [show ∀ a b c e : ℝ, a + b - (c + e) = (a - c) + (b - e) by intros; ring]
        exact (abs_add_le _ _).trans (add_le_add hm hp)
    _ = 2 * vonMangoldtAtom k * (2 * (nf * nd) + ∫ u, d u ^ 2) := by ring

/-! ### The pole pieces -/

theorem abs_moment_le {R : ℝ} {d : ℝ → ℝ} (hd : Continuous d) (hdc : HasCompactSupport d)
    (hdR : SupportedIn R d) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφR : ∀ u, |u| ≤ R → |φ u| ≤ Real.cosh (R / 2)) :
    |∫ u, d u * φ u| ≤ Real.cosh (R / 2) * ∫ u, |d u| := by
  have hint : Integrable fun u => |d u| := (hd.integrable_of_hasCompactSupport hdc).abs
  refine (abs_integral_le_integral_abs).trans ?_
  rw [← integral_const_mul]
  refine integral_mono ((hd.mul hφ).integrable_of_hasCompactSupport hdc.mul_right).abs
    (hint.const_mul _) fun u => ?_
  by_cases hu : R < |u|
  · simp [hdR u hu]
  · push Not at hu
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hφR u hu) (abs_nonneg _)

theorem abs_cosh_half_le {R u : ℝ} (hu : |u| ≤ R) : |Real.cosh (u / 2)| ≤ Real.cosh (R / 2) := by
  rw [abs_of_pos (Real.cosh_pos _), Real.cosh_le_cosh, abs_div, abs_two]
  have : |R / 2| = |R| / 2 := by rw [abs_div, abs_two]
  rw [this]
  linarith [le_abs_self R]

theorem abs_sinh_le_cosh (x : ℝ) : |Real.sinh x| ≤ Real.cosh x := by
  rw [abs_le]
  have h1 := Real.sinh_lt_cosh x
  have h2 := Real.sinh_lt_cosh (-x)
  rw [Real.sinh_neg, Real.cosh_neg] at h2
  constructor <;> linarith

theorem abs_sinh_half_le {R u : ℝ} (hu : |u| ≤ R) : |Real.sinh (u / 2)| ≤ Real.cosh (R / 2) :=
  (abs_sinh_le_cosh _).trans ((le_abs_self _).trans (abs_cosh_half_le hu))

/-! ### The perturbation bound -/

/-- **Weil's form moves by Lévy-norm amounts**: for `f, d` supported in `[−R, R]`,
`Q(f + d) ≤ Q(f) + 2|θ′(0)|(2‖f‖‖d‖ + ‖d‖²) + 2√(L f · L d) + L d + 2P_R(2‖f‖‖d‖ + ‖d‖²)
  + 4 cosh(R/2)(|C f| + |S f|)‖d‖₁ + 4 cosh(R/2)² ‖d‖₁²`. -/
theorem weilQuad_add_le {R : ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hd : ContDiff ℝ 2 d) (hdc : HasCompactSupport d) (hfR : SupportedIn R f)
    (hdR : SupportedIn R d) :
    weilQuad (fun u => f u + d u) ≤ weilQuad f +
      (2 * |gammaHardyPhaseRate 0| * (2 * (Real.sqrt (∫ u, f u ^ 2) * Real.sqrt (∫ u, d u ^ 2)) +
          ∫ u, d u ^ 2) +
        (2 * (Real.sqrt (levyEnergy f) * Real.sqrt (levyEnergy d)) + levyEnergy d) +
        2 * primeMass R * (2 * (Real.sqrt (∫ u, f u ^ 2) * Real.sqrt (∫ u, d u ^ 2)) +
          ∫ u, d u ^ 2) +
        4 * Real.cosh (R / 2) * (|coshHalfMoment f| + |sinhHalfMoment f|) * (∫ u, |d u|) +
        4 * Real.cosh (R / 2) ^ 2 * (∫ u, |d u|) ^ 2) := by
  have hs := contDiff_smul_add hf hd 1
  have hsc := hasCompactSupport_smul_add hfc hdc 1
  simp only [one_mul] at hs hsc
  rw [weilQuad_eq hs hsc, weilQuad_eq hf hfc]
  set nf := Real.sqrt (∫ u, f u ^ 2)
  set nd := Real.sqrt (∫ u, d u ^ 2)
  set N1 := ∫ u, |d u|
  set ch := Real.cosh (R / 2)
  -- the `L²` piece
  have hfi := integrable_sq_of_continuous hf.continuous hfc
  have hdi := integrable_sq_of_continuous hd.continuous hdc
  have hfdi : Integrable fun u => f u * d u :=
    (hf.continuous.mul hd.continuous).integrable_of_hasCompactSupport hfc.mul_right
  have hsq : ∫ u, (f u + d u) ^ 2 = (∫ u, f u ^ 2) + 2 * (∫ u, f u * d u) + ∫ u, d u ^ 2 := by
    rw [show (fun u => (f u + d u) ^ 2) = fun u => 1 * f u ^ 2 + 2 * (f u * d u) + d u ^ 2 by
      funext u; ring, integral_lin3 hfi hfdi hdi]
    ring
  have hcs := abs_integral_mul_le hfi hdi hfdi
  have hnd2 : nd * nd = ∫ u, d u ^ 2 := Real.mul_self_sqrt (integral_nonneg fun u => sq_nonneg _)
  have hL2 : |2 * gammaHardyPhaseRate 0 * (∫ u, (f u + d u) ^ 2) -
      2 * gammaHardyPhaseRate 0 * (∫ u, f u ^ 2)| ≤
      2 * |gammaHardyPhaseRate 0| * (2 * (nf * nd) + ∫ u, d u ^ 2) := by
    rw [hsq, show 2 * gammaHardyPhaseRate 0 * ((∫ u, f u ^ 2) + 2 * (∫ u, f u * d u) +
        ∫ u, d u ^ 2) - 2 * gammaHardyPhaseRate 0 * (∫ u, f u ^ 2) =
        2 * gammaHardyPhaseRate 0 * (2 * (∫ u, f u * d u) + ∫ u, d u ^ 2) by ring, abs_mul,
      abs_mul, abs_two]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (abs_add_le _ _).trans ?_
    have hd2 : |∫ u, d u ^ 2| = ∫ u, d u ^ 2 := abs_of_nonneg (integral_nonneg fun u => sq_nonneg _)
    rw [abs_mul, abs_two, hd2]
    linarith
  -- the Lévy piece
  have hlevy := levyEnergy_add_le hf hfc hd hdc
  -- the prime piece
  have hprime := abs_primeSum_add_sub_le hf.continuous hfc hd.continuous hdc hfR hdR
  -- the pole piece
  have hcf : Continuous fun u => Real.cosh (u / 2) := Real.continuous_cosh.comp (continuous_id.div_const 2)
  have hsf : Continuous fun u => Real.sinh (u / 2) := Real.continuous_sinh.comp (continuous_id.div_const 2)
  have hCadd : coshHalfMoment (fun u => f u + d u) = coshHalfMoment f + coshHalfMoment d := by
    have i1 : Integrable fun u => f u * Real.cosh (u / 2) :=
      (hf.continuous.mul hcf).integrable_of_hasCompactSupport hfc.mul_right
    have i2 : Integrable fun u => d u * Real.cosh (u / 2) :=
      (hd.continuous.mul hcf).integrable_of_hasCompactSupport hdc.mul_right
    unfold coshHalfMoment
    rw [← integral_add i1 i2]
    congr 1; funext u; ring
  have hSadd : sinhHalfMoment (fun u => f u + d u) = sinhHalfMoment f + sinhHalfMoment d := by
    have i1 : Integrable fun u => f u * Real.sinh (u / 2) :=
      (hf.continuous.mul hsf).integrable_of_hasCompactSupport hfc.mul_right
    have i2 : Integrable fun u => d u * Real.sinh (u / 2) :=
      (hd.continuous.mul hsf).integrable_of_hasCompactSupport hdc.mul_right
    unfold sinhHalfMoment
    rw [← integral_add i1 i2]
    congr 1; funext u; ring
  have hCd : |coshHalfMoment d| ≤ ch * N1 :=
    abs_moment_le hd.continuous hdc hdR hcf fun u hu => abs_cosh_half_le hu
  have hSd : |sinhHalfMoment d| ≤ ch * N1 :=
    abs_moment_le hd.continuous hdc hdR hsf fun u hu => abs_sinh_half_le hu
  have hN1 : 0 ≤ N1 := integral_nonneg fun u => abs_nonneg _
  have hch : 0 ≤ ch := (Real.cosh_pos _).le
  have hpole : (2 * coshHalfMoment (fun u => f u + d u) ^ 2 -
      2 * sinhHalfMoment (fun u => f u + d u) ^ 2) -
      (2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2) ≤
      4 * ch * (|coshHalfMoment f| + |sinhHalfMoment f|) * N1 + 4 * ch ^ 2 * N1 ^ 2 := by
    rw [hCadd, hSadd]
    have e : 2 * (coshHalfMoment f + coshHalfMoment d) ^ 2 -
        2 * (sinhHalfMoment f + sinhHalfMoment d) ^ 2 -
        (2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2) =
        4 * coshHalfMoment f * coshHalfMoment d + 2 * coshHalfMoment d ^ 2 -
          4 * sinhHalfMoment f * sinhHalfMoment d - 2 * sinhHalfMoment d ^ 2 := by ring
    rw [e]
    have h1 : 4 * coshHalfMoment f * coshHalfMoment d ≤ 4 * |coshHalfMoment f| * (ch * N1) := by
      nlinarith [abs_nonneg (coshHalfMoment f), mul_le_mul_of_nonneg_left hCd
        (abs_nonneg (coshHalfMoment f)), le_abs_self (coshHalfMoment f * coshHalfMoment d),
        abs_mul (coshHalfMoment f) (coshHalfMoment d)]
    have h2 : -(4 * sinhHalfMoment f * sinhHalfMoment d) ≤ 4 * |sinhHalfMoment f| * (ch * N1) := by
      nlinarith [abs_nonneg (sinhHalfMoment f), mul_le_mul_of_nonneg_left hSd
        (abs_nonneg (sinhHalfMoment f)), neg_abs_le (sinhHalfMoment f * sinhHalfMoment d),
        abs_mul (sinhHalfMoment f) (sinhHalfMoment d)]
    have h3 : coshHalfMoment d ^ 2 ≤ (ch * N1) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hCd 2
    nlinarith [sq_nonneg (sinhHalfMoment d)]
  have hP := (abs_le.mp hprime).1
  have hL := (abs_le.mp hL2).2
  linarith

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
