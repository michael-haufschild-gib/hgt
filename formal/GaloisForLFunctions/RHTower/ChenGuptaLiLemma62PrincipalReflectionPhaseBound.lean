import GaloisForLFunctions.RHTower.VanDerCorputWeightedSecondGeneral
import GaloisForLFunctions.RHTower.VanDerCorputSecond

/-!
# Guth–Maynard Lemma 6.2 for `ζ`: the reflection phase integral

In the proof of Lemma 6.2 (Guth–Maynard, arXiv:2405.20552, p. 20) the Mellin variable is
separated from the Poisson frequency by the oscillatory integral `∫ v^{-1+iρ} e(-v) dv`.
After the substitution `v = eˣ` it is the unit-amplitude phase integral

`K(ρ; α, β) = ∫_α^β exp(i(ρx − 2πeˣ)) dx`,

whose phase `g(x) = ρx − 2πeˣ` is smooth on all of `ℝ`, with `g' = ρ − 2πeˣ`, `g'' = −2πeˣ`.
This module proves the uniform van der Corput bound `‖K(ρ; α, β)‖ ≤ 28 / √|ρ|` for `|ρ| ≥ 1`,
independent of the interval, and the trivial bound `‖K‖ ≤ |β − α|`.

Mechanism (corpus van der Corput tests, unit weight):
* `ρ < 0`: the conjugate phase `−g` has `(−g)' ≥ |ρ|` and `(−g)'' ≥ 0`, so `‖K‖ ≤ 2/|ρ|`.
* `ρ > 0`: split at `p = log(ρ/4π)`.  Left of `p`, `g' ≥ ρ/2` and `g'' ≤ 0`, so the piece is
  `≤ 8/ρ`; right of `p`, `g'' ≤ −ρ/2`, so the piece is `≤ 10/√(ρ/2)`.
-/

set_option autoImplicit false

open Complex MeasureTheory Set

noncomputable section

namespace RHTower

/-- Guth–Maynard's reflection phase `g_ρ(x) = ρx − 2πeˣ`. -/
def cglGMReflectionPhase (ρ x : ℝ) : ℝ :=
  ρ * x - 2 * Real.pi * Real.exp x

/-- Guth–Maynard's reflection phase integral `K(ρ; α, β) = ∫_α^β exp(i(ρx − 2πeˣ)) dx`. -/
def cglGMReflectionPhaseIntegral (ρ α β : ℝ) : ℂ :=
  ∫ x in α..β, Complex.exp ((cglGMReflectionPhase ρ x : ℂ) * I)

theorem hasDerivAt_cglGMReflectionPhase (ρ x : ℝ) :
    HasDerivAt (cglGMReflectionPhase ρ) (ρ - 2 * Real.pi * Real.exp x) x := by
  exact (((hasDerivAt_id x).const_mul ρ).sub
    ((Real.hasDerivAt_exp x).const_mul (2 * Real.pi))).congr_deriv (by simp)

theorem hasDerivAt_cglGMReflectionPhase_deriv (ρ x : ℝ) :
    HasDerivAt (fun y => ρ - 2 * Real.pi * Real.exp y) (-(2 * Real.pi * Real.exp x)) x := by
  simpa using ((Real.hasDerivAt_exp x).const_mul (2 * Real.pi)).const_sub ρ

theorem continuous_cglGMReflectionPhase_secondDeriv :
    Continuous fun x : ℝ => -(2 * Real.pi * Real.exp x) := by
  fun_prop

theorem continuous_cglGMReflectionPhase (ρ : ℝ) : Continuous (cglGMReflectionPhase ρ) := by
  unfold cglGMReflectionPhase
  fun_prop

/-- The unit weight in the corpus weighted tests. -/
theorem cglGM_unitWeight_hasDerivAt (x : ℝ) :
    HasDerivAt (fun _ : ℝ => (1 : ℝ)) ((fun _ : ℝ => (0 : ℝ)) x) x :=
  hasDerivAt_const x 1

/-- Negative frequency: no stationary point, `‖∫_a^b exp(i g_ρ)‖ ≤ 2/|ρ|`. -/
theorem norm_integral_exp_reflectionPhase_le_of_neg {ρ a b : ℝ} (hab : a ≤ b) (hρ : ρ < 0) :
    ‖∫ x in a..b, Complex.exp ((cglGMReflectionPhase ρ x : ℂ) * I)‖ ≤ 2 / |ρ| := by
  -- the conjugate phase `−g = 2πeˣ − ρx` is increasing with increasing derivative
  have hconj := norm_integral_cexp_neg_phase (a := a) (b := b)
    (g := fun x => -cglGMReflectionPhase ρ x)
    (((Complex.continuous_ofReal.comp (continuous_cglGMReflectionPhase ρ).neg).mul
      continuous_const).cexp.intervalIntegrable a b)
  simp only [neg_neg] at hconj
  rw [hconj]
  refine norm_integral_cexp_ofReal_mul_I_le_mono hab (abs_pos.mpr hρ.ne)
    (g' := fun x => -(ρ - 2 * Real.pi * Real.exp x)) (g'' := fun x => 2 * Real.pi * Real.exp x)
    (fun x _ => (hasDerivAt_cglGMReflectionPhase ρ x).neg)
    (fun x _ => (hasDerivAt_cglGMReflectionPhase_deriv ρ x).neg.congr_deriv (neg_neg _))
    (by fun_prop) (fun x _ => ?_) (fun x _ => by positivity)
  have : 0 < 2 * Real.pi * Real.exp x := by positivity
  rw [abs_of_neg hρ]
  linarith

/-- Positive frequency: two pieces split at `p = log(ρ/4π)`, total `8/ρ + 10/√(ρ/2)`. -/
theorem norm_integral_exp_reflectionPhase_le_of_pos {ρ a b : ℝ} (hab : a ≤ b) (hρ : 0 < ρ) :
    ‖∫ x in a..b, Complex.exp ((cglGMReflectionPhase ρ x : ℂ) * I)‖ ≤
      8 / ρ + 10 / Real.sqrt (ρ / 2) := by
  set p : ℝ := Real.log (ρ / (4 * Real.pi)) with hp
  have hpi : 0 < Real.pi := Real.pi_pos
  have hexp_p : Real.exp p = ρ / (4 * Real.pi) := Real.exp_log (by positivity)
  set c : ℝ := max a (min p b) with hc
  have hac : a ≤ c := le_max_left _ _
  have hcb : c ≤ b := max_le hab (min_le_right _ _)
  have hcont : Continuous fun x => Complex.exp ((cglGMReflectionPhase ρ x : ℂ) * I) :=
    ((Complex.continuous_ofReal.comp (continuous_cglGMReflectionPhase ρ)).mul
      continuous_const).cexp
  -- unit weight: `((1 : ℝ) : ℂ) * exp(i g)`
  have hunit : ∀ u v : ℝ, (∫ x in u..v, ((fun _ : ℝ => (1 : ℝ)) x : ℂ) *
      Complex.exp ((cglGMReflectionPhase ρ x : ℂ) * I)) =
        ∫ x in u..v, Complex.exp ((cglGMReflectionPhase ρ x : ℂ) * I) := by
    intro u v
    simp only [Complex.ofReal_one, one_mul]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := c)
    (hcont.intervalIntegrable a c) (hcont.intervalIntegrable c b)]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · -- left piece: `x ≤ p`, so `g'(x) ≥ ρ/2` and `g'' ≤ 0`
    by_cases hpa : p < a
    · have hca : c = a := by
        rw [hc]; exact max_eq_left ((min_le_left _ _).trans hpa.le)
      rw [hca, intervalIntegral.integral_same, norm_zero]
      positivity
    · have hcp : c ≤ p := by
        rw [hc]; exact max_le (not_lt.mp hpa) (min_le_left _ _)
      rw [← hunit]
      have h := norm_integral_weight_cexp_le_anti hac (by positivity : 0 < ρ / 2)
        (w' := fun _ => 0) (g' := fun x => ρ - 2 * Real.pi * Real.exp x)
        (g'' := fun x => -(2 * Real.pi * Real.exp x))
        (fun x _ => cglGM_unitWeight_hasDerivAt x) continuousOn_const
        (fun _ _ => zero_le_one) (fun _ _ => le_rfl)
        (fun x _ => hasDerivAt_cglGMReflectionPhase ρ x)
        (fun x _ => hasDerivAt_cglGMReflectionPhase_deriv ρ x)
        continuous_cglGMReflectionPhase_secondDeriv.continuousOn
        (fun x hx => ?_) (fun x _ => by simp only [neg_nonpos]; positivity)
      · refine h.trans (le_of_eq ?_)
        field_simp
        norm_num
      · have hx' : x ≤ p := by
          rw [uIcc_of_le hac] at hx
          exact hx.2.trans hcp
        have hle : Real.exp x ≤ ρ / (4 * Real.pi) := hexp_p ▸ Real.exp_le_exp.mpr hx'
        have : 2 * Real.pi * Real.exp x ≤ ρ / 2 := by
          calc 2 * Real.pi * Real.exp x ≤ 2 * Real.pi * (ρ / (4 * Real.pi)) := by gcongr
            _ = ρ / 2 := by field_simp; ring
        linarith
  · -- right piece: `x ≥ p`, so `g''(x) ≤ −ρ/2`
    by_cases hpb : b < p
    · have hcb' : c = b := by
        rw [hc, min_eq_right hpb.le, max_eq_right hab]
      rw [hcb', intervalIntegral.integral_same, norm_zero]
      positivity
    · have hpc : p ≤ c := by
        rw [hc, min_eq_left (not_lt.mp hpb)]; exact le_max_right _ _
      rw [← hunit]
      have h := norm_integral_weight_cexp_secondDeriv_neg hcb (by positivity : 0 < ρ / 2)
        (w' := fun _ => 0) (g' := fun x => ρ - 2 * Real.pi * Real.exp x)
        (g'' := fun x => -(2 * Real.pi * Real.exp x))
        (fun x _ => cglGM_unitWeight_hasDerivAt x) continuousOn_const
        (fun _ _ => zero_le_one) (fun _ _ => le_rfl)
        (fun x _ => hasDerivAt_cglGMReflectionPhase ρ x)
        (fun x _ => hasDerivAt_cglGMReflectionPhase_deriv ρ x)
        continuous_cglGMReflectionPhase_secondDeriv.continuousOn (fun x hx => ?_)
      · simpa using h
      · have hx' : p ≤ x := by
          rw [uIcc_of_le hcb] at hx
          exact hpc.trans hx.1
        have hle : ρ / (4 * Real.pi) ≤ Real.exp x := hexp_p ▸ Real.exp_le_exp.mpr hx'
        have : ρ / 2 ≤ 2 * Real.pi * Real.exp x := by
          calc ρ / 2 = 2 * Real.pi * (ρ / (4 * Real.pi)) := by field_simp; ring
            _ ≤ 2 * Real.pi * Real.exp x := by gcongr
        linarith

/-- `10/√(ρ/2) ≤ 20/√ρ`. -/
theorem ten_div_sqrt_half_le {ρ : ℝ} (hρ : 0 < ρ) :
    10 / Real.sqrt (ρ / 2) ≤ 20 / Real.sqrt ρ := by
  have hs : Real.sqrt ρ / 2 ≤ Real.sqrt (ρ / 2) := by
    rw [show Real.sqrt ρ / 2 = Real.sqrt (ρ / 4) by
      rw [Real.sqrt_div' ρ (by norm_num : (0 : ℝ) ≤ 4),
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsq : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  calc 10 / Real.sqrt (ρ / 2) ≤ 10 / (Real.sqrt ρ / 2) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hs
    _ = 20 / Real.sqrt ρ := by field_simp; norm_num

/-- `c/|ρ| ≤ c/√|ρ|` for `|ρ| ≥ 1`, `c ≥ 0`. -/
theorem div_abs_le_div_sqrt_abs {ρ : ℝ} (hρ : 1 ≤ |ρ|) {c : ℝ} (hc : 0 ≤ c) :
    c / |ρ| ≤ c / Real.sqrt |ρ| := by
  have hsq : 0 < Real.sqrt |ρ| := Real.sqrt_pos.mpr (by linarith)
  refine div_le_div_of_nonneg_left hc hsq ?_
  calc Real.sqrt |ρ| ≤ Real.sqrt |ρ| * Real.sqrt |ρ| :=
        le_mul_of_one_le_right hsq.le (Real.one_le_sqrt.mpr hρ)
    _ = |ρ| := Real.mul_self_sqrt (abs_nonneg ρ)

/-- Uniform van der Corput bound on an ordered interval. -/
theorem norm_integral_exp_reflectionPhase_le {ρ a b : ℝ} (hab : a ≤ b) (hρ : 1 ≤ |ρ|) :
    ‖∫ x in a..b, Complex.exp ((cglGMReflectionPhase ρ x : ℂ) * I)‖ ≤
      28 / Real.sqrt |ρ| := by
  rcases lt_or_gt_of_ne (show ρ ≠ 0 by rintro rfl; norm_num at hρ) with hneg | hpos
  · refine (norm_integral_exp_reflectionPhase_le_of_neg hab hneg).trans ?_
    refine (div_abs_le_div_sqrt_abs hρ (by norm_num : (0 : ℝ) ≤ 2)).trans ?_
    gcongr
    norm_num
  · have h := norm_integral_exp_reflectionPhase_le_of_pos hab hpos
    have h1 := div_abs_le_div_sqrt_abs hρ (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := ten_div_sqrt_half_le hpos
    rw [abs_of_pos hpos] at h1 ⊢
    calc _ ≤ 8 / ρ + 10 / Real.sqrt (ρ / 2) := h
      _ ≤ 8 / Real.sqrt ρ + 20 / Real.sqrt ρ := add_le_add h1 h2
      _ = 28 / Real.sqrt ρ := by ring

/-- **Uniform phase bound.** `‖∫_α^β exp(i(ρx − 2πeˣ)) dx‖ ≤ 28/√|ρ|` for `|ρ| ≥ 1`, all `α, β`. -/
theorem norm_cglGMReflectionPhaseIntegral_le {ρ : ℝ} (hρ : 1 ≤ |ρ|) (α β : ℝ) :
    ‖cglGMReflectionPhaseIntegral ρ α β‖ ≤ 28 / Real.sqrt |ρ| := by
  unfold cglGMReflectionPhaseIntegral
  rcases le_total α β with hab | hba
  · exact norm_integral_exp_reflectionPhase_le hab hρ
  · rw [intervalIntegral.integral_symm, norm_neg]
    exact norm_integral_exp_reflectionPhase_le hba hρ

/-- Trivial bound: the integrand has unit modulus. -/
theorem norm_cglGMReflectionPhaseIntegral_le_length (ρ α β : ℝ) :
    ‖cglGMReflectionPhaseIntegral ρ α β‖ ≤ |β - α| := by
  unfold cglGMReflectionPhaseIntegral
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := α) (b := β) (C := 1)
    (f := fun x => Complex.exp ((cglGMReflectionPhase ρ x : ℂ) * I))
    (fun x _ => by rw [Complex.norm_exp_ofReal_mul_I])
  simpa using h

end RHTower
