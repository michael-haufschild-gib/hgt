import GaloisForLFunctions.TransThresholdPairCorrelation.SmoothWindowFrobeniusChannels

/-!
# The Weighted Frobenius Sum as a Smooth Form

For a height weight `W` supported in `[s₀, s₁] ⊆ [T, 2T]` the weighted Frobenius sum of the Gram
matrix of a density `ν` is `L²` times the smooth form `∬ W(τ)² Φ(τ − τ')² ν(τ) ν(τ')`, up to two
errors: the Lipschitz error of sampling `W` on the grid and the deficit `ρ` of the finite lattice
inside the window (`abs_weightedFrobenius_sub_smoothForm_le`). Both error integrals are controlled
by the window Lorentz weight `(1 + ((τ − 3T/2)/T)²)⁻¹`:

* a density with `|ν(τ)| ≤ B + log⁺(|τ|/4T)` satisfies `ν(τ)² ≤ 2B² + 16 √(|τ − c|/T)` for every
  `|c| ≤ 4T` (`sq_le_of_nuBound`), from `log(1 + x) ≤ 4 x^{1/4}`;
* for `ν_X` the prime part of `∫ ν_X² · lorentz` is the Lorentz mean value of the prime polynomial
  (`integral_lorentz_mul_nuX_sq_le`);
* inside `[T + D, 2T − D]` the lattice deficit is `ρ ≤ (c_ϱ/w)² (2/D⁴ + 2/(3hD³) + 1/(D − 1)⁴)`
  (`rho_le_of_dist`).
-/

open MeasureTheory Real Set Finset Filter
open scoped BigOperators ArithmeticFunction
open Zeta23 Zeta23.PrimeSide RHTower

noncomputable section

namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-! ## 1. Growth of densities with a logarithmic bound -/

/-- `log(1 + s²) ≤ 2s` for `s ≥ 0`. -/
theorem log_one_add_sq_le {s : ℝ} (hs : 0 ≤ s) : Real.log (1 + s ^ 2) ≤ 2 * s := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  have := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ 2 * s)
  nlinarith

/-- `log(1 + x) ≤ 4 x^{1/4}` for `x ≥ 0`, through `1 + x ≤ (1 + √x)²`. -/
theorem log_one_add_le_four_sqrt_sqrt {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ 4 * Real.sqrt (Real.sqrt x) := by
  have hs := Real.sqrt_nonneg x
  have h1 : 1 + x ≤ (1 + Real.sqrt x) ^ 2 := by nlinarith [Real.sq_sqrt hx]
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_pow] at h2
  have h3 := log_one_add_sq_le (Real.sqrt_nonneg (Real.sqrt x))
  rw [Real.sq_sqrt hs] at h3
  push_cast at h2
  linarith

/-- `log⁺(|τ|/4T) ≤ log(1 + |τ − c|/4T)` whenever `|c| ≤ 4T`. -/
theorem logPos_le_log_one_add {T c τ : ℝ} (hT : 0 < T) (hc : |c| ≤ 4 * T) :
    max (Real.log (|τ| / (4 * T))) 0 ≤ Real.log (1 + |τ - c| / (4 * T)) := by
  have hq : 0 ≤ |τ - c| / (4 * T) := by positivity
  refine max_le ?_ (Real.log_nonneg (by linarith))
  rcases eq_or_lt_of_le (abs_nonneg τ) with h0 | hpos
  · rw [← h0, zero_div, Real.log_zero]; exact Real.log_nonneg (by linarith)
  · refine Real.log_le_log (by positivity) ?_
    have h1 : |τ| ≤ |τ - c| + |c| := by
      have := abs_add_le (τ - c) c; simpa using this
    rw [div_le_iff₀ (by positivity), add_mul, div_mul_cancel₀ _ (by positivity)]
    linarith

variable {p : Setting} {B : ℝ} {ν : ℝ → ℝ}

/-- **Square growth.** `|ν| ≤ B + log⁺(|τ|/4T)` gives `ν(τ)² ≤ 2B² + 16√(|τ − c|/T)` for `|c| ≤ 4T`. -/
theorem sq_le_of_nuBound (hν : NuBound p B ν) (hB : 0 ≤ B) (hT : 0 < p.T) {c : ℝ}
    (hc : |c| ≤ 4 * p.T) (τ : ℝ) :
    ν τ ^ 2 ≤ 2 * B ^ 2 + 16 * Real.sqrt (|τ - c| / p.T) := by
  set x := |τ - c| / (4 * p.T) with hx
  have hx0 : 0 ≤ x := by positivity
  have h1 : |ν τ| ≤ B + 4 * Real.sqrt (Real.sqrt x) :=
    (hν τ).trans (by linarith [logPos_le_log_one_add (τ := τ) hT hc,
      log_one_add_le_four_sqrt_sqrt hx0])
  have hy : (4 * Real.sqrt (Real.sqrt x)) ^ 2 = 16 * Real.sqrt x := by
    rw [mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]; norm_num
  have hsx : Real.sqrt x = Real.sqrt (|τ - c| / p.T) / 2 := by
    rw [hx, show |τ - c| / (4 * p.T) = (|τ - c| / p.T) / 2 ^ 2 by ring, Real.sqrt_div' _ (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have h0 : 0 ≤ B + 4 * Real.sqrt (Real.sqrt x) := by positivity
  have h2 : ν τ ^ 2 ≤ (B + 4 * Real.sqrt (Real.sqrt x)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  nlinarith [sq_nonneg (B - 4 * Real.sqrt (Real.sqrt x))]

/-- **Pointwise growth.** For `τ ∈ [T, 2T]` and `T ≥ 1`: `|ν(τ')| ≤ B + √|τ' − τ|`. -/
theorem abs_le_of_nuBound (hν : NuBound p B ν) (hT : 1 ≤ p.T) {τ : ℝ}
    (hτ : τ ∈ Icc p.T (2 * p.T)) (τ' : ℝ) : |ν τ'| ≤ B + Real.sqrt |τ' - τ| := by
  have hT0 : 0 < p.T := by linarith
  have hc : |τ| ≤ 4 * p.T := by rw [abs_of_nonneg (by linarith [hτ.1])]; linarith [hτ.2]
  set x := |τ' - τ| / (4 * p.T)
  have hx0 : 0 ≤ x := by positivity
  have h1 := logPos_le_log_one_add (τ := τ') hT0 hc
  have h2 : Real.log (1 + x) ≤ 2 * Real.sqrt x := by
    have := log_one_add_sq_le (Real.sqrt_nonneg x); rwa [Real.sq_sqrt hx0] at this
  have h3 : 2 * Real.sqrt x ≤ Real.sqrt |τ' - τ| := by
    rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ 2), ← Real.sqrt_mul (by norm_num)]
    refine Real.sqrt_le_sqrt ?_
    have : 2 ^ 2 * x = |τ' - τ| / p.T := by simp only [x]; field_simp; ring
    rw [this]; exact div_le_self (abs_nonneg _) hT
  linarith [hν τ']

/-- `√(x + y) ≤ √x + √y`. -/
theorem sqrt_add_le_sqrt_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sqrt_nonneg x, Real.sqrt_nonneg y]

theorem continuous_lorentzW {R : ℝ} (c : ℝ) : Continuous (lorentzW R c) := by
  have h : Continuous fun τ => 1 + ((τ - c) / R) ^ 2 := by fun_prop
  exact h.inv₀ fun τ => by positivity

theorem lorentzW_eq_lor1 (R c τ : ℝ) : lorentzW R c τ = lor1 ((τ - c) / R) := rfl

/-- `∫ lorentz_R(τ − c) √(|τ − c|/R) dτ = R ∫ lor1 √|·|`. -/
theorem integral_lorentzW_mul_sqrt {R : ℝ} (hR : 0 < R) (c : ℝ) :
    ∫ τ, lorentzW R c τ * Real.sqrt (|τ - c| / R) = R * ∫ r, lor1 r * Real.sqrt |r| := by
  have e : (fun τ => lorentzW R c τ * Real.sqrt (|τ - c| / R))
      = fun τ => (fun r => lor1 r * Real.sqrt |r|) ((τ - c) / R) := by
    funext τ
    show lor1 ((τ - c) / R) * Real.sqrt (|τ - c| / R) = lor1 ((τ - c) / R) * Real.sqrt |(τ - c) / R|
    rw [abs_div, abs_of_pos hR]
  rw [e, integral_sub_right_eq_self (fun τ => (fun r => lor1 r * Real.sqrt |r|) (τ / R)) c,
    Measure.integral_comp_div (fun r => lor1 r * Real.sqrt |r|) R, abs_of_pos hR, smul_eq_mul]

theorem integrable_lorentzW_mul_sqrt {R : ℝ} (hR : 0 < R) (c : ℝ) :
    Integrable fun τ => lorentzW R c τ * Real.sqrt (|τ - c| / R) := by
  have h := (integrable_lor1_mul_sqrt.comp_div hR.ne').comp_sub_right c
  refine h.congr (Eventually.of_forall fun τ => ?_)
  simp only [lorentzW_eq_lor1, abs_div, abs_of_pos hR]

/-- `lorentz · ν²` is integrable for a continuous density with a logarithmic bound. -/
theorem integrable_lorentzW_mul_sq (hν : NuBound p B ν) (hB : 0 ≤ B) (hT : 0 < p.T)
    (hνc : Continuous ν) {c : ℝ} (hc : |c| ≤ 4 * p.T) :
    Integrable fun τ => lorentzW p.T c τ * ν τ ^ 2 := by
  have hmaj : Integrable fun τ => 2 * B ^ 2 * lorentzW p.T c τ
      + 16 * (lorentzW p.T c τ * Real.sqrt (|τ - c| / p.T)) :=
    ((integrable_lorentzW hT c).const_mul _).add ((integrable_lorentzW_mul_sqrt hT c).const_mul _)
  refine hmaj.mono' (((continuous_lorentzW c).mul (hνc.pow 2)).aestronglyMeasurable)
    (Eventually.of_forall fun τ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (lorentzW_nonneg _ _ _) (sq_nonneg _))]
  have h := mul_le_mul_of_nonneg_left (sq_le_of_nuBound hν hB hT hc τ) (lorentzW_nonneg p.T c τ)
  linarith

/-- `lor1(· − a) ν²` is integrable for every shift `a`. -/
theorem integrable_lor1_mul_sq (hν : NuBound p B ν) (hB : 0 ≤ B) (hT : 0 < p.T)
    (hνc : Continuous ν) (a : ℝ) : Integrable fun τ => lor1 (τ - a) * ν τ ^ 2 := by
  have hc : |(0:ℝ)| ≤ 4 * p.T := by rw [abs_zero]; linarith
  have hsT : 0 < Real.sqrt p.T := Real.sqrt_pos.mpr hT
  have hmaj : Integrable fun τ => (2 * B ^ 2 + 16 * (Real.sqrt |a| / Real.sqrt p.T)) * lor1 (τ - a)
      + 16 / Real.sqrt p.T * (lor1 (τ - a) * Real.sqrt |τ - a|) :=
    ((integrable_lor1.comp_sub_right a).const_mul _).add
      ((integrable_lor1_mul_sqrt.comp_sub_right a).const_mul _)
  refine hmaj.mono' (((continuous_lor1.comp (continuous_id.sub continuous_const)).mul
    (hνc.pow 2)).aestronglyMeasurable) (Eventually.of_forall fun τ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (lor1_pos _).le (sq_nonneg _))]
  have h := sq_le_of_nuBound hν hB hT hc τ
  rw [sub_zero, Real.sqrt_div' _ hT.le] at h
  have hsq : Real.sqrt |τ| ≤ Real.sqrt |τ - a| + Real.sqrt |a| := by
    refine (Real.sqrt_le_sqrt (show |τ| ≤ |τ - a| + |a| by
      have := abs_add_le (τ - a) a; simpa using this)).trans ?_
    exact sqrt_add_le_sqrt_add_sqrt (abs_nonneg _) (abs_nonneg _)
  have h' : ν τ ^ 2 ≤ 2 * B ^ 2 + 16 * (Real.sqrt |a| / Real.sqrt p.T)
      + 16 / Real.sqrt p.T * Real.sqrt |τ - a| := by
    have : Real.sqrt |τ| / Real.sqrt p.T ≤ Real.sqrt |τ - a| / Real.sqrt p.T
        + Real.sqrt |a| / Real.sqrt p.T := by
      rw [← add_div]; exact div_le_div_of_nonneg_right hsq hsT.le
    have e : 16 / Real.sqrt p.T * Real.sqrt |τ - a| = 16 * (Real.sqrt |τ - a| / Real.sqrt p.T) := by
      ring
    linarith
  have hl := (lor1_pos (τ - a)).le
  nlinarith [mul_le_mul_of_nonneg_left h' hl]

/-- `lor1(· − a) |ν|` is integrable for every shift `a`. -/
theorem integrable_lor1_mul_abs (hν : NuBound p B ν) (hT : 1 ≤ p.T) (hνc : Continuous ν)
    (a : ℝ) : Integrable fun τ => lor1 (τ - a) * |ν τ| := by
  have hT0 : 0 < p.T := by linarith
  have hτ : 3 * p.T / 2 ∈ Icc p.T (2 * p.T) := ⟨by linarith, by linarith⟩
  have hmaj : Integrable fun τ => (B + Real.sqrt |a - 3 * p.T / 2|) * lor1 (τ - a)
      + lor1 (τ - a) * Real.sqrt |τ - a| :=
    ((integrable_lor1.comp_sub_right a).const_mul _).add (integrable_lor1_mul_sqrt.comp_sub_right a)
  refine hmaj.mono' (((continuous_lor1.comp (continuous_id.sub continuous_const)).mul
    hνc.abs).aestronglyMeasurable) (Eventually.of_forall fun τ => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (lor1_pos _)]
  have h := abs_le_of_nuBound hν hT hτ τ
  have hsq : Real.sqrt |τ - 3 * p.T / 2| ≤ Real.sqrt |τ - a| + Real.sqrt |a - 3 * p.T / 2| := by
    refine (Real.sqrt_le_sqrt (show |τ - 3 * p.T / 2| ≤ |τ - a| + |a - 3 * p.T / 2| by
      have := abs_add_le (τ - a) (a - 3 * p.T / 2); simpa using this)).trans ?_
    exact sqrt_add_le_sqrt_add_sqrt (abs_nonneg _) (abs_nonneg _)
  have hl := (lor1_pos (τ - a)).le
  nlinarith [mul_le_mul_of_nonneg_left (h.trans (by linarith [hsq] :
    B + Real.sqrt |τ - 3 * p.T / 2| ≤ B + Real.sqrt |a - 3 * p.T / 2| + Real.sqrt |τ - a|)) hl]

end GaloisForLFunctions.TransThresholdPairCorrelation
