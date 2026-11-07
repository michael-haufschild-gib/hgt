import GaloisForLFunctions.CompletedArithmeticForms.BesselTailCoshMoment
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The factorial scale of integrated first-atom moments

The exact Bessel tail has a finite cosh moment beyond the mixed Gaussian
radius. Its even moments therefore lose every fixed fraction of the
factorial scale `(2k)! / 2^k`. The quantitative upper bound retains the
complete signed radial density and its exact exponential-profile cost.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace GaloisForLFunctions.CompletedArithmeticForms

private theorem exp_abs_le_two_cosh (x : ℝ) : Real.exp |x| ≤ 2 * Real.cosh x := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx, Real.cosh_eq]
    linarith only [Real.exp_pos (-x)]
  · rw [abs_of_neg hx, Real.cosh_eq]
    linarith only [Real.exp_pos x]

private theorem even_power_le_cosh (k : ℕ) (x : ℝ) :
    x ^ (2 * k) ≤
      2 * ((2 * k).factorial : ℝ) * (4 / 9 : ℝ) ^ k * Real.cosh (3 / 2 * x) := by
  have hf : (0 : ℝ) < (2 * k).factorial := by positivity
  have h := (div_le_iff₀ hf).mp
    (Real.pow_div_factorial_le_exp |(3 / 2 : ℝ) * x|
      (abs_nonneg ((3 / 2 : ℝ) * x)) (2 * k))
  have h' := h.trans (mul_le_mul_of_nonneg_right (exp_abs_le_two_cosh (3 / 2 * x)) hf.le)
  have hs : (4 / 9 : ℝ) * |(3 / 2 : ℝ) * x| ^ 2 = x ^ 2 := by rw [sq_abs]; ring
  have he := congrArg (fun u : ℝ => u ^ k) hs
  rw [mul_pow, ← pow_mul, ← pow_mul] at he
  have hm := mul_le_mul_of_nonneg_left h' (by positivity : (0 : ℝ) ≤ (4 / 9 : ℝ) ^ k)
  rw [he] at hm
  exact hm.trans_eq (by ring)

private theorem normalize_even_power_bound {k : ℕ} {M I : ℝ}
    (h : M ≤ 2 * ((2 * k).factorial : ℝ) * (4 / 9 : ℝ) ^ k * I) :
    ((2 : ℝ) ^ k / (2 * k).factorial) * M ≤ 2 * I * (8 / 9 : ℝ) ^ k := by
  have hf : ((2 * k).factorial : ℝ) ≠ 0 := by positivity
  calc
    _ ≤ ((2 : ℝ) ^ k / (2 * k).factorial) *
        (2 * ((2 * k).factorial : ℝ) * (4 / 9 : ℝ) ^ k * I) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 * I * ((2 : ℝ) ^ k * (4 / 9 : ℝ) ^ k) := by field_simp [hf]
    _ = _ := by rw [← mul_pow]; norm_num

private theorem density_nonneg {q : ℝ} (hq : 3 ≤ q) (b : ℝ) :
    0 ≤ besselFirstAtomTailDensity (b / 2) q := by
  have hs : Real.sqrt 2 < 2 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  exact (besselFirstAtomTailDensity_pos (by linarith only [hq, hs]) (b / 2)).le

private theorem three_halves_lt_pi_half : (3 / 2 : ℝ) < Real.pi / 2 := by
  linarith only [Real.pi_gt_three]

/-- The complete first-atom tail's even frequency moment. -/
def besselFirstAtomEvenMoment (q : ℝ) (k : ℕ) : ℝ :=
  ∫ b : ℝ, b ^ (2 * k) * besselFirstAtomTailDensity (b / 2) q

/-- Normalization by the factorial scale of the integrated local Gaussian. -/
def besselFirstAtomGammaRatio (q : ℝ) (k : ℕ) : ℝ :=
  ((2 : ℝ) ^ k / (2 * k).factorial) * besselFirstAtomEvenMoment q k

/-- An exact source cost from the cosh moment at aperture `3/2`. -/
def besselFirstAtomMomentCost (q : ℝ) : ℝ :=
  2 * Real.pi * besselFirstAtomExponentialTail (Real.cos (3 / 2)) q

private theorem density_integrable {q : ℝ} (hq : 3 ≤ q) :
    Integrable (fun b : ℝ => besselFirstAtomTailDensity (b / 2) q) := by
  have hh := integrable_cosh_besselFirstAtomTailDensity
    (by linarith only [hq] : (1 : ℝ) ≤ q) (η := 0) le_rfl
    (by positivity : (0 : ℝ) < Real.pi / 2)
  simpa only [zero_mul, Real.cosh_zero, one_mul] using hh

private theorem moment_point_bound {q : ℝ} (hq : 3 ≤ q) (k : ℕ) (b : ℝ) :
    b ^ (2 * k) * besselFirstAtomTailDensity (b / 2) q ≤
      (2 * ((2 * k).factorial : ℝ) * (4 / 9 : ℝ) ^ k) *
        (Real.cosh (3 / 2 * b) * besselFirstAtomTailDensity (b / 2) q) := by
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right (even_power_le_cosh k b) (density_nonneg hq b)

/-- Every even frequency moment is integrable, with the complete radial density retained. -/
theorem integrable_besselFirstAtomEvenMoment {q : ℝ} (hq : 3 ≤ q) (k : ℕ) :
    Integrable (fun b : ℝ => b ^ (2 * k) * besselFirstAtomTailDensity (b / 2) q) := by
  have hc := integrable_cosh_besselFirstAtomTailDensity
    (by linarith only [hq] : (1 : ℝ) ≤ q) (η := 3 / 2)
    (by norm_num) three_halves_lt_pi_half
  refine (hc.const_mul (2 * ((2 * k).factorial : ℝ) * (4 / 9 : ℝ) ^ k)).mono'
    ((continuous_id.pow (2 * k)).aestronglyMeasurable.mul
      (density_integrable hq).aestronglyMeasurable) ?_
  filter_upwards with b
  have hp : 0 ≤ b ^ (2 * k) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg b) k
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp (density_nonneg hq b))]
  exact moment_point_bound hq k b

/-- The actual analytic strip supplies an explicit upper bound at every degree. -/
theorem besselFirstAtomEvenMoment_le {q : ℝ} (hq : 3 ≤ q) (k : ℕ) :
    besselFirstAtomEvenMoment q k ≤
      2 * ((2 * k).factorial : ℝ) * (4 / 9 : ℝ) ^ k *
        (Real.pi * besselFirstAtomExponentialTail (Real.cos (3 / 2)) q) := by
  have hc := integrable_cosh_besselFirstAtomTailDensity
    (by linarith only [hq] : (1 : ℝ) ≤ q) (η := 3 / 2)
    (by norm_num) three_halves_lt_pi_half
  have hh := integral_mono (integrable_besselFirstAtomEvenMoment hq k)
    (hc.const_mul (2 * ((2 * k).factorial : ℝ) * (4 / 9 : ℝ) ^ k))
    (moment_point_bound hq k)
  rw [integral_const_mul, integral_cosh_besselFirstAtomTailDensity
    (by linarith only [hq] : (1 : ℝ) ≤ q) (by norm_num) three_halves_lt_pi_half] at hh
  exact hh

theorem besselFirstAtomGammaRatio_nonneg {q : ℝ} (hq : 3 ≤ q) (k : ℕ) :
    0 ≤ besselFirstAtomGammaRatio q k := by
  have hM : 0 ≤ besselFirstAtomEvenMoment q k := by
    apply integral_nonneg
    intro b
    have hp : 0 ≤ b ^ (2 * k) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg b) k
    exact mul_nonneg hp (density_nonneg hq b)
  exact mul_nonneg (by positivity) hM

/-- The actual radial moments lose the integrated Gaussian factorial scale geometrically. -/
theorem besselFirstAtomGammaRatio_le {q : ℝ} (hq : 3 ≤ q) (k : ℕ) :
    besselFirstAtomGammaRatio q k ≤ besselFirstAtomMomentCost q * (8 / 9 : ℝ) ^ k := by
  simpa only [besselFirstAtomGammaRatio, besselFirstAtomMomentCost, mul_assoc] using
    normalize_even_power_bound (besselFirstAtomEvenMoment_le hq k)

/-- Radial integration does not retain a fixed fraction of this factorial scale at every rank. -/
theorem besselFirstAtomGammaRatio_tendsto_zero {q : ℝ} (hq : 3 ≤ q) :
    Tendsto (besselFirstAtomGammaRatio q) atTop (𝓝 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    (by norm_num : |(8 / 9 : ℝ)| < 1)
  have hh := hp.const_mul (besselFirstAtomMomentCost q)
  rw [mul_zero] at hh
  exact squeeze_zero (besselFirstAtomGammaRatio_nonneg hq)
    (besselFirstAtomGammaRatio_le hq) hh

/-- No positive constant is a lower bound for all normalized actual moments. -/
theorem not_uniform_besselFirstAtomGammaRatio {q : ℝ} (hq : 3 ≤ q) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, c ≤ besselFirstAtomGammaRatio q k := by
  rintro ⟨c, hc, hbound⟩
  obtain ⟨k, hk⟩ := ((besselFirstAtomGammaRatio_tendsto_zero hq).eventually
    (gt_mem_nhds hc)).exists
  exact (not_lt_of_ge (hbound k)) hk

#print axioms integrable_besselFirstAtomEvenMoment
#print axioms besselFirstAtomEvenMoment_le
#print axioms besselFirstAtomGammaRatio_le
#print axioms besselFirstAtomGammaRatio_tendsto_zero
#print axioms not_uniform_besselFirstAtomGammaRatio

end GaloisForLFunctions.CompletedArithmeticForms
