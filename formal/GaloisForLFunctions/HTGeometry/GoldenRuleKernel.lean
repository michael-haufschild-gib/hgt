import GaloisForLFunctions.HTGeometry.GoldenRuleSincIntegral

/-!
# The golden-rule kernel

First-order time-dependent perturbation theory produces the amplitude

```text
∫₀ᵗ exp (i s x) ds
```

for a transition with energy mismatch `x` after time `t`.  Its squared modulus is the *golden-rule
kernel*

```text
K t x = 4 sin (x t / 2)² / x²  =  t² sinc (x t / 2)² .
```

Writing it through `Real.sinc` makes it continuous at the resonant point `x = 0`, where it takes the
value `t²`.  This file collects everything the golden-rule limit consumes:

* the exact identification with the squared amplitude, `goldenRuleKernel_eq_normSq`;
* the two elementary bounds `K ≤ t²` and `K ≤ 4/x²`, and the single integrable majorant
  `K t x ≤ (t² + 4)/(1 + x²)` they combine into;
* the total mass `∫_ℝ K t = 2 π t`, which is the sinc-square normalization.
-/

open MeasureTheory Set intervalIntegral

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The golden-rule kernel `K t x = 4 sin(x t/2)²/x²`, written through `Real.sinc` so that it is
continuous at the resonance `x = 0`, where its value is `t²`. -/
def goldenRuleKernel (t x : ℝ) : ℝ := t ^ (2 : ℕ) * Real.sinc (x * t / 2) ^ (2 : ℕ)

@[simp] theorem goldenRuleKernel_zero_arg (t : ℝ) : goldenRuleKernel t 0 = t ^ (2 : ℕ) := by
  simp [goldenRuleKernel]

theorem goldenRuleKernel_nonneg (t x : ℝ) : 0 ≤ goldenRuleKernel t x := by
  unfold goldenRuleKernel; positivity

/-- Away from the resonance the kernel is the classical `4 sin²/x²`. -/
theorem goldenRuleKernel_eq {x : ℝ} (t : ℝ) (hx : x ≠ 0) :
    goldenRuleKernel t x = 4 * Real.sin (x * t / 2) ^ (2 : ℕ) / x ^ (2 : ℕ) := by
  rcases eq_or_ne t 0 with ht | ht
  · simp [goldenRuleKernel, ht]
  · have hxt : x * t / 2 ≠ 0 := by
      intro h
      rcases mul_eq_zero.mp (by linarith [h] : x * t = 0) with h' | h'
      · exact hx h'
      · exact ht h'
    rw [goldenRuleKernel, Real.sinc_of_ne_zero hxt]
    field_simp
    ring

theorem goldenRuleKernel_le_sq (t x : ℝ) : goldenRuleKernel t x ≤ t ^ (2 : ℕ) := by
  have h : Real.sinc (x * t / 2) ^ (2 : ℕ) ≤ 1 := by
    have := Real.abs_sinc_le_one (x * t / 2)
    nlinarith [abs_nonneg (Real.sinc (x * t / 2)), sq_abs (Real.sinc (x * t / 2))]
  have ht : (0 : ℝ) ≤ t ^ (2 : ℕ) := sq_nonneg t
  calc goldenRuleKernel t x = t ^ (2 : ℕ) * Real.sinc (x * t / 2) ^ (2 : ℕ) := rfl
    _ ≤ t ^ (2 : ℕ) * 1 := by exact mul_le_mul_of_nonneg_left h ht
    _ = t ^ (2 : ℕ) := mul_one _

theorem goldenRuleKernel_le_four_div_sq {x : ℝ} (t : ℝ) (hx : x ≠ 0) :
    goldenRuleKernel t x ≤ 4 / x ^ (2 : ℕ) := by
  rw [goldenRuleKernel_eq t hx]
  have hx2 : (0 : ℝ) < x ^ (2 : ℕ) := by positivity
  rw [div_le_div_iff_of_pos_right hx2]
  nlinarith [Real.sin_sq_le_one (x * t / 2)]

/-- A single integrable majorant valid for every time. -/
theorem goldenRuleKernel_le_majorant (t x : ℝ) :
    goldenRuleKernel t x ≤ (t ^ (2 : ℕ) + 4) * (1 + x ^ (2 : ℕ))⁻¹ := by
  have hpos : (0 : ℝ) < 1 + x ^ (2 : ℕ) := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  rcases le_or_gt (x ^ (2 : ℕ) * t ^ (2 : ℕ)) 4 with hcase | hcase
  · calc goldenRuleKernel t x * (1 + x ^ (2 : ℕ)) ≤ t ^ (2 : ℕ) * (1 + x ^ (2 : ℕ)) := by
          exact mul_le_mul_of_nonneg_right (goldenRuleKernel_le_sq t x) (le_of_lt hpos)
      _ ≤ t ^ (2 : ℕ) + 4 := by nlinarith
  · have hx : x ≠ 0 := by
      intro h
      rw [h] at hcase; simp at hcase; linarith
    have hx2 : (0 : ℝ) < x ^ (2 : ℕ) := by positivity
    calc goldenRuleKernel t x * (1 + x ^ (2 : ℕ)) ≤ (4 / x ^ (2 : ℕ)) * (1 + x ^ (2 : ℕ)) := by
          exact mul_le_mul_of_nonneg_right (goldenRuleKernel_le_four_div_sq t hx) (le_of_lt hpos)
      _ ≤ t ^ (2 : ℕ) + 4 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hx2]
          nlinarith

@[fun_prop]
theorem continuous_goldenRuleKernel (t : ℝ) : Continuous (goldenRuleKernel t) := by
  unfold goldenRuleKernel
  fun_prop

theorem integrable_goldenRuleKernel (t : ℝ) :
    Integrable (goldenRuleKernel t) (volume : Measure ℝ) := by
  refine MeasureTheory.Integrable.mono'
    (((integrable_inv_one_add_sq).const_mul (t ^ (2 : ℕ) + 4)))
    (continuous_goldenRuleKernel t).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (goldenRuleKernel_nonneg t x)]
  exact goldenRuleKernel_le_majorant t x

/-- **Total mass of the golden-rule kernel.**  `∫_ℝ K t = 2 π t`. -/
theorem integral_goldenRuleKernel {t : ℝ} (ht : 0 ≤ t) :
    ∫ x : ℝ, goldenRuleKernel t x = 2 * Real.pi * t := by
  have hstep : (∫ x : ℝ, goldenRuleKernel t x)
      = ∫ x : ℝ, 4 * (Real.sin (t / 2 * x) ^ (2 : ℕ) / x ^ (2 : ℕ)) := by
    refine MeasureTheory.integral_congr_ae ?_
    have hnull : (volume : Measure ℝ) {(0 : ℝ)} = 0 := by simp
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    rw [goldenRuleKernel_eq t hx0, show x * t / 2 = t / 2 * x by ring]
    ring
  rw [hstep, MeasureTheory.integral_const_mul, integral_sin_sq_div_sq (by linarith)]
  ring

/-- **The kernel is the squared modulus of the first-order amplitude.** -/
theorem goldenRuleKernel_eq_normSq (t x : ℝ) :
    goldenRuleKernel t x
      = ‖∫ s in (0 : ℝ)..t, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)‖ ^ (2 : ℕ) := by
  rcases eq_or_ne x 0 with hx | hx
  · simp [hx]
  · have hc : (Complex.I * (x : ℂ)) ≠ 0 := by simp [Complex.I_ne_zero, hx]
    have hrw : (∫ s in (0 : ℝ)..t, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I))
        = ∫ s in (0 : ℝ)..t, Complex.exp ((Complex.I * (x : ℂ)) * (s : ℂ)) := by
      refine intervalIntegral.integral_congr ?_
      intro s _
      push_cast
      ring_nf
    rw [hrw, integral_exp_mul_complex hc]
    have e1 : (Complex.I * (x : ℂ)) * ((t : ℝ) : ℂ) = ((t * x : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [e1]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [Complex.exp_mul_I]
    have hnorm : ‖(Complex.cos ((t * x : ℝ) : ℂ) + Complex.sin ((t * x : ℝ) : ℂ) * Complex.I - 1)
        / (Complex.I * (x : ℂ))‖ ^ (2 : ℕ)
        = ‖Complex.cos ((t * x : ℝ) : ℂ) + Complex.sin ((t * x : ℝ) : ℂ) * Complex.I - 1‖ ^ (2 : ℕ)
          / ‖Complex.I * (x : ℂ)‖ ^ (2 : ℕ) := by
      rw [norm_div, div_pow]
    rw [hnorm]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hre : (((Real.cos (t * x) : ℝ) : ℂ) + ((Real.sin (t * x) : ℝ) : ℂ) * Complex.I - 1)
        = (((Real.cos (t * x) - 1 : ℝ)) : ℂ) + ((Real.sin (t * x) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hre, Complex.norm_add_mul_I]
    rw [Real.sq_sqrt (by positivity)]
    have hden : ‖Complex.I * (x : ℂ)‖ ^ (2 : ℕ) = x ^ (2 : ℕ) := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hden, goldenRuleKernel_eq t hx]
    have hsin2 : Real.sin (x * t / 2) ^ (2 : ℕ) = (1 - Real.cos (t * x)) / 2 := by
      have h2 : Real.cos (2 * (t * x / 2)) = 2 * Real.cos (t * x / 2) ^ (2 : ℕ) - 1 :=
        Real.cos_two_mul _
      have h3 : (2 : ℝ) * (t * x / 2) = t * x := by ring
      rw [h3] at h2
      have hp := Real.sin_sq_add_cos_sq (t * x / 2)
      rw [show x * t / 2 = t * x / 2 by ring]
      nlinarith [h2, hp]
    rw [hsin2]
    have hpyth := Real.sin_sq_add_cos_sq (t * x)
    field_simp
    nlinarith [hpyth]

end GaloisForLFunctions.HTGeometry
