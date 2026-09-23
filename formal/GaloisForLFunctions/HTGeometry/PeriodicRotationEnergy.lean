import Mathlib

/-!
# Rotation energy of a periodic function

For a continuous `L`-periodic function the energy over one period is unchanged by a rotation, and
subtracting a rotated multiple changes the energy by at most the expected factor:

`(1-c)² ∫₀ᴸ‖F‖² ≤ ∫₀ᴸ‖F - c F(·+M)‖² ≤ (1+c)² ∫₀ᴸ‖F‖²`.

Both bounds are the triangle and reverse-triangle inequalities squared pointwise, integrated, and
combined with the arithmetic-geometric bound on the cross term; no inner product or Cauchy--Schwarz
is needed.

* `intervalIntegral_normSq_rotate` : **rotation preserves the energy over one period.**
* `intervalIntegral_normSq_sub_rotate_le` : **the upper bound.**
* `le_intervalIntegral_normSq_sub_rotate` : **the lower bound.**
-/

namespace GaloisForLFunctions

open MeasureTheory

variable {F : ℝ → ℂ} {L M c : ℝ}

/-- The energy integrand is interval integrable. -/
theorem intervalIntegrable_normSq (G : ℝ → ℂ) (b : ℝ) (hG : Continuous G) :
    IntervalIntegrable (fun t : ℝ => ‖G t‖ ^ (2 : ℕ)) volume 0 b :=
  Continuous.intervalIntegrable (by fun_prop) 0 b

/-- The rotated energy integrand is interval integrable. -/
theorem intervalIntegrable_normSq_rotate (G : ℝ → ℂ) (a b : ℝ) (hG : Continuous G) :
    IntervalIntegrable (fun t : ℝ => ‖G (t + a)‖ ^ (2 : ℕ)) volume 0 b :=
  Continuous.intervalIntegrable (by fun_prop) 0 b

/-- The cross integrand is interval integrable. -/
theorem intervalIntegrable_norm_mul_rotate (G : ℝ → ℂ) (a b : ℝ) (hG : Continuous G) :
    IntervalIntegrable (fun t : ℝ => ‖G t‖ * ‖G (t + a)‖) volume 0 b :=
  Continuous.intervalIntegrable (by fun_prop) 0 b

/-- **Rotation preserves the energy over one period.** -/
theorem intervalIntegral_normSq_rotate (hF : Continuous F) (hL : 0 < L)
    (hper : Function.Periodic F L) (M : ℝ) :
    (∫ t in (0 : ℝ)..L, ‖F (t + M)‖ ^ (2 : ℕ)) = ∫ t in (0 : ℝ)..L, ‖F t‖ ^ (2 : ℕ) := by
  have hperSq : Function.Periodic (fun t : ℝ => ‖F t‖ ^ (2 : ℕ)) L := by
    intro s
    show ‖F (s + L)‖ ^ (2 : ℕ) = ‖F s‖ ^ (2 : ℕ)
    rw [hper s]
  have hcomp : (∫ t in (0 : ℝ)..L, ‖F (t + M)‖ ^ (2 : ℕ))
      = ∫ t in (0 + M)..(L + M), ‖F t‖ ^ (2 : ℕ) :=
    intervalIntegral.integral_comp_add_right (fun t => ‖F t‖ ^ (2 : ℕ)) M
  rw [hcomp]
  have hrange : (∫ t in M..(M + L), ‖F t‖ ^ (2 : ℕ)) = ∫ t in (0 : ℝ)..(0 + L), ‖F t‖ ^ (2 : ℕ) :=
    hperSq.intervalIntegral_add_eq M 0
  have h1 : (0 : ℝ) + M = M := by ring
  have h2 : L + M = M + L := by ring
  rw [h1, h2, hrange, zero_add]

/-- The cross term is bounded by the energy. -/
theorem intervalIntegral_norm_mul_rotate_le (hF : Continuous F) (hL : 0 < L)
    (hper : Function.Periodic F L) (M : ℝ) :
    (∫ t in (0 : ℝ)..L, ‖F t‖ * ‖F (t + M)‖) ≤ ∫ t in (0 : ℝ)..L, ‖F t‖ ^ (2 : ℕ) := by
  have hi1 := intervalIntegrable_normSq F L hF
  have hi2 := intervalIntegrable_normSq_rotate F M L hF
  have hi3 := intervalIntegrable_norm_mul_rotate F M L hF
  have havg : IntervalIntegrable
      (fun t : ℝ => (‖F t‖ ^ (2 : ℕ) + ‖F (t + M)‖ ^ (2 : ℕ)) / 2) volume 0 L :=
    Continuous.intervalIntegrable (by fun_prop) 0 L
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) L,
      ‖F t‖ * ‖F (t + M)‖ ≤ (‖F t‖ ^ (2 : ℕ) + ‖F (t + M)‖ ^ (2 : ℕ)) / 2 := by
    intro t _
    nlinarith [sq_nonneg (‖F t‖ - ‖F (t + M)‖)]
  have hmono := intervalIntegral.integral_mono_on hL.le hi3 havg hpt
  refine hmono.trans (le_of_eq ?_)
  have hsplit : (∫ t in (0 : ℝ)..L, (‖F t‖ ^ (2 : ℕ) + ‖F (t + M)‖ ^ (2 : ℕ)) / 2)
      = ((∫ t in (0 : ℝ)..L, ‖F t‖ ^ (2 : ℕ)) + ∫ t in (0 : ℝ)..L, ‖F (t + M)‖ ^ (2 : ℕ)) / 2 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add hi1 hi2]
  rw [hsplit, intervalIntegral_normSq_rotate hF hL hper M]
  ring

/-- **The upper bound.** -/
theorem intervalIntegral_normSq_sub_rotate_le (hF : Continuous F) (hL : 0 < L)
    (hper : Function.Periodic F L) (M : ℝ) (hc : 0 ≤ c) :
    (∫ t in (0 : ℝ)..L, ‖F t - (c : ℂ) * F (t + M)‖ ^ (2 : ℕ))
      ≤ (1 + c) ^ (2 : ℕ) * ∫ t in (0 : ℝ)..L, ‖F t‖ ^ (2 : ℕ) := by
  have hi1 := intervalIntegrable_normSq F L hF
  have hi2 := intervalIntegrable_normSq_rotate F M L hF
  have hi3 := intervalIntegrable_norm_mul_rotate F M L hF
  have hiL : IntervalIntegrable
      (fun t : ℝ => ‖F t - (c : ℂ) * F (t + M)‖ ^ (2 : ℕ)) volume 0 L :=
    Continuous.intervalIntegrable (by fun_prop) 0 L
  have hiR : IntervalIntegrable
      (fun t : ℝ => ‖F t‖ ^ (2 : ℕ) + 2 * c * (‖F t‖ * ‖F (t + M)‖)
        + c ^ (2 : ℕ) * ‖F (t + M)‖ ^ (2 : ℕ)) volume 0 L :=
    Continuous.intervalIntegrable (by fun_prop) 0 L
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) L,
      ‖F t - (c : ℂ) * F (t + M)‖ ^ (2 : ℕ)
        ≤ ‖F t‖ ^ (2 : ℕ) + 2 * c * (‖F t‖ * ‖F (t + M)‖) + c ^ (2 : ℕ) * ‖F (t + M)‖ ^ (2 : ℕ) := by
    intro t _
    have htri : ‖F t - (c : ℂ) * F (t + M)‖ ≤ ‖F t‖ + c * ‖F (t + M)‖ := by
      refine (norm_sub_le _ _).trans (le_of_eq ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
    have hnn : (0 : ℝ) ≤ ‖F t‖ + c * ‖F (t + M)‖ := by positivity
    nlinarith [norm_nonneg (F t - (c : ℂ) * F (t + M))]
  have hmono := intervalIntegral.integral_mono_on hL.le hiL hiR hpt
  refine hmono.trans ?_
  have hsplit : (∫ t in (0 : ℝ)..L,
      (‖F t‖ ^ (2 : ℕ) + 2 * c * (‖F t‖ * ‖F (t + M)‖) + c ^ (2 : ℕ) * ‖F (t + M)‖ ^ (2 : ℕ)))
      = (∫ t in (0 : ℝ)..L, ‖F t‖ ^ (2 : ℕ))
        + 2 * c * (∫ t in (0 : ℝ)..L, ‖F t‖ * ‖F (t + M)‖)
        + c ^ (2 : ℕ) * ∫ t in (0 : ℝ)..L, ‖F (t + M)‖ ^ (2 : ℕ) := by
    rw [intervalIntegral.integral_add (hi1.add (hi3.const_mul (2 * c))) (hi2.const_mul (c ^ (2 : ℕ))),
      intervalIntegral.integral_add hi1 (hi3.const_mul (2 * c)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hsplit, intervalIntegral_normSq_rotate hF hL hper M]
  have hcross := intervalIntegral_norm_mul_rotate_le hF hL hper M
  nlinarith [hcross]

/-- **The lower bound.** -/
theorem le_intervalIntegral_normSq_sub_rotate (hF : Continuous F) (hL : 0 < L)
    (hper : Function.Periodic F L) (M : ℝ) (hc : 0 ≤ c) :
    (1 - c) ^ (2 : ℕ) * (∫ t in (0 : ℝ)..L, ‖F t‖ ^ (2 : ℕ))
      ≤ ∫ t in (0 : ℝ)..L, ‖F t - (c : ℂ) * F (t + M)‖ ^ (2 : ℕ) := by
  have hi1 := intervalIntegrable_normSq F L hF
  have hi2 := intervalIntegrable_normSq_rotate F M L hF
  have hi3 := intervalIntegrable_norm_mul_rotate F M L hF
  have hiR : IntervalIntegrable
      (fun t : ℝ => ‖F t - (c : ℂ) * F (t + M)‖ ^ (2 : ℕ)) volume 0 L :=
    Continuous.intervalIntegrable (by fun_prop) 0 L
  have hiL : IntervalIntegrable
      (fun t : ℝ => ‖F t‖ ^ (2 : ℕ) - 2 * c * (‖F t‖ * ‖F (t + M)‖)
        + c ^ (2 : ℕ) * ‖F (t + M)‖ ^ (2 : ℕ)) volume 0 L :=
    Continuous.intervalIntegrable (by fun_prop) 0 L
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) L,
      ‖F t‖ ^ (2 : ℕ) - 2 * c * (‖F t‖ * ‖F (t + M)‖) + c ^ (2 : ℕ) * ‖F (t + M)‖ ^ (2 : ℕ)
        ≤ ‖F t - (c : ℂ) * F (t + M)‖ ^ (2 : ℕ) := by
    intro t _
    have hrev : |‖F t‖ - c * ‖F (t + M)‖| ≤ ‖F t - (c : ℂ) * F (t + M)‖ := by
      have h := abs_norm_sub_norm_le (F t) ((c : ℂ) * F (t + M))
      rwa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc] at h
    have hb := abs_le.1 hrev
    nlinarith [hb.1, hb.2, norm_nonneg (F t - (c : ℂ) * F (t + M))]
  have hmono := intervalIntegral.integral_mono_on hL.le hiL hiR hpt
  refine le_trans ?_ hmono
  have hsplit : (∫ t in (0 : ℝ)..L,
      (‖F t‖ ^ (2 : ℕ) - 2 * c * (‖F t‖ * ‖F (t + M)‖) + c ^ (2 : ℕ) * ‖F (t + M)‖ ^ (2 : ℕ)))
      = (∫ t in (0 : ℝ)..L, ‖F t‖ ^ (2 : ℕ))
        - 2 * c * (∫ t in (0 : ℝ)..L, ‖F t‖ * ‖F (t + M)‖)
        + c ^ (2 : ℕ) * ∫ t in (0 : ℝ)..L, ‖F (t + M)‖ ^ (2 : ℕ) := by
    rw [intervalIntegral.integral_add (hi1.sub (hi3.const_mul (2 * c))) (hi2.const_mul (c ^ (2 : ℕ))),
      intervalIntegral.integral_sub hi1 (hi3.const_mul (2 * c)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hsplit, intervalIntegral_normSq_rotate hF hL hper M]
  have hcross := intervalIntegral_norm_mul_rotate_le hF hL hper M
  nlinarith [hcross, hc]

end GaloisForLFunctions
