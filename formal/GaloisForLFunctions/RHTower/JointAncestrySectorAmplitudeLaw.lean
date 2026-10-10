import GaloisForLFunctions.RHTower.JointAncestryExactPhaseBudget

/-!
# The sector amplitude law

For radii `0 ≤ r₁, r₂ < 1` the rotated local density
`ℓ(θ) = (1 − r₁ r₂)/((1 − r₁ e^{iθ})(1 − r₂ e^{−iθ}))` has the exact amplitude profile

`|ℓ(θ)|² = ℓ(0)² / ((1 + 2 r₁ (1 − cos θ)/(1 − r₁)²) (1 + 2 r₂ (1 − cos θ)/(1 − r₂)²))`,

with peak value `ℓ(0) = (1 − r₁ r₂)/((1 − r₁)(1 − r₂))` at the Kronecker point.  For a dressed zero
`r₁ = a/t`, `r₂ = a t` (`a = p^{-σ}`, `t = p^{|δ|}`) the peak value is strictly increasing in
`t ∈ [1, 1/a)`.  So at every finite depth the largest possible sector amplitude of an off-line zero
grows with its distance from the critical line, and the decay of the amplitude away from the peak
is governed by the same radii that produce the peak.  This is the exact form of the obstruction met
when trying to isolate one zero of an infinite off-line chain: a farther zero always has the larger
peak, and isolating a zero costs amplitude at the rate at which the radii amplify it.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

variable {r₁ r₂ : ℝ}

/-- `|1 − r e^{iθ}|² = (1 − r)² + 2 r (1 − cos θ)`. -/
theorem normSq_one_sub_mul_exp (r θ : ℝ) :
    Complex.normSq (1 - (r : ℂ) * cexp ((θ : ℂ) * I)) = (1 - r) ^ 2 + 2 * r * (1 - Real.cos θ) := by
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.sub_im, Complex.one_im,
    Complex.mul_im, zero_mul, sub_zero, zero_sub]
  linear_combination r ^ 2 * Real.sin_sq_add_cos_sq θ

/-- The peak value of a rotated local density. -/
def jasPeak (r₁ r₂ : ℝ) : ℝ := (1 - r₁ * r₂) / ((1 - r₁) * (1 - r₂))

/-- **Exact amplitude profile.** -/
theorem normSq_jasRotLocal (h₁ : 0 ≤ r₁) (h₁' : r₁ < 1) (h₂ : 0 ≤ r₂) (h₂' : r₂ < 1) (θ : ℝ) :
    Complex.normSq (jasRotLocal r₁ r₂ θ) =
      jasPeak r₁ r₂ ^ 2 / ((1 + 2 * r₁ * (1 - Real.cos θ) / (1 - r₁) ^ 2) *
        (1 + 2 * r₂ * (1 - Real.cos θ) / (1 - r₂) ^ 2)) := by
  have hr₁ : 0 < 1 - r₁ := by linarith
  have hr₂ : 0 < 1 - r₂ := by linarith
  have hc : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
  unfold jasRotLocal jasPeak
  rw [Complex.normSq_div, Complex.normSq_mul, Complex.normSq_ofReal, normSq_one_sub_mul_exp,
    normSq_one_sub_mul_exp, Real.cos_neg]
  have e1 : (1 - r₁) ^ 2 + 2 * r₁ * (1 - Real.cos θ) =
      (1 - r₁) ^ 2 * (1 + 2 * r₁ * (1 - Real.cos θ) / (1 - r₁) ^ 2) := by
    field_simp
  have e2 : (1 - r₂) ^ 2 + 2 * r₂ * (1 - Real.cos θ) =
      (1 - r₂) ^ 2 * (1 + 2 * r₂ * (1 - Real.cos θ) / (1 - r₂) ^ 2) := by
    field_simp
  rw [e1, e2, div_pow]
  have hA : 0 < 1 + 2 * r₁ * (1 - Real.cos θ) / (1 - r₁) ^ 2 := by positivity
  have hB : 0 < 1 + 2 * r₂ * (1 - Real.cos θ) / (1 - r₂) ^ 2 := by positivity
  field_simp

/-- The peak is attained at the Kronecker point and bounds the amplitude everywhere. -/
theorem norm_jasRotLocal_le_peak (h₁ : 0 ≤ r₁) (h₁' : r₁ < 1) (h₂ : 0 ≤ r₂) (h₂' : r₂ < 1)
    (θ : ℝ) : ‖jasRotLocal r₁ r₂ θ‖ ≤ jasPeak r₁ r₂ := by
  have hc : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
  have hr₁ : 0 < 1 - r₁ := by linarith
  have hr₂ : 0 < 1 - r₂ := by linarith
  have hpk : 0 ≤ jasPeak r₁ r₂ := by
    unfold jasPeak; apply div_nonneg <;> nlinarith
  have hsq : ‖jasRotLocal r₁ r₂ θ‖ ^ 2 ≤ jasPeak r₁ r₂ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, normSq_jasRotLocal h₁ h₁' h₂ h₂']
    have hA : 1 ≤ 1 + 2 * r₁ * (1 - Real.cos θ) / (1 - r₁) ^ 2 := by
      have : 0 ≤ 2 * r₁ * (1 - Real.cos θ) / (1 - r₁) ^ 2 := by positivity
      linarith
    have hB : 1 ≤ 1 + 2 * r₂ * (1 - Real.cos θ) / (1 - r₂) ^ 2 := by
      have : 0 ≤ 2 * r₂ * (1 - Real.cos θ) / (1 - r₂) ^ 2 := by positivity
      linarith
    exact div_le_self (sq_nonneg _) (one_le_mul_of_one_le_of_one_le hA hB)
  nlinarith [norm_nonneg (jasRotLocal r₁ r₂ θ)]

theorem jasRotLocal_zero (r₁ r₂ : ℝ) : jasRotLocal r₁ r₂ 0 = (jasPeak r₁ r₂ : ℂ) := by
  unfold jasRotLocal jasPeak
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, neg_zero]
  push_cast
  rfl

/-! ## Farther zeros have larger peaks -/

/-- For `r₁ = a/t`, `r₂ = a t` the peak is strictly increasing in `t ∈ [1, 1/a)`. -/
theorem jasPeak_lt_of_lt {a s t : ℝ} (ha : 0 < a) (hs : 1 ≤ s) (hst : s < t) (ht : a * t < 1) :
    jasPeak (a / s) (a * s) < jasPeak (a / t) (a * t) := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have has : a * s < 1 := by nlinarith
  have hDs : 0 < (1 - a / s) * (1 - a * s) := by
    apply mul_pos
    · rw [sub_pos, div_lt_one hs0]; nlinarith
    · linarith
  have hDt : 0 < (1 - a / t) * (1 - a * t) := by
    apply mul_pos
    · rw [sub_pos, div_lt_one ht0]; nlinarith
    · linarith
  unfold jasPeak
  have hnum : a / s * (a * s) = a ^ 2 := by field_simp
  have hnum' : a / t * (a * t) = a ^ 2 := by field_simp
  rw [hnum, hnum']
  have ha2 : 0 < 1 - a ^ 2 := by nlinarith
  apply div_lt_div_of_pos_left ha2 hDt
  -- the denominator `1 − a(t + 1/t) + a²` decreases in `t ≥ 1`
  have e1 : (1 - a / s) * (1 - a * s) = 1 - a * (s + 1 / s) + a ^ 2 := by field_simp; ring
  have e2 : (1 - a / t) * (1 - a * t) = 1 - a * (t + 1 / t) + a ^ 2 := by field_simp; ring
  rw [e1, e2]
  have hmono : s + 1 / s < t + 1 / t := by
    rw [← sub_pos]
    have : t + 1 / t - (s + 1 / s) = (t - s) * (s * t - 1) / (s * t) := by field_simp; ring
    rw [this]
    apply div_pos _ (mul_pos hs0 ht0)
    apply mul_pos (by linarith)
    nlinarith
  nlinarith

end

end RHTower
