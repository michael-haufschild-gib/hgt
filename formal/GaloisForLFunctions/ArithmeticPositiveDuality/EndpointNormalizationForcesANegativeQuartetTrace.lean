import GaloisForLFunctions.ArithmeticPositiveDuality.TheVerticalTraceOfZeroRelocation

/-!
# Endpoint normalization fixes the sign of a single-quartet trace

If a symmetric quartet multiplier is one at `s=1`, its quadratic trace is
nonpositive. Equality forces the target onto the critical line and both donor
heights to coincide with its height up to sign. Every off-line move therefore
has a negative endpoint derivative and a nonzero quadratic vertical trace.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- The normalized endpoint defect splits into square terms and the quadratic trace. -/
theorem quartet_endpoint_trace_identity (ρ : ℂ) (γ₁ γ₂ : ℝ) :
    let A := relocationQuadraticCoefficient ρ γ₁ γ₂
    4 * (relocationQuarticCoefficient ρ γ₁ γ₂ + A / 4) =
      A ^ 2 + A * (8 * (ρ.re - 1 / 2) ^ 2 + 2 * (γ₁ ^ 2 + γ₂ ^ 2) + 1) +
        16 * (ρ.re - 1 / 2) ^ 4 + 8 * (ρ.re - 1 / 2) ^ 2 * (γ₁ ^ 2 + γ₂ ^ 2) +
          (γ₁ ^ 2 - γ₂ ^ 2) ^ 2 := by
  dsimp only
  unfold relocationQuadraticCoefficient relocationQuarticCoefficient
  ring

theorem quartet_quartic_eq_of_endpoint {ρ : ℂ} {γ₁ γ₂ : ℝ}
    (hR : zeroRelocationFactor ρ γ₁ γ₂ 1 = 1) :
    relocationQuarticCoefficient ρ γ₁ γ₂ = -relocationQuadraticCoefficient ρ γ₁ γ₂ / 4 := by
  have hd := zeroRelocationDen_ne_zero_of_re_ne_half γ₁ γ₂ (s := 1) (by norm_num)
  have hn := congrArg (fun z : ℂ => z * zeroRelocationDen γ₁ γ₂ 1) hR
  dsimp only [zeroRelocationFactor] at hn
  field_simp [hd] at hn
  have he := zeroRelocationNum_sub_den ρ 1 γ₁ γ₂
  rw [hn, sub_self] at he
  have hre := congrArg Complex.re he
  norm_num at hre
  linarith only [hre]

/-- Every endpoint-normalized single-quartet multiplier has nonpositive quadratic trace. -/
theorem quartet_quadratic_nonpos_of_endpoint {ρ : ℂ} {γ₁ γ₂ : ℝ}
    (hR : zeroRelocationFactor ρ γ₁ γ₂ 1 = 1) :
    relocationQuadraticCoefficient ρ γ₁ γ₂ ≤ 0 := by
  by_contra hnot
  have hA : 0 < relocationQuadraticCoefficient ρ γ₁ γ₂ := lt_of_not_ge hnot
  have hid := quartet_endpoint_trace_identity ρ γ₁ γ₂
  dsimp only at hid
  rw [quartet_quartic_eq_of_endpoint hR] at hid
  have hp : 0 < relocationQuadraticCoefficient ρ γ₁ γ₂ *
      (8 * (ρ.re - 1 / 2) ^ 2 + 2 * (γ₁ ^ 2 + γ₂ ^ 2) + 1) := mul_pos hA (by positivity)
  have hr : 0 ≤ 16 * (ρ.re - 1 / 2) ^ 4 +
      8 * (ρ.re - 1 / 2) ^ 2 * (γ₁ ^ 2 + γ₂ ^ 2) + (γ₁ ^ 2 - γ₂ ^ 2) ^ 2 := by positivity
  nlinarith only [hid, hp, hr, sq_nonneg (relocationQuadraticCoefficient ρ γ₁ γ₂)]

/-- Zero quadratic trace is possible only when all four factors collapse to the same line pair. -/
theorem quartet_quadratic_eq_zero_iff_of_endpoint {ρ : ℂ} {γ₁ γ₂ : ℝ}
    (hR : zeroRelocationFactor ρ γ₁ γ₂ 1 = 1) :
    relocationQuadraticCoefficient ρ γ₁ γ₂ = 0 ↔
      ρ.re = 1 / 2 ∧ γ₁ ^ 2 = ρ.im ^ 2 ∧ γ₂ ^ 2 = ρ.im ^ 2 := by
  constructor
  · intro hA
    have hB := quartet_quartic_eq_of_endpoint hR
    rw [hA, neg_zero, zero_div] at hB
    have hρ : ρ.re = 1 / 2 := by
      by_contra hn
      have hp := quarticCoefficient_pos_of_quadratic_zero hn γ₁ γ₂ hA
      linarith only [hB, hp]
    have hy : ρ.im ^ 2 = (γ₁ ^ 2 + γ₂ ^ 2) / 2 := by
      unfold relocationQuadraticCoefficient at hA
      rw [hρ] at hA
      norm_num at hA
      linarith only [hA]
    have hprod : (ρ.im ^ 2) ^ 2 = γ₁ ^ 2 * γ₂ ^ 2 := by
      unfold relocationQuarticCoefficient at hB
      rw [hρ] at hB
      norm_num at hB
      linarith only [hB]
    rw [hy] at hprod
    have hsq : (γ₁ ^ 2 - γ₂ ^ 2) ^ 2 = 0 := by nlinarith only [hprod]
    have hsame : γ₁ ^ 2 = γ₂ ^ 2 := sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
    exact ⟨hρ, by linarith only [hy, hsame], by linarith only [hy, hsame]⟩
  · rintro ⟨hρ, h₁, h₂⟩
    unfold relocationQuadraticCoefficient
    rw [hρ, h₁, h₂]
    ring

/-- Off-line endpoint-normalized quartets have strictly negative quadratic trace. -/
theorem quartet_quadratic_neg_of_endpoint {ρ : ℂ} {γ₁ γ₂ : ℝ}
    (hρ : ρ.re ≠ 1 / 2) (hR : zeroRelocationFactor ρ γ₁ γ₂ 1 = 1) :
    relocationQuadraticCoefficient ρ γ₁ γ₂ < 0 := by
  have hn := quartet_quadratic_nonpos_of_endpoint hR
  by_contra hnot
  have he := le_antisymm hn (le_of_not_gt hnot)
  exact hρ ((quartet_quadratic_eq_zero_iff_of_endpoint hR).mp he).1

/-- Normalization reduces the quartic difference to `A s(s-1)`. -/
theorem quartet_polynomial_of_endpoint {ρ : ℂ} {γ₁ γ₂ : ℝ}
    (hR : zeroRelocationFactor ρ γ₁ γ₂ 1 = 1) (s : ℂ) :
    zeroRelocationNum ρ s - zeroRelocationDen γ₁ γ₂ s =
      (relocationQuadraticCoefficient ρ γ₁ γ₂ : ℂ) * s * (s - 1) := by
  rw [zeroRelocationNum_sub_den, quartet_quartic_eq_of_endpoint hR]
  push_cast
  ring

theorem quartet_deriv_one_of_endpoint {ρ : ℂ} {γ₁ γ₂ : ℝ}
    (hR : zeroRelocationFactor ρ γ₁ γ₂ 1 = 1) :
    deriv (zeroRelocationFactor ρ γ₁ γ₂) 1 =
      (relocationQuadraticCoefficient ρ γ₁ γ₂ : ℂ) / zeroRelocationDen γ₁ γ₂ 1 := by
  let D : ℂ → ℂ := zeroRelocationDen γ₁ γ₂
  let c : ℂ := relocationQuadraticCoefficient ρ γ₁ γ₂
  have hd : D 1 ≠ 0 := zeroRelocationDen_ne_zero_of_re_ne_half γ₁ γ₂ (by norm_num)
  have hD : DifferentiableAt ℂ D 1 := by
    change DifferentiableAt ℂ (fun s => zeroRelocationDen γ₁ γ₂ s) 1
    unfold zeroRelocationDen
    fun_prop
  have hP : HasDerivAt (fun s : ℂ => c * s * (s - 1)) c 1 := by
    simpa [Pi.mul_def] using ((hasDerivAt_id (1 : ℂ)).const_mul c).mul
      ((hasDerivAt_id (1 : ℂ)).sub_const 1)
  have hnum : zeroRelocationNum ρ = fun s => D s + c * s * (s - 1) := by
    funext s
    have he := quartet_polynomial_of_endpoint hR s
    dsimp only [D, c]
    linear_combination he
  have h := ((hD.hasDerivAt.add hP).div hD.hasDerivAt hd).deriv
  change deriv (fun s => (D s + c * s * (s - 1)) / D s) 1 =
    ((deriv D 1 + c) * D 1 - (D 1 + c * 1 * (1 - 1)) * deriv D 1) / (D 1) ^ 2 at h
  change deriv (fun s => zeroRelocationNum ρ s / D s) 1 = c / D 1
  rw [hnum, h]
  field_simp [hd]
  ring

/-- A genuine off-line single-quartet move cannot preserve both endpoint value and derivative. -/
theorem quartet_deriv_one_neg_of_endpoint {ρ : ℂ} {γ₁ γ₂ : ℝ}
    (hρ : ρ.re ≠ 1 / 2) (hR : zeroRelocationFactor ρ γ₁ γ₂ 1 = 1) :
    (deriv (zeroRelocationFactor ρ γ₁ γ₂) 1).re < 0 := by
  rw [quartet_deriv_one_of_endpoint hR]
  have hd : zeroRelocationDen γ₁ γ₂ 1 =
      (((γ₁ ^ 2 + 1 / 4) * (γ₂ ^ 2 + 1 / 4) : ℝ) : ℂ) := by
    apply Complex.ext <;>
      norm_num [zeroRelocationDen, pow_two, Complex.mul_re, Complex.mul_im] <;> ring
  rw [hd, ← Complex.ofReal_div, Complex.ofReal_re]
  exact div_neg_of_neg_of_pos (quartet_quadratic_neg_of_endpoint hρ hR) (by positivity)

/-- Endpoint normalization forces a positive rescaled vertical defect for every off-line move. -/
theorem quartet_positive_vertical_trace_of_endpoint {ρ : ℂ} {γ₁ γ₂ : ℝ}
    (hρ : ρ.re ≠ 1 / 2) (hR : zeroRelocationFactor ρ γ₁ γ₂ 1 = 1) (σ : ℝ) :
    ∃ a : ℝ, 0 < a ∧ Tendsto (fun t : ℝ => (t : ℂ) ^ 2 *
      (zeroRelocationFactor ρ γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I) - 1)) atTop (𝓝 (a : ℂ)) := by
  refine ⟨-relocationQuadraticCoefficient ρ γ₁ γ₂,
    neg_pos.mpr (quartet_quadratic_neg_of_endpoint hρ hR), ?_⟩
  simpa only [Complex.ofReal_neg] using tendsto_quadratic_vertical_relocation_error ρ γ₁ γ₂ σ

#print axioms quartet_quadratic_eq_zero_iff_of_endpoint
#print axioms quartet_deriv_one_neg_of_endpoint
#print axioms quartet_positive_vertical_trace_of_endpoint

end GaloisForLFunctions.ArithmeticPositiveDuality
