import GaloisForLFunctions.ArithmeticPositiveDuality.TheVerticalTraceOfZeroRelocation

/-!
# A quartet relocation preserving both real endpoints

Two critical-line pairs can be replaced by a quartet on the lines `1/4` and
`3/4` while the rational multiplier retains value one at zero and one.
The difference of the two monic quartics is exactly `c s(s-1)`, with `c<0`.
-/

noncomputable section
set_option autoImplicit false

open Complex

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- The ordinate of the normalized quartet on `Re s=1/4,3/4`. -/
def normalizedRelocationHeight (γ₁ γ₂ : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt ((γ₁ ^ 2 + 1 / 4) * (γ₂ ^ 2 + 1 / 4) + 1 / 16) - 5 / 16)

def normalizedRelocationTarget (γ₁ γ₂ : ℝ) : ℂ :=
  3 / 4 + (normalizedRelocationHeight γ₁ γ₂ : ℂ) * I

@[simp] theorem normalizedRelocationTarget_re (γ₁ γ₂ : ℝ) :
    (normalizedRelocationTarget γ₁ γ₂).re = 3 / 4 := by
  norm_num [normalizedRelocationTarget]

@[simp] theorem normalizedRelocationTarget_im (γ₁ γ₂ : ℝ) :
    (normalizedRelocationTarget γ₁ γ₂).im = normalizedRelocationHeight γ₁ γ₂ := by
  norm_num [normalizedRelocationTarget]

/-- The prescribed off-line target is an exact zero of the rational multiplier. -/
theorem normalizedRelocation_target_zero (γ₁ γ₂ : ℝ) :
    zeroRelocationFactor (normalizedRelocationTarget γ₁ γ₂) γ₁ γ₂
      (normalizedRelocationTarget γ₁ γ₂) = 0 := by
  simp only [zeroRelocationFactor, zeroRelocationNum, sub_self, zero_mul, zero_div]

/-- The quadratic trace of the normalized rational multiplier. -/
def normalizedRelocationTrace (γ₁ γ₂ : ℝ) : ℝ :=
  2 * normalizedRelocationHeight γ₁ γ₂ ^ 2 - 1 / 8 - γ₁ ^ 2 - γ₂ ^ 2

private theorem inner_height_gt {γ₁ γ₂ : ℝ} (hγ₁ : 1 < γ₁) (hγ₂ : 1 < γ₂) :
    5 / 16 < Real.sqrt ((γ₁ ^ 2 + 1 / 4) * (γ₂ ^ 2 + 1 / 4) + 1 / 16) := by
  have h₁ : 1 < γ₁ ^ 2 := by nlinarith only [hγ₁]
  have h₂ : 1 < γ₂ ^ 2 := by nlinarith only [hγ₂]
  have hp : (5 / 4 : ℝ) * (5 / 4) ≤ (γ₁ ^ 2 + 1 / 4) * (γ₂ ^ 2 + 1 / 4) :=
    mul_le_mul (by linarith only [h₁]) (by linarith only [h₂])
      (by norm_num) (by positivity)
  have hD : 0 ≤ (γ₁ ^ 2 + 1 / 4) * (γ₂ ^ 2 + 1 / 4) + 1 / 16 := by positivity
  have hh := Real.sq_sqrt hD
  by_contra h
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_of_not_gt h) 2
  nlinarith only [hp, hh, hsq]

theorem normalizedRelocationHeight_pos {γ₁ γ₂ : ℝ}
    (hγ₁ : 1 < γ₁) (hγ₂ : 1 < γ₂) : 0 < normalizedRelocationHeight γ₁ γ₂ := by
  exact Real.sqrt_pos.mpr (sub_pos.mpr (inner_height_gt hγ₁ hγ₂))

theorem normalizedRelocationHeight_sq {γ₁ γ₂ : ℝ}
    (hγ₁ : 1 < γ₁) (hγ₂ : 1 < γ₂) :
    normalizedRelocationHeight γ₁ γ₂ ^ 2 =
      Real.sqrt ((γ₁ ^ 2 + 1 / 4) * (γ₂ ^ 2 + 1 / 4) + 1 / 16) - 5 / 16 :=
  Real.sq_sqrt (sub_nonneg.mpr (inner_height_gt hγ₁ hγ₂).le)

/-- Preserving the pole residue while moving to `Re s=3/4` forces a negative trace. -/
theorem normalizedRelocationTrace_neg {γ₁ γ₂ : ℝ}
    (hγ₁ : 1 < γ₁) (hγ₂ : 1 < γ₂) : normalizedRelocationTrace γ₁ γ₂ < 0 := by
  let h := Real.sqrt ((γ₁ ^ 2 + 1 / 4) * (γ₂ ^ 2 + 1 / 4) + 1 / 16)
  have hh : h ^ 2 = (γ₁ ^ 2 + 1 / 4) * (γ₂ ^ 2 + 1 / 4) + 1 / 16 :=
    Real.sq_sqrt (by positivity)
  have hp : 0 < γ₁ ^ 2 + γ₂ ^ 2 + 3 / 4 := by positivity
  have hgap : (2 * h) ^ 2 < (γ₁ ^ 2 + γ₂ ^ 2 + 3 / 4) ^ 2 := by
    nlinarith only [hh, sq_nonneg (γ₁ ^ 2 - γ₂ ^ 2), sq_nonneg γ₁, sq_nonneg γ₂]
  have hlt : 2 * h < γ₁ ^ 2 + γ₂ ^ 2 + 3 / 4 := by
    by_contra hnot
    have hsq := pow_le_pow_left₀ hp.le (le_of_not_gt hnot) 2
    exact (not_lt_of_ge hsq) hgap
  rw [normalizedRelocationTrace, normalizedRelocationHeight_sq hγ₁ hγ₂]
  change 2 * (h - 5 / 16) - 1 / 8 - γ₁ ^ 2 - γ₂ ^ 2 < 0
  linarith only [hlt]

theorem normalizedRelocation_quadratic (γ₁ γ₂ : ℝ) :
    relocationQuadraticCoefficient (normalizedRelocationTarget γ₁ γ₂) γ₁ γ₂ =
      normalizedRelocationTrace γ₁ γ₂ := by
  norm_num [relocationQuadraticCoefficient, normalizedRelocationTarget, normalizedRelocationTrace]
  ring

theorem normalizedRelocation_quartic {γ₁ γ₂ : ℝ}
    (hγ₁ : 1 < γ₁) (hγ₂ : 1 < γ₂) :
    relocationQuarticCoefficient (normalizedRelocationTarget γ₁ γ₂) γ₁ γ₂ =
      -normalizedRelocationTrace γ₁ γ₂ / 4 := by
  have hh : (Real.sqrt ((γ₁ ^ 2 + 1 / 4) * (γ₂ ^ 2 + 1 / 4) + 1 / 16)) ^ 2 =
      (γ₁ ^ 2 + 1 / 4) * (γ₂ ^ 2 + 1 / 4) + 1 / 16 := Real.sq_sqrt (by positivity)
  norm_num [relocationQuarticCoefficient, normalizedRelocationTarget, normalizedRelocationTrace]
  rw [normalizedRelocationHeight_sq hγ₁ hγ₂]
  nlinarith only [hh]

/-- The exact quartic difference simultaneously fixes the values at zero and one. -/
theorem normalizedRelocation_polynomial {γ₁ γ₂ : ℝ}
    (hγ₁ : 1 < γ₁) (hγ₂ : 1 < γ₂) (s : ℂ) :
    zeroRelocationNum (normalizedRelocationTarget γ₁ γ₂) s - zeroRelocationDen γ₁ γ₂ s =
      (normalizedRelocationTrace γ₁ γ₂ : ℂ) * s * (s - 1) := by
  rw [zeroRelocationNum_sub_den, normalizedRelocation_quadratic,
    normalizedRelocation_quartic hγ₁ hγ₂]
  push_cast
  ring

/-- Both real endpoint values are exactly preserved. -/
theorem normalizedRelocation_endpoints {γ₁ γ₂ : ℝ}
    (hγ₁ : 1 < γ₁) (hγ₂ : 1 < γ₂) :
    zeroRelocationFactor (normalizedRelocationTarget γ₁ γ₂) γ₁ γ₂ 0 = 1 ∧
      zeroRelocationFactor (normalizedRelocationTarget γ₁ γ₂) γ₁ γ₂ 1 = 1 := by
  constructor
  · have he := normalizedRelocation_polynomial hγ₁ hγ₂ 0
    simp only [mul_zero, zero_mul, sub_eq_zero] at he
    rw [zeroRelocationFactor, he]
    exact div_self (zeroRelocationDen_ne_zero_of_re_ne_half γ₁ γ₂ (by norm_num))
  · have he := normalizedRelocation_polynomial hγ₁ hγ₂ 1
    simp only [sub_self, mul_zero, sub_eq_zero] at he
    rw [zeroRelocationFactor, he]
    exact div_self (zeroRelocationDen_ne_zero_of_re_ne_half γ₁ γ₂ (by norm_num))

/-- Away from the donor line the multiplier is the normalized rational correction. -/
theorem normalizedRelocation_factor_eq {γ₁ γ₂ : ℝ}
    (hγ₁ : 1 < γ₁) (hγ₂ : 1 < γ₂) {s : ℂ} (hs : s.re ≠ 1 / 2) :
    zeroRelocationFactor (normalizedRelocationTarget γ₁ γ₂) γ₁ γ₂ s =
      1 + (normalizedRelocationTrace γ₁ γ₂ : ℂ) * s * (s - 1) /
        zeroRelocationDen γ₁ γ₂ s := by
  have hd := zeroRelocationDen_ne_zero_of_re_ne_half γ₁ γ₂ hs
  have he := normalizedRelocation_polynomial hγ₁ hγ₂ s
  rw [zeroRelocationFactor]
  apply (div_eq_iff hd).mpr
  field_simp [hd]
  linear_combination he

/-- The endpoint derivative records the same strictly negative quadratic trace. -/
theorem normalizedRelocation_deriv_one {γ₁ γ₂ : ℝ}
    (hγ₁ : 1 < γ₁) (hγ₂ : 1 < γ₂) :
    deriv (zeroRelocationFactor (normalizedRelocationTarget γ₁ γ₂) γ₁ γ₂) 1 =
      (normalizedRelocationTrace γ₁ γ₂ : ℂ) / zeroRelocationDen γ₁ γ₂ 1 := by
  let D : ℂ → ℂ := zeroRelocationDen γ₁ γ₂
  let c : ℂ := normalizedRelocationTrace γ₁ γ₂
  have hd : D 1 ≠ 0 := zeroRelocationDen_ne_zero_of_re_ne_half γ₁ γ₂ (by norm_num)
  have hD : DifferentiableAt ℂ D 1 := by
    change DifferentiableAt ℂ (fun s => zeroRelocationDen γ₁ γ₂ s) 1
    unfold zeroRelocationDen
    fun_prop
  have hP : HasDerivAt (fun s : ℂ => c * s * (s - 1)) c 1 := by
    simpa [Pi.mul_def] using ((hasDerivAt_id (1 : ℂ)).const_mul c).mul
      ((hasDerivAt_id (1 : ℂ)).sub_const 1)
  have hnum : zeroRelocationNum (normalizedRelocationTarget γ₁ γ₂) =
      fun s => D s + c * s * (s - 1) := by
    funext s
    have he := normalizedRelocation_polynomial hγ₁ hγ₂ s
    dsimp only [D, c]
    linear_combination he
  have h := ((hD.hasDerivAt.add hP).div hD.hasDerivAt hd).deriv
  change deriv (fun s => (D s + c * s * (s - 1)) / D s) 1 =
    ((deriv D 1 + c) * D 1 - (D 1 + c * 1 * (1 - 1)) * deriv D 1) / (D 1) ^ 2 at h
  change deriv (fun s => zeroRelocationNum (normalizedRelocationTarget γ₁ γ₂) s / D s) 1 = c / D 1
  rw [hnum, h]
  field_simp [hd]
  ring

/-- A normalized single-quartet move cannot also preserve the first derivative at one. -/
theorem normalizedRelocation_deriv_one_neg {γ₁ γ₂ : ℝ}
    (hγ₁ : 1 < γ₁) (hγ₂ : 1 < γ₂) :
    (deriv (zeroRelocationFactor (normalizedRelocationTarget γ₁ γ₂) γ₁ γ₂) 1).re < 0 := by
  rw [normalizedRelocation_deriv_one hγ₁ hγ₂]
  have hd : zeroRelocationDen γ₁ γ₂ 1 =
      (((γ₁ ^ 2 + 1 / 4) * (γ₂ ^ 2 + 1 / 4) : ℝ) : ℂ) := by
    apply Complex.ext <;>
      norm_num [zeroRelocationDen, pow_two, Complex.mul_re, Complex.mul_im] <;> ring
  rw [hd, ← Complex.ofReal_div, Complex.ofReal_re]
  exact div_neg_of_neg_of_pos (normalizedRelocationTrace_neg hγ₁ hγ₂) (by positivity)

#print axioms normalizedRelocation_polynomial
#print axioms normalizedRelocationTrace_neg
#print axioms normalizedRelocation_endpoints
#print axioms normalizedRelocation_deriv_one_neg

end GaloisForLFunctions.ArithmeticPositiveDuality
