import GaloisForLFunctions.ArithmeticPositiveDuality.SymmetricRationalZeroRelocationBohrObstruction

/-!
# The vertical trace of a rationally relocated quartet

Symmetry cancels the cubic and linear terms in centered coordinates. The
remaining numerator difference is quadratic. Its vertical coefficient is
visible after multiplication by `t²`; if that coefficient vanishes, a positive
quartic trace detects every off-line target. Ordinary mean spectra therefore
lose information that a rescaled vertical limit retains.
-/

noncomputable section
set_option autoImplicit false
open Complex Filter Topology

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- The quadratic coefficient of the numerator difference in `s−1/2`. -/
def relocationQuadraticCoefficient (ρ : ℂ) (γ₁ γ₂ : ℝ) : ℝ :=
  2 * (ρ.im ^ 2 - (ρ.re - 1 / 2) ^ 2) - γ₁ ^ 2 - γ₂ ^ 2

/-- The constant coefficient of the numerator difference in `s−1/2`. -/
def relocationQuarticCoefficient (ρ : ℂ) (γ₁ γ₂ : ℝ) : ℝ :=
  (ρ.im ^ 2 + (ρ.re - 1 / 2) ^ 2) ^ 2 - γ₁ ^ 2 * γ₂ ^ 2

/-- Reflection symmetry leaves exactly two coefficients in the numerator difference. -/
theorem zeroRelocationNum_sub_den (ρ s : ℂ) (γ₁ γ₂ : ℝ) :
    zeroRelocationNum ρ s - zeroRelocationDen γ₁ γ₂ s =
      (relocationQuadraticCoefficient ρ γ₁ γ₂ : ℂ) * (s - 1 / 2) ^ 2 +
        (relocationQuarticCoefficient ρ γ₁ γ₂ : ℂ) := by
  apply Complex.ext <;>
    norm_num [zeroRelocationNum, zeroRelocationDen, relocationQuadraticCoefficient,
      relocationQuarticCoefficient, Complex.mul_re, Complex.mul_im, pow_two] <;> ring

theorem zeroRelocationFactor_sub_one (ρ s : ℂ) (γ₁ γ₂ : ℝ)
    (hden : zeroRelocationDen γ₁ γ₂ s ≠ 0) :
    zeroRelocationFactor ρ γ₁ γ₂ s - 1 =
      ((relocationQuadraticCoefficient ρ γ₁ γ₂ : ℂ) * (s - 1 / 2) ^ 2 +
        (relocationQuarticCoefficient ρ γ₁ γ₂ : ℂ)) / zeroRelocationDen γ₁ γ₂ s := by
  rw [← zeroRelocationNum_sub_den, zeroRelocationFactor]
  field_simp [hden]

private theorem tendsto_cast_inv :
    Tendsto (fun t : ℝ => (t : ℂ)⁻¹) atTop (𝓝 0) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
  change Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) atTop (𝓝 (0 : ℂ)) at h
  simpa only [Complex.ofReal_inv] using h

private theorem tendsto_vertical_factor_div (σ : ℝ) (a : ℂ) :
    Tendsto (fun t : ℝ => (((σ : ℂ) + (t : ℂ) * I) - a) / (t : ℂ))
      atTop (𝓝 I) := by
  have h : Tendsto (fun t : ℝ => ((σ : ℂ) - a) * (t : ℂ)⁻¹ + I) atTop (𝓝 I) := by
    simpa only [mul_zero, zero_add] using
      (tendsto_cast_inv.const_mul ((σ : ℂ) - a)).add_const I
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  change ((σ : ℂ) - a) * (t : ℂ)⁻¹ + I = (((σ : ℂ) + (t : ℂ) * I) - a) / (t : ℂ)
  field_simp [htC]
  ring

private theorem tendsto_vertical_den_div_four (γ₁ γ₂ σ : ℝ) :
    Tendsto (fun t : ℝ => zeroRelocationDen γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I) / (t : ℂ) ^ 4)
      atTop (𝓝 1) := by
  have h := ((tendsto_vertical_factor_div σ (1 / 2 + I * γ₁)).mul
      (tendsto_vertical_factor_div σ (1 / 2 - I * γ₁))).mul
    ((tendsto_vertical_factor_div σ (1 / 2 + I * γ₂)).mul
      (tendsto_vertical_factor_div σ (1 / 2 - I * γ₂)))
  have hI : I * I * (I * I) = 1 := by
    calc I * I * (I * I) = (I ^ 2) ^ 2 := by ring
      _ = 1 := by rw [Complex.I_sq]; norm_num
  rw [hI] at h
  convert h using 1
  funext t
  simp only [zeroRelocationDen, div_mul_div_comm]
  congr 1 <;> ring

/-- The first visible vertical trace is independent of the abscissa. -/
theorem tendsto_quadratic_vertical_relocation_error (ρ : ℂ) (γ₁ γ₂ σ : ℝ) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ 2 *
      (zeroRelocationFactor ρ γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I) - 1))
      atTop (𝓝 (-(relocationQuadraticCoefficient ρ γ₁ γ₂ : ℂ))) := by
  have hz := tendsto_vertical_factor_div σ (1 / 2)
  have hd := tendsto_vertical_den_div_four γ₁ γ₂ σ
  have hn := ((hz.pow 2).const_mul (relocationQuadraticCoefficient ρ γ₁ γ₂ : ℂ)).add
    ((tendsto_cast_inv.pow 2).const_mul (relocationQuarticCoefficient ρ γ₁ γ₂ : ℂ))
  have h := hn.div hd one_ne_zero
  simp only [Complex.I_sq, mul_neg_one, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, add_zero, div_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), hd.eventually_ne one_ne_zero] with t ht hdT
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hden : zeroRelocationDen γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro hzero
    exact hdT (by rw [hzero, zero_div])
  change ((relocationQuadraticCoefficient ρ γ₁ γ₂ : ℂ) *
        ((((σ : ℂ) + (t : ℂ) * I) - 1 / 2) / (t : ℂ)) ^ 2 +
      (relocationQuarticCoefficient ρ γ₁ γ₂ : ℂ) * ((t : ℂ)⁻¹) ^ 2) /
      (zeroRelocationDen γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I) / (t : ℂ) ^ 4) =
    (t : ℂ) ^ 2 * (zeroRelocationFactor ρ γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I) - 1)
  rw [zeroRelocationFactor_sub_one ρ _ γ₁ γ₂ hden]
  field_simp [htC, hden]

/-- If the quadratic trace cancels, the constant numerator is the quartic trace. -/
theorem tendsto_quartic_vertical_relocation_error (ρ : ℂ) (γ₁ γ₂ σ : ℝ)
    (hquad : relocationQuadraticCoefficient ρ γ₁ γ₂ = 0) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ 4 *
      (zeroRelocationFactor ρ γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I) - 1))
      atTop (𝓝 (relocationQuarticCoefficient ρ γ₁ γ₂ : ℂ)) := by
  have hd := tendsto_vertical_den_div_four γ₁ γ₂ σ
  have h : Tendsto (fun t : ℝ => (relocationQuarticCoefficient ρ γ₁ γ₂ : ℂ) /
      (zeroRelocationDen γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I) / (t : ℂ) ^ 4))
      atTop (𝓝 (relocationQuarticCoefficient ρ γ₁ γ₂ : ℂ)) := by
    have hc : Tendsto (fun _ : ℝ => (relocationQuarticCoefficient ρ γ₁ γ₂ : ℂ))
        atTop (𝓝 (relocationQuarticCoefficient ρ γ₁ γ₂ : ℂ)) := tendsto_const_nhds
    have hdiv := hc.div hd one_ne_zero
    change Tendsto (fun t : ℝ => (relocationQuarticCoefficient ρ γ₁ γ₂ : ℂ) /
      (zeroRelocationDen γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I) / (t : ℂ) ^ 4))
        atTop (𝓝 ((relocationQuarticCoefficient ρ γ₁ γ₂ : ℂ) / 1)) at hdiv
    simpa only [div_one] using hdiv
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), hd.eventually_ne one_ne_zero] with t ht hdT
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hden : zeroRelocationDen γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro hzero
    exact hdT (by rw [hzero, zero_div])
  change (relocationQuarticCoefficient ρ γ₁ γ₂ : ℂ) /
      (zeroRelocationDen γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I) / (t : ℂ) ^ 4) =
    (t : ℂ) ^ 4 * (zeroRelocationFactor ρ γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I) - 1)
  rw [zeroRelocationFactor_sub_one ρ _ γ₁ γ₂ hden, hquad,
    Complex.ofReal_zero, zero_mul, zero_add]
  field_simp [htC, hden]

/-- After cancellation, the quartic trace is an explicit sum of nonnegative terms. -/
theorem quarticCoefficient_eq_of_quadratic_zero (ρ : ℂ) (γ₁ γ₂ : ℝ)
    (hquad : relocationQuadraticCoefficient ρ γ₁ γ₂ = 0) :
    relocationQuarticCoefficient ρ γ₁ γ₂ =
      4 * (ρ.re - 1 / 2) ^ 4 +
        2 * (ρ.re - 1 / 2) ^ 2 * (γ₁ ^ 2 + γ₂ ^ 2) +
          (γ₁ ^ 2 - γ₂ ^ 2) ^ 2 / 4 := by
  have hy : ρ.im ^ 2 = (ρ.re - 1 / 2) ^ 2 + (γ₁ ^ 2 + γ₂ ^ 2) / 2 := by
    unfold relocationQuadraticCoefficient at hquad
    linarith only [hquad]
  unfold relocationQuarticCoefficient
  rw [hy]
  ring

/-- Cancelling the quadratic trace forces a positive quartic trace of at least `4δ⁴`. -/
theorem quarticCoefficient_ge_of_quadratic_zero (ρ : ℂ) (γ₁ γ₂ : ℝ)
    (hquad : relocationQuadraticCoefficient ρ γ₁ γ₂ = 0) :
    4 * (ρ.re - 1 / 2) ^ 4 ≤ relocationQuarticCoefficient ρ γ₁ γ₂ := by
  rw [quarticCoefficient_eq_of_quadratic_zero ρ γ₁ γ₂ hquad]
  have h₁ : 0 ≤ 2 * (ρ.re - 1 / 2) ^ 2 * (γ₁ ^ 2 + γ₂ ^ 2) := by positivity
  have h₂ : 0 ≤ (γ₁ ^ 2 - γ₂ ^ 2) ^ 2 / 4 := by positivity
  linarith only [h₁, h₂]

theorem quarticCoefficient_pos_of_quadratic_zero {ρ : ℂ} (hρ : ρ.re ≠ 1 / 2)
    (γ₁ γ₂ : ℝ) (hquad : relocationQuadraticCoefficient ρ γ₁ γ₂ = 0) :
    0 < relocationQuarticCoefficient ρ γ₁ γ₂ := by
  have hd : (ρ.re - 1 / 2) ^ 4 > 0 := by
    have hδ : ρ.re - 1 / 2 ≠ 0 := sub_ne_zero.mpr hρ
    have h₄ : (ρ.re - 1 / 2) ^ 4 ≠ 0 := pow_ne_zero 4 hδ
    exact lt_of_le_of_ne (by positivity) h₄.symm
  exact (mul_pos (by norm_num : (0 : ℝ) < 4) hd).trans_le
    (quarticCoefficient_ge_of_quadratic_zero ρ γ₁ γ₂ hquad)

/-- An off-line quartet is detected by a nonzero quadratic trace or a positive quartic trace. -/
theorem zeroRelocation_has_nonzero_vertical_trace {ρ : ℂ} (hρ : ρ.re ≠ 1 / 2)
    (γ₁ γ₂ σ : ℝ) :
    (relocationQuadraticCoefficient ρ γ₁ γ₂ ≠ 0 ∧
      Tendsto (fun t : ℝ => (t : ℂ) ^ 2 *
        (zeroRelocationFactor ρ γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I) - 1))
        atTop (𝓝 (-(relocationQuadraticCoefficient ρ γ₁ γ₂ : ℂ)))) ∨
    (0 < relocationQuarticCoefficient ρ γ₁ γ₂ ∧
      Tendsto (fun t : ℝ => (t : ℂ) ^ 4 *
        (zeroRelocationFactor ρ γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I) - 1))
        atTop (𝓝 (relocationQuarticCoefficient ρ γ₁ γ₂ : ℂ))) := by
  by_cases hquad : relocationQuadraticCoefficient ρ γ₁ γ₂ = 0
  · exact Or.inr ⟨quarticCoefficient_pos_of_quadratic_zero hρ γ₁ γ₂ hquad,
      tendsto_quartic_vertical_relocation_error ρ γ₁ γ₂ σ hquad⟩
  · exact Or.inl ⟨hquad, tendsto_quadratic_vertical_relocation_error ρ γ₁ γ₂ σ⟩

#print axioms zeroRelocationNum_sub_den
#print axioms tendsto_quadratic_vertical_relocation_error
#print axioms tendsto_quartic_vertical_relocation_error
#print axioms quarticCoefficient_eq_of_quadratic_zero
#print axioms quarticCoefficient_ge_of_quadratic_zero
#print axioms zeroRelocation_has_nonzero_vertical_trace

end GaloisForLFunctions.ArithmeticPositiveDuality
