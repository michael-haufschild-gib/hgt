import GaloisForLFunctions.RHTower.Sieve.InghamUniformGabrielBudget

/-!
# Conservative uniform Gabriel budget after polylog critical closure

The pointwise divisor estimate on a right edge `beta = 1 + delta` supplies the weaker moment
saving `-delta`, rather than the divisor-square-average saving `-2 delta`.  Once the critical
endpoint has exact height exponent one with only polylogarithmic loss, this weaker saving still
closes Route T uniformly with coefficient `16/5 < 10/3`.
-/

namespace RHTower.Sieve

noncomputable section

/-- Conservative right-endpoint exponent supplied by the existing pointwise divisor bound. -/
noncomputable def inghamUniformGabrielConservativeRightMomentExponent
    (sigma : ℝ) : ℝ :=
  -(9 / 100 : ℝ) * (1 - sigma)

/-- Uniform center exponent using only pointwise divisor control on the moving right edge. -/
noncomputable def inghamUniformGabrielConservativeExponent (sigma : ℝ) : ℝ :=
  inghamUniformGabrielCriticalShare sigma +
    inghamUniformGabrielConservativeRightMomentExponent sigma *
      inghamUniformGabrielRightShare sigma

theorem inghamUniformGabrielConservativeExponent_eq
    {sigma : ℝ} (hsigma : sigma ≤ 1) :
    inghamUniformGabrielConservativeExponent sigma =
      (1 - sigma) *
        ((3183 / 1000 : ℝ) + (9009 / 50000 : ℝ) * (1 - sigma)) /
          (1 + (1271 / 1000 : ℝ) * (1 - sigma)) := by
  have hdenpos :
      0 < 1 + (1271 / 1000 : ℝ) * (1 - sigma) := by positivity
  unfold inghamUniformGabrielConservativeExponent
    inghamUniformGabrielConservativeRightMomentExponent
    inghamUniformGabrielCriticalShare inghamUniformGabrielRightShare
  rw [inghamUniformGabriel_denominator_eq]
  field_simp [hdenpos.ne']
  unfold inghamUniformGabrielRightEdge inghamUniformGabrielCenter
  ring

/-- The weaker pointwise-divisor budget remains uniformly below coefficient `16/5`. -/
theorem inghamUniformGabrielConservativeExponent_le_sixteen_fifths_mul
    {sigma : ℝ} (hsigma : sigma ≤ 1) :
    inghamUniformGabrielConservativeExponent sigma ≤
      (16 / 5 : ℝ) * (1 - sigma) := by
  have hd : 0 ≤ 1 - sigma := sub_nonneg.mpr hsigma
  have hdenpos :
      0 < 1 + (1271 / 1000 : ℝ) * (1 - sigma) := by positivity
  rw [inghamUniformGabrielConservativeExponent_eq hsigma]
  rw [div_le_iff₀ hdenpos]
  nlinarith [sq_nonneg (1 - sigma)]

/-- At the Route-T counting line, the conservative density exponent remains below height one. -/
theorem inghamUniformGabrielConservative_primeSupply_height_margin :
    1 - (16 / 5 : ℝ) * (1 - 7 / 10) = 1 / 25 := by
  norm_num

/-- Equivalent density-to-short-ranges exponent room at `theta = 7/10`. -/
theorem inghamUniformGabrielConservative_shortInterval_margin :
    (7 / 10 : ℝ) - (1 - 1 / (16 / 5 : ℝ)) = 1 / 80 := by
  norm_num

end


end RHTower.Sieve
