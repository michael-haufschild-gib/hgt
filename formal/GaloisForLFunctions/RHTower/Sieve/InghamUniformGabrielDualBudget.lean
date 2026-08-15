import GaloisForLFunctions.RHTower.Sieve.InghamUniformGabrielConservativeBudget

open Complex

namespace RHTower.Sieve

noncomputable section

private noncomputable def uniformGabrielDenominator (sigma : ℝ) : ℝ :=
  3 * inghamUniformGabrielRightEdge sigma - inghamUniformGabrielCenter sigma - 1

private noncomputable def uniformGabrielSeedDenominator (sigma : ℝ) : ℝ :=
  inghamUniformGabrielRightEdge sigma + inghamUniformGabrielCenter sigma - 1

/-- Moving interior moment power in the `4/3 -> 2` Gabriel interpolation. -/
noncomputable def inghamUniformGabrielInteriorPower (sigma : ℝ) : ℝ :=
  4 * (inghamUniformGabrielRightEdge sigma - 1 / 2) /
    uniformGabrielDenominator sigma

/-- Norm exponent of the source-selected center dual datum. -/
noncomputable def inghamUniformGabrielSeedExponent (sigma : ℝ) : ℝ :=
  uniformGabrielSeedDenominator sigma /
    uniformGabrielDenominator sigma

/-- Affine analytic exponent transporting the center dual datum across the moving strip. -/
def inghamUniformGabrielDualExponent (sigma : ℝ) (z : ℂ) : ℂ :=
  (z + ((inghamUniformGabrielRightEdge sigma - 1 : ℝ) : ℂ)) /
    ((uniformGabrielSeedDenominator sigma : ℝ) : ℂ)

theorem uniformGabrielDenominator_eq (sigma : ℝ) :
    uniformGabrielDenominator sigma =
      1 + (1271 / 1000 : ℝ) * (1 - sigma) := by
  unfold uniformGabrielDenominator
  exact inghamUniformGabriel_denominator_eq sigma

theorem uniformGabrielSeedDenominator_eq (sigma : ℝ) :
    uniformGabrielSeedDenominator sigma =
      1 - (911 / 1000 : ℝ) * (1 - sigma) := by
  unfold uniformGabrielSeedDenominator inghamUniformGabrielRightEdge
    inghamUniformGabrielCenter
  ring

theorem uniformGabrielDenominator_pos
    {sigma : ℝ} (hsigma : sigma ≤ 1) :
    0 < uniformGabrielDenominator sigma := by
  rw [uniformGabrielDenominator_eq]
  positivity

theorem uniformGabrielSeedDenominator_pos
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) :
    0 < uniformGabrielSeedDenominator sigma := by
  rw [uniformGabrielSeedDenominator_eq]
  nlinarith

theorem inghamUniformGabrielInteriorPower_eq
    (sigma : ℝ) :
    inghamUniformGabrielInteriorPower sigma =
      (2 + (9 / 25 : ℝ) * (1 - sigma)) /
        (1 + (1271 / 1000 : ℝ) * (1 - sigma)) := by
  unfold inghamUniformGabrielInteriorPower
  rw [uniformGabrielDenominator_eq]
  unfold inghamUniformGabrielRightEdge
  ring

theorem four_thirds_le_inghamUniformGabrielInteriorPower
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    (4 / 3 : ℝ) ≤ inghamUniformGabrielInteriorPower sigma := by
  have hden : 0 < 1 + (1271 / 1000 : ℝ) * (1 - sigma) := by positivity
  rw [inghamUniformGabrielInteriorPower_eq sigma]
  rw [le_div_iff₀ hden]
  nlinarith

theorem inghamUniformGabrielInteriorPower_le_two
    {sigma : ℝ} (hsigma : sigma ≤ 1) :
    inghamUniformGabrielInteriorPower sigma ≤ 2 := by
  have hden : 0 < 1 + (1271 / 1000 : ℝ) * (1 - sigma) := by positivity
  rw [inghamUniformGabrielInteriorPower_eq sigma]
  rw [div_le_iff₀ hden]
  nlinarith

theorem inghamUniformGabrielSeedExponent_pos
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    0 < inghamUniformGabrielSeedExponent sigma := by
  unfold inghamUniformGabrielSeedExponent
  exact div_pos
    (uniformGabrielSeedDenominator_pos hsigma0)
    (uniformGabrielDenominator_pos hsigma1)

theorem inghamUniformGabrielInteriorPower_eq_one_add_seedExponent
    {sigma : ℝ} (hsigma1 : sigma ≤ 1) :
    inghamUniformGabrielInteriorPower sigma =
      1 + inghamUniformGabrielSeedExponent sigma := by
  have hD := (uniformGabrielDenominator_pos hsigma1).ne'
  unfold inghamUniformGabrielInteriorPower
    inghamUniformGabrielSeedExponent
  field_simp [hD]
  unfold uniformGabrielDenominator uniformGabrielSeedDenominator
  ring

@[simp] theorem inghamUniformGabrielDualExponent_re (sigma : ℝ) (z : ℂ) :
    (inghamUniformGabrielDualExponent sigma z).re =
      (z.re + (inghamUniformGabrielRightEdge sigma - 1)) /
        uniformGabrielSeedDenominator sigma := by
  simp [inghamUniformGabrielDualExponent]

@[simp] theorem inghamUniformGabrielDualExponent_center
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) :
    inghamUniformGabrielDualExponent sigma
        (inghamUniformGabrielCenter sigma : ℂ) = 1 := by
  have hS := (uniformGabrielSeedDenominator_pos hsigma0).ne'
  have hnum :
      (inghamUniformGabrielCenter sigma : ℂ) +
          ((inghamUniformGabrielRightEdge sigma - 1 : ℝ) : ℂ) =
        (uniformGabrielSeedDenominator sigma : ℂ) := by
    unfold uniformGabrielSeedDenominator
    push_cast
    ring
  unfold inghamUniformGabrielDualExponent
  rw [hnum, div_self (Complex.ofReal_ne_zero.mpr hS)]

theorem inghamUniformGabrielDualExponent_re_left
    {sigma : ℝ} {z : ℂ} (hz : z.re = 1 / 2) :
    (inghamUniformGabrielDualExponent sigma z).re =
      (inghamUniformGabrielRightEdge sigma - 1 / 2) /
        uniformGabrielSeedDenominator sigma := by
  rw [inghamUniformGabrielDualExponent_re, hz]
  ring

theorem inghamUniformGabrielDualExponent_re_right
    {sigma : ℝ} {z : ℂ}
    (hz : z.re = inghamUniformGabrielRightEdge sigma) :
    (inghamUniformGabrielDualExponent sigma z).re =
      2 * (inghamUniformGabrielRightEdge sigma - 1 / 2) /
        uniformGabrielSeedDenominator sigma := by
  rw [inghamUniformGabrielDualExponent_re, hz]
  congr 1
  ring

theorem inghamUniformGabriel_seed_left_identity
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    4 * inghamUniformGabrielSeedExponent sigma *
        ((inghamUniformGabrielRightEdge sigma - 1 / 2) /
          uniformGabrielSeedDenominator sigma) =
      inghamUniformGabrielInteriorPower sigma := by
  have hD := (uniformGabrielDenominator_pos hsigma1).ne'
  have hS := (uniformGabrielSeedDenominator_pos hsigma0).ne'
  unfold inghamUniformGabrielSeedExponent
    inghamUniformGabrielInteriorPower
  field_simp [hD, hS]

theorem inghamUniformGabriel_seed_right_identity
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    2 * inghamUniformGabrielSeedExponent sigma *
        (2 * (inghamUniformGabrielRightEdge sigma - 1 / 2) /
          uniformGabrielSeedDenominator sigma) =
      inghamUniformGabrielInteriorPower sigma := by
  rw [show 2 * inghamUniformGabrielSeedExponent sigma *
      (2 * (inghamUniformGabrielRightEdge sigma - 1 / 2) /
        uniformGabrielSeedDenominator sigma) =
      4 * inghamUniformGabrielSeedExponent sigma *
        ((inghamUniformGabrielRightEdge sigma - 1 / 2) /
          uniformGabrielSeedDenominator sigma) by ring]
  exact inghamUniformGabriel_seed_left_identity hsigma0 hsigma1

end

end RHTower.Sieve
