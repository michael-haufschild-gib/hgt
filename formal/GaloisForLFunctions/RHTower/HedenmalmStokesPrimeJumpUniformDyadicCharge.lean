import GaloisForLFunctions.RHTower.HedenmalmStokesPrimeJumpScalingShell

/-!
# Uniform dyadic prime--Stokes charge

This strengthens `HCF-SX2` from fixed moving coordinates to a uniform closed-band estimate.  One
local bound for the explicit regular pole--Gamma--von-Mangoldt anomaly controls both sides of both
apertures.  If `2*a < δ` and `a*M < 2/25`, every `c` in `[1/2,1]` receives squared dyadic-shell
charge strictly greater than `21/100`.  The endpoints are included: their limiting shell charge is
`1/2`, rather than zero.

The statement remains source-only.  It does not sum over `XiZeroCopy`; next required weld is a
height-summed source-frame inequality against the finite HCF Plemelj/source-piece covariance.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Quantitative half-jump error at the moving aperture boundary. -/
theorem abs_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_boundary_sub_half_le
    {a M : ℝ} (ha : 0 < a) (_hM : 0 ≤ M)
    (hA : |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly (2 * a)| ≤ M) :
    |gammaSewnMobiusApertureStokesPrimeJumpProjector a a - 1 / 2| ≤
      a * M / 4 := by
  rw [gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_boundary_eq ha,
    add_sub_cancel_left, abs_div, abs_mul, abs_of_pos ha]
  norm_num
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hA ha.le) (by norm_num)

/-- In the open dyadic band, shell charge differs from one by at most `a*M/2`. -/
theorem abs_gammaSewnMobiusApertureStokesPrimeDyadicShell_scaled_interior_sub_one_le
    {δ M a c : ℝ} (hM : 0 ≤ M) (ha : 0 < a) (h2aδ : 2 * a < δ)
    (hbound : ∀ d : ℝ, 0 < d → d < δ →
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly d| ≤ M)
    (hcLower : 1 / 2 < c) (hcUpper : c < 1) :
    |gammaSewnMobiusApertureStokesPrimeDyadicShell a (c * a) - 1| ≤
      a * M / 2 := by
  have hcAbs : |c| < 1 := by
    rw [abs_of_pos (by linarith : 0 < c)]
    exact hcUpper
  have houterPlus :
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((1 + c) * a)| ≤ M := by
    apply hbound _ (mul_pos (by linarith) ha)
    exact (mul_lt_mul_of_pos_right (by linarith : 1 + c < 2) ha).trans h2aδ
  have houterMinus :
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((1 - c) * a)| ≤ M := by
    apply hbound _ (mul_pos (by linarith) ha)
    exact (mul_lt_mul_of_pos_right (by linarith : 1 - c < 2) ha).trans h2aδ
  have houter :=
    abs_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_sub_one_le
      ha hcAbs hM houterPlus houterMinus
  have hb : 0 < a / 2 := div_pos ha (by norm_num)
  have hinnerPlus :
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly
        ((2 * c + 1) * (a / 2))| ≤ M := by
    apply hbound _ (mul_pos (by linarith) hb)
    have : (2 * c + 1) * (a / 2) < 2 * a := by
      nlinarith
    exact this.trans h2aδ
  have hinnerMinus :
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly
        ((2 * c - 1) * (a / 2))| ≤ M := by
    apply hbound _ (mul_pos (by linarith) hb)
    have : (2 * c - 1) * (a / 2) < 2 * a := by
      nlinarith
    exact this.trans h2aδ
  have hinner :=
    abs_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_outside_le
      hb (show 1 < 2 * c by linarith) hM hinnerPlus hinnerMinus
  have hinner' :
      |gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) (c * a)| ≤
        a * M / 4 := by
    have hrewrite :
        gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2)
            ((2 * c) * (a / 2)) =
          gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) (c * a) := by
      congr 1
      ring
    rw [hrewrite] at hinner
    calc
      _ ≤ (2 * c) * (a / 2) * M / 4 := hinner
      _ ≤ a * M / 4 := by
        have hca : c * (a * M) ≤ 1 * (a * M) :=
          mul_le_mul_of_nonneg_right hcUpper.le (mul_nonneg ha.le hM)
        nlinarith
  have htri :
      |gammaSewnMobiusApertureStokesPrimeDyadicShell a (c * a) - 1| ≤
        |gammaSewnMobiusApertureStokesPrimeJumpProjector a (c * a) - 1| +
        |gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) (c * a)| := by
    rw [gammaSewnMobiusApertureStokesPrimeDyadicShell]
    rw [show
      gammaSewnMobiusApertureStokesPrimeJumpProjector a (c * a) -
          gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) (c * a) - 1 =
        (gammaSewnMobiusApertureStokesPrimeJumpProjector a (c * a) - 1) +
          (-gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) (c * a)) by ring]
    simpa only [abs_neg] using abs_add_le
      (gammaSewnMobiusApertureStokesPrimeJumpProjector a (c * a) - 1)
      (-gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) (c * a))
  exact htri.trans <| (add_le_add houter hinner').trans_eq (by ring)

/-- Inner band endpoint has half-charge with the same coarse `a*M/2` error. -/
theorem abs_gammaSewnMobiusApertureStokesPrimeDyadicShell_scaled_lowerBoundary_sub_half_le
    {δ M a : ℝ} (hM : 0 ≤ M) (ha : 0 < a) (h2aδ : 2 * a < δ)
    (hbound : ∀ d : ℝ, 0 < d → d < δ →
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly d| ≤ M) :
    |gammaSewnMobiusApertureStokesPrimeDyadicShell a (a / 2) - 1 / 2| ≤
      a * M / 2 := by
  have houterPlus := hbound ((1 + (1 / 2 : ℝ)) * a)
    (mul_pos (by norm_num) ha)
    ((mul_lt_mul_of_pos_right (by norm_num : (1 + (1 / 2 : ℝ)) < 2) ha).trans h2aδ)
  have houterMinus := hbound ((1 - (1 / 2 : ℝ)) * a)
    (mul_pos (by norm_num) ha)
    ((mul_lt_mul_of_pos_right (by norm_num : (1 - (1 / 2 : ℝ)) < 2) ha).trans h2aδ)
  have houter :=
    abs_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_sub_one_le
      ha (by norm_num : |(1 / 2 : ℝ)| < 1) hM houterPlus houterMinus
  have hb : 0 < a / 2 := div_pos ha (by norm_num)
  have hinnerA :
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly (2 * (a / 2))| ≤ M := by
    apply hbound _ (by nlinarith)
    nlinarith
  have hinner :=
    abs_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_boundary_sub_half_le
      hb hM hinnerA
  have htri :
      |gammaSewnMobiusApertureStokesPrimeDyadicShell a (a / 2) - 1 / 2| ≤
        |gammaSewnMobiusApertureStokesPrimeJumpProjector a (a / 2) - 1| +
        |gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) (a / 2) - 1 / 2| := by
    rw [gammaSewnMobiusApertureStokesPrimeDyadicShell]
    rw [show
      gammaSewnMobiusApertureStokesPrimeJumpProjector a (a / 2) -
          gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) (a / 2) - 1 / 2 =
        (gammaSewnMobiusApertureStokesPrimeJumpProjector a (a / 2) - 1) -
          (gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) (a / 2) - 1 / 2) by ring]
    rw [sub_eq_add_neg]
    simpa only [abs_neg] using abs_add_le
      (gammaSewnMobiusApertureStokesPrimeJumpProjector a (a / 2) - 1)
      (-(gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) (a / 2) - 1 / 2))
  have houter' :
      |gammaSewnMobiusApertureStokesPrimeJumpProjector a (a / 2) - 1| ≤
        a * M / 4 := by
    convert houter using 1 <;> ring
  calc
    _ ≤ _ := htri
    _ ≤ a * M / 4 + (a / 2) * M / 4 := add_le_add houter' hinner
    _ ≤ a * M / 2 := by
      have haM : 0 ≤ a * M := mul_nonneg ha.le hM
      nlinarith

/-- Outer band endpoint has half-charge with error `a*M/2`. -/
theorem abs_gammaSewnMobiusApertureStokesPrimeDyadicShell_scaled_upperBoundary_sub_half_le
    {δ M a : ℝ} (hM : 0 ≤ M) (ha : 0 < a) (h2aδ : 2 * a < δ)
    (hbound : ∀ d : ℝ, 0 < d → d < δ →
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly d| ≤ M) :
    |gammaSewnMobiusApertureStokesPrimeDyadicShell a a - 1 / 2| ≤
      a * M / 2 := by
  have houterA := hbound (2 * a) (by positivity) h2aδ
  have houter :=
    abs_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_boundary_sub_half_le
      ha hM houterA
  have hb : 0 < a / 2 := div_pos ha (by norm_num)
  have hinnerPlus := hbound ((2 + 1 : ℝ) * (a / 2))
    (mul_pos (by norm_num) hb) (by nlinarith)
  have hinnerMinus := hbound ((2 - 1 : ℝ) * (a / 2))
    (mul_pos (by norm_num) hb) (by nlinarith)
  have hinner :=
    abs_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_outside_le
      hb (by norm_num : (1 : ℝ) < 2) hM hinnerPlus hinnerMinus
  have hinner' :
      |gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) a| ≤
        a * M / 4 := by
    convert hinner using 1 <;> ring
  have htri :
      |gammaSewnMobiusApertureStokesPrimeDyadicShell a a - 1 / 2| ≤
        |gammaSewnMobiusApertureStokesPrimeJumpProjector a a - 1 / 2| +
        |gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) a| := by
    rw [gammaSewnMobiusApertureStokesPrimeDyadicShell]
    rw [show
      gammaSewnMobiusApertureStokesPrimeJumpProjector a a -
          gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) a - 1 / 2 =
        (gammaSewnMobiusApertureStokesPrimeJumpProjector a a - 1 / 2) +
          (-gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) a) by ring]
    simpa only [abs_neg] using abs_add_le
      (gammaSewnMobiusApertureStokesPrimeJumpProjector a a - 1 / 2)
      (-gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) a)
  exact htri.trans <| (add_le_add houter hinner').trans_eq (by ring)

/-- **Uniform closed-band quantum.**  One source anomaly bound gives squared shell charge
strictly above `21/100` at every coordinate `c` in the closed dyadic band. -/
theorem twentyOneHundred_lt_sq_gammaSewnMobiusApertureStokesPrimeDyadicShell_of_small
    {δ M a c : ℝ} (hM : 0 ≤ M) (ha : 0 < a) (h2aδ : 2 * a < δ)
    (haM : a * M < 2 / 25)
    (hbound : ∀ d : ℝ, 0 < d → d < δ →
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly d| ≤ M)
    (hcLower : 1 / 2 ≤ c) (hcUpper : c ≤ 1) :
    (21 / 100 : ℝ) <
      gammaSewnMobiusApertureStokesPrimeDyadicShell a (c * a) ^ 2 := by
  let shell := gammaSewnMobiusApertureStokesPrimeDyadicShell a (c * a)
  have square_of_half_error (herror : |shell - 1 / 2| ≤ a * M / 2) :
      (21 / 100 : ℝ) < shell ^ 2 := by
    have hshell : (23 / 50 : ℝ) < shell := by
      have hlower := (abs_le.mp herror).1
      nlinarith
    have hprod : 0 < (shell - 23 / 50) * (shell + 23 / 50) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  by_cases hcLowerEq : c = 1 / 2
  · subst c
    apply square_of_half_error
    dsimp only [shell]
    convert
      abs_gammaSewnMobiusApertureStokesPrimeDyadicShell_scaled_lowerBoundary_sub_half_le
        hM ha h2aδ hbound using 1 <;> ring
  by_cases hcUpperEq : c = 1
  · subst c
    apply square_of_half_error
    simpa only [one_mul, shell] using
      abs_gammaSewnMobiusApertureStokesPrimeDyadicShell_scaled_upperBoundary_sub_half_le
        hM ha h2aδ hbound
  · have herror :=
      abs_gammaSewnMobiusApertureStokesPrimeDyadicShell_scaled_interior_sub_one_le
        hM ha h2aδ hbound
        (lt_of_le_of_ne hcLower (Ne.symm hcLowerEq))
        (lt_of_le_of_ne hcUpper hcUpperEq)
    have hshell : (24 / 25 : ℝ) < shell := by
      have hlower := (abs_le.mp herror).1
      dsimp only [shell]
      nlinarith
    have hprod : 0 < (shell - 24 / 25) * (shell + 24 / 25) :=
      mul_pos (by linarith) (by linarith)
    nlinarith

end

end RHTower
