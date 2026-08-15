import GaloisForLFunctions.RHTower.Sieve.InghamFixedGabrielBudget

/-!
# A uniform subcritical Gabriel budget for Route T

The fixed Route-T Gabriel geometry cannot yield a density estimate uniform up to `sigma = 1`:
its fixed critical power loss and fixed right-edge displacement leave a strictly positive exponent
at `sigma = 1`.  This is a mathematical obstruction, not bookkeeping.

The surviving geometry scales every artificial displacement with `1 - sigma`.  Put the detector
center a distance `(1 - sigma) / 1000` left of the counting line and the right edge a distance
`9(1 - sigma) / 100` right of one.  If the critical endpoint is retained as `X * polylog X`, while
the right endpoint uses the sharp divisor-square-average saving `-2(beta - 1)`, the interpolated
height exponent is at most

`(31 / 10) * (1 - sigma)`.

Since `(31 / 10) * (1 - 7 / 10) = 93 / 100 < 1`, this coefficient is already strong enough for
Route T's fixed `7/10` density-to-short-ranges handoff.  Recovering the limiting classical
coefficient three is unnecessary.
-/

namespace RHTower.Sieve

noncomputable section

/-- Counting-dependent Gabriel center.  Its layer-cake gap is `(1 - sigma) / 1000`. -/
noncomputable def inghamUniformGabrielCenter (sigma : ℝ) : ℝ :=
  sigma - (1 - sigma) / 1000

/-- Counting-dependent right edge. -/
noncomputable def inghamUniformGabrielRightEdge (sigma : ℝ) : ℝ :=
  1 + (9 / 100 : ℝ) * (1 - sigma)

/-- Sharp right-endpoint height exponent predicted by divisor-square average rather than a
pointwise divisor bound: `-2 * (beta - 1)`. -/
noncomputable def inghamUniformGabrielRightMomentExponent (sigma : ℝ) : ℝ :=
  -(9 / 50 : ℝ) * (1 - sigma)

/-- Critical-endpoint share in the `4/3 -> 2` Gabriel interpolation. -/
noncomputable def inghamUniformGabrielCriticalShare (sigma : ℝ) : ℝ :=
  3 * (inghamUniformGabrielRightEdge sigma - inghamUniformGabrielCenter sigma) /
    (3 * inghamUniformGabrielRightEdge sigma - inghamUniformGabrielCenter sigma - 1)

/-- Right-endpoint share in the `4/3 -> 2` Gabriel interpolation. -/
noncomputable def inghamUniformGabrielRightShare (sigma : ℝ) : ℝ :=
  (2 * inghamUniformGabrielCenter sigma - 1) /
    (3 * inghamUniformGabrielRightEdge sigma - inghamUniformGabrielCenter sigma - 1)

/-- Height exponent after a sharp critical polylog bound and the scaled right-edge saving. -/
noncomputable def inghamUniformGabrielExponent (sigma : ℝ) : ℝ :=
  inghamUniformGabrielCriticalShare sigma +
    inghamUniformGabrielRightMomentExponent sigma *
      inghamUniformGabrielRightShare sigma

theorem inghamUniformGabriel_denominator_eq (sigma : ℝ) :
    3 * inghamUniformGabrielRightEdge sigma -
        inghamUniformGabrielCenter sigma - 1 =
      1 + (1271 / 1000 : ℝ) * (1 - sigma) := by
  unfold inghamUniformGabrielRightEdge inghamUniformGabrielCenter
  ring

/-- Closed form exposing the coefficient at `sigma = 1` and its favorable denominator. -/
theorem inghamUniformGabrielExponent_eq {sigma : ℝ} (hsigma : sigma ≤ 1) :
    inghamUniformGabrielExponent sigma =
      (1 - sigma) *
        ((3093 / 1000 : ℝ) + (9009 / 25000 : ℝ) * (1 - sigma)) /
          (1 + (1271 / 1000 : ℝ) * (1 - sigma)) := by
  have hdenpos :
      0 < 1 + (1271 / 1000 : ℝ) * (1 - sigma) := by positivity
  unfold inghamUniformGabrielExponent inghamUniformGabrielCriticalShare
    inghamUniformGabrielRightShare inghamUniformGabrielRightMomentExponent
  rw [inghamUniformGabriel_denominator_eq]
  field_simp [hdenpos.ne']
  unfold inghamUniformGabrielRightEdge inghamUniformGabrielCenter
  ring

/-- Uniform coefficient `31/10`, strictly below Route T's critical coefficient `10/3`. -/
theorem inghamUniformGabrielExponent_le_three_point_one_mul
    {sigma : ℝ} (hsigma : sigma ≤ 1) :
    inghamUniformGabrielExponent sigma ≤
      (31 / 10 : ℝ) * (1 - sigma) := by
  have hd : 0 ≤ 1 - sigma := sub_nonneg.mpr hsigma
  have hdenpos :
      0 < 1 + (1271 / 1000 : ℝ) * (1 - sigma) := by positivity
  rw [inghamUniformGabrielExponent_eq hsigma]
  rw [div_le_iff₀ hdenpos]
  nlinarith [sq_nonneg (1 - sigma)]

/-- Exact power room left in the `7/10` density-to-short-ranges handoff. -/
theorem inghamUniformGabriel_primeSupply_margin :
    1 - (31 / 10 : ℝ) * (1 - 7 / 10) = 7 / 100 := by
  norm_num

/-- Fixed Route-T endpoint losses leave positive height exponent at `sigma = 1`; therefore that
fixed geometry cannot be promoted to a uniform density theorem. -/
theorem fixedGabrielEndpointLoss_positive_at_one :
    0 < (251 / 250 : ℝ) *
          (3 * (inghamPowerSavingRightEdge - 1) /
            (3 * inghamPowerSavingRightEdge - 2)) +
        (-(1 / 180 : ℝ)) *
          (1 / (3 * inghamPowerSavingRightEdge - 2)) := by
  norm_num [inghamPowerSavingRightEdge]

end

end RHTower.Sieve
