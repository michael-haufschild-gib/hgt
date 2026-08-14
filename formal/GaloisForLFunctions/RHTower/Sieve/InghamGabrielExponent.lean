import GaloisForLFunctions.RHTower.Sieve.InghamCriticalMoment

/-!
# Exact exponent geometry behind Ingham--Gabriel interpolation

Gabriel interpolation uses boundary moment parameters `λ=3/4` on `α=1/2` and `μ=1/2` on a right
edge `β`.  With strip weights

`w₁=(β-σ)/(β-1/2)`, `w₂=(σ-1/2)/(β-1/2)`,

the height exponent contributed by the critical edge is `(λw₁)/(λw₁+μw₂)`.  This file proves its
closed form

`3(β-σ)/(3β-σ-1)`.

At `β=1` this is Ingham's coefficient-three exponent `3(1-σ)/(2-σ)`.  Moving the right edge to
`β=1+ε` adds exactly

`3ε(2σ-1) / ((2+3ε-σ)(2-σ))`.

At Route T's fixed `σ=7/10`, the limiting exponent is `9/13`, leaving the exact positive margin
`1/130` below `7/10`; the perturbed exponent stays below `7/10` exactly when `ε<1/90`.  Thus the
fixed short-interval exponent has genuine room for the `1/log X` right-edge displacement.
-/

namespace RHTower.Sieve

/-- Left-boundary strip weight. -/
noncomputable def inghamGabrielLeftWeight (σ β : ℝ) : ℝ :=
  (β - σ) / (β - 1 / 2)

/-- Right-boundary strip weight. -/
noncomputable def inghamGabrielRightWeight (σ β : ℝ) : ℝ :=
  (σ - 1 / 2) / (β - 1 / 2)

/-- Interpolated moment parameter for `λ=3/4`, `μ=1/2`. -/
noncomputable def inghamGabrielMomentParameter (σ β : ℝ) : ℝ :=
  (3 / 4) * inghamGabrielLeftWeight σ β +
    (1 / 2) * inghamGabrielRightWeight σ β

/-- Critical-edge height exponent after Gabriel interpolation. -/
noncomputable def inghamGabrielHeightExponent (σ β : ℝ) : ℝ :=
  ((3 / 4) * inghamGabrielLeftWeight σ β) /
    inghamGabrielMomentParameter σ β

theorem inghamGabrielMomentParameter_eq (σ β : ℝ) :
    inghamGabrielMomentParameter σ β =
      (3 * β - σ - 1) / (4 * (β - 1 / 2)) := by
  unfold inghamGabrielMomentParameter inghamGabrielLeftWeight inghamGabrielRightWeight
  by_cases h : β - 1 / 2 = 0
  · rw [h]
    simp
  · field_simp [h]
    ring

/-- Closed form of the interpolated height exponent. -/
theorem inghamGabrielHeightExponent_eq {σ β : ℝ}
    (hβhalf : β ≠ 1 / 2) :
    inghamGabrielHeightExponent σ β =
      3 * (β - σ) / (3 * β - σ - 1) := by
  have hD : β - 1 / 2 ≠ 0 := sub_ne_zero.mpr hβhalf
  have hc : 4 * (β - 1 / 2) ≠ 0 := mul_ne_zero (by norm_num) hD
  have hnum :
      (3 / 4) * inghamGabrielLeftWeight σ β =
        (3 * (β - σ)) / (4 * (β - 1 / 2)) := by
    unfold inghamGabrielLeftWeight
    field_simp [hD]
  unfold inghamGabrielHeightExponent
  rw [hnum, inghamGabrielMomentParameter_eq]
  exact div_div_div_cancel_right₀ hc _ _

/-- Ingham's limiting coefficient-three density exponent. -/
noncomputable def inghamDensityExponent (σ : ℝ) : ℝ :=
  3 * (1 - σ) / (2 - σ)

theorem inghamGabrielHeightExponent_one (σ : ℝ) :
    inghamGabrielHeightExponent σ 1 = inghamDensityExponent σ := by
  rw [inghamGabrielHeightExponent_eq (by norm_num)]
  unfold inghamDensityExponent
  ring

/-- Exact inflation caused by moving the right edge from `1` to `1+ε`. -/
theorem inghamGabrielHeightExponent_one_add (σ ε : ℝ)
    (hden0 : 2 - σ ≠ 0) (hdenε : 2 + 3 * ε - σ ≠ 0)
    (hhalf : 1 + ε ≠ 1 / 2) :
    inghamGabrielHeightExponent σ (1 + ε) =
      inghamDensityExponent σ +
        3 * ε * (2 * σ - 1) / ((2 + 3 * ε - σ) * (2 - σ)) := by
  rw [inghamGabrielHeightExponent_eq hhalf]
  rw [show 3 * (1 + ε) - σ - 1 = 2 + 3 * ε - σ by ring]
  unfold inghamDensityExponent
  field_simp [hden0, hdenε]
  ring

/-- On the critical-to-one strip, a nonnegative right-edge displacement can only increase the
height exponent. -/
theorem inghamDensityExponent_le_heightExponent_one_add
    {σ ε : ℝ} (hσhalf : 1 / 2 ≤ σ) (hσone : σ ≤ 1) (hε : 0 ≤ ε) :
    inghamDensityExponent σ ≤ inghamGabrielHeightExponent σ (1 + ε) := by
  have hden0 : 2 - σ ≠ 0 := by linarith
  have hdenεpos : 0 < 2 + 3 * ε - σ := by linarith
  have hhalf : 1 + ε ≠ 1 / 2 := by linarith
  rw [inghamGabrielHeightExponent_one_add σ ε hden0 hdenεpos.ne' hhalf]
  have hden0pos : 0 < 2 - σ := by linarith
  have hsig : 0 ≤ 2 * σ - 1 := by linarith
  have hnum : 0 ≤ 3 * ε * (2 * σ - 1) :=
    mul_nonneg (mul_nonneg (by norm_num) hε) hsig
  have hcorr : 0 ≤
      3 * ε * (2 * σ - 1) / ((2 + 3 * ε - σ) * (2 - σ)) := by
    exact div_nonneg hnum (mul_nonneg hdenεpos.le hden0pos.le)
  linarith

/-- Route T's `7/10` ordinate has limiting density exponent `9/13`. -/
theorem inghamDensityExponent_seven_tenths :
    inghamDensityExponent (7 / 10 : ℝ) = 9 / 13 := by
  unfold inghamDensityExponent
  norm_num

/-- Exact positive density margin below the fixed `7/10` short-interval exponent. -/
theorem seven_tenths_sub_inghamDensityExponent :
    (7 / 10 : ℝ) - inghamDensityExponent (7 / 10 : ℝ) = 1 / 130 := by
  rw [inghamDensityExponent_seven_tenths]
  norm_num

/-- The `β=1+ε` Gabriel exponent at `σ=7/10` remains below `7/10` precisely for
`ε<1/90` (on the nonnegative perturbation range). -/
theorem inghamGabrielHeightExponent_seven_tenths_lt_iff
    {ε : ℝ} (hε : 0 ≤ ε) :
    inghamGabrielHeightExponent (7 / 10 : ℝ) (1 + ε) < 7 / 10 ↔ ε < 1 / 90 := by
  have hhalf : 1 + ε ≠ (1 / 2 : ℝ) := by linarith
  rw [inghamGabrielHeightExponent_eq hhalf]
  have hpos : 0 < 3 * (1 + ε) - (7 / 10 : ℝ) - 1 := by linarith
  rw [div_lt_iff₀ hpos]
  constructor <;> intro h <;> linarith

end RHTower.Sieve
