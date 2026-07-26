/-
# Quantitative scale choice in Bourgain's Section 1 bootstrap

The normalized Taylor theorem gives the explicit smallness requirement

`50331648000 * R / K^(3/2) ≤ 1/24`.

Bourgain writes this as `R = o(K^(3/2))`.  We retain every constant and
choose

`K = (24 * 50331648000)^(2/3) * R^(2/3)`.

The fixed dilation is handled by
`BourgainDilatedPowerScaleSubpower`.
-/
import GaloisForLFunctions.RHTower.BourgainDilatedPowerScaleSubpower

namespace RHTower

noncomputable section

/-- Explicit Taylor constant in the normalized Section 1 cap estimate. -/
def bourgainSectionOneTaylorConstant : ℝ := 50331648000

/-- Fixed dilation accompanying the `R^(2/3)` bootstrap scale. -/
def bourgainSectionOneScaleDilation : ℝ :=
  (24 * bourgainSectionOneTaylorConstant) ^ (2 / 3 : ℝ)

/-- Bourgain's quantitative recurrence scale. -/
def bourgainSectionOneRecurrenceScale (R : ℝ) : ℝ :=
  bourgainSectionOneScaleDilation * R ^ (2 / 3 : ℝ)

theorem bourgainSectionOneTaylorConstant_pos :
    0 < bourgainSectionOneTaylorConstant := by
  norm_num [bourgainSectionOneTaylorConstant]

theorem bourgainSectionOneScaleDilation_one_le :
    1 ≤ bourgainSectionOneScaleDilation := by
  unfold bourgainSectionOneScaleDilation
  apply Real.one_le_rpow
  · norm_num [bourgainSectionOneTaylorConstant]
  · norm_num

theorem bourgainSectionOneRecurrenceScale_pos
    {R : ℝ} (hR : 0 < R) :
    0 < bourgainSectionOneRecurrenceScale R := by
  unfold bourgainSectionOneRecurrenceScale
  exact mul_pos
    (lt_of_lt_of_le zero_lt_one
      bourgainSectionOneScaleDilation_one_le)
    (Real.rpow_pos_of_pos hR _)

/-- The explicit `R^(2/3)` scale saturates the normalized cubic Taylor
smallness condition exactly. -/
theorem bourgainSectionOneRecurrenceScale_threeHalves
    {R : ℝ} (hR : 0 < R) :
    bourgainSectionOneRecurrenceScale R ^ (3 / 2 : ℝ) =
      (24 * bourgainSectionOneTaylorConstant) * R := by
  let Q : ℝ := 24 * bourgainSectionOneTaylorConstant
  have hQ : 0 < Q := by
    dsimp [Q]
    exact mul_pos (by norm_num) bourgainSectionOneTaylorConstant_pos
  have hroot (x : ℝ) (hx : 0 < x) :
      (x ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) = x := by
    rw [← Real.rpow_mul hx.le]
    norm_num
  unfold bourgainSectionOneRecurrenceScale
    bourgainSectionOneScaleDilation
  change
    (Q ^ (2 / 3 : ℝ) * R ^ (2 / 3 : ℝ)) ^
        (3 / 2 : ℝ) =
      Q * R
  rw [Real.mul_rpow
    (Real.rpow_nonneg hQ.le _) (Real.rpow_nonneg hR.le _),
    hroot Q hQ, hroot R hR]

/-- Exact quantitative replacement for Bourgain's
`R = o(K^(3/2))` in (1.22). -/
theorem bourgainSectionOneRecurrenceScale_taylor_small
    {R : ℝ} (hR : 0 < R) :
    bourgainSectionOneTaylorConstant * R /
        bourgainSectionOneRecurrenceScale R ^ (3 / 2 : ℝ) =
      1 / 24 := by
  rw [bourgainSectionOneRecurrenceScale_threeHalves hR]
  have hC := bourgainSectionOneTaylorConstant_pos
  field_simp

/-- Integer-cap form consumed by the normalized exact-curve theorem. -/
theorem bourgainNormalizedQuadraticCap_small
    {H : ℕ} {D : ℝ} (hD : 0 < D)
    (hcap :
      24 * bourgainSectionOneTaylorConstant *
          (H : ℝ) ^ (3 : ℕ) ≤ D) :
    bourgainSectionOneTaylorConstant *
        (H : ℝ) ^ (3 : ℕ) / D ≤ 1 / 24 := by
  apply (div_le_iff₀ hD).2
  nlinarith [hcap]

end

end RHTower
