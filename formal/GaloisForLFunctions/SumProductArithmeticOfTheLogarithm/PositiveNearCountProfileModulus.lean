import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCountExactAverage
import GaloisForLFunctions.HTGeometry.ExponentialDividedDifference
import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCountProfile

/-!
# Explicit continuity bounds for the positive count profile

Squared midpoint rounding is one-half Lipschitz. Truncating the geometric
profile after `J` corrections leaves a nonnegative error at most
`1 / (12 * 4^J * x)`. On a fixed scale interval, each retained correction
has a bounded Lipschitz constant, giving a modulus linear in `J` plus a
geometric tail.

Period-four normalization transfers this estimate to the entire logarithmic
line. A displacement of size `log 4 / Q` changes the logarithmic profile by
at most `(16 log Q + 64 log 4 + 4/3) / Q`, uniformly in its starting point.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCount

/-- Squared midpoint-rounding distance has Lipschitz constant one half. -/
theorem midpointRounding_lipschitz (X Y : ℝ) :
    |midpointRounding X - midpointRounding Y| ≤ |X - Y| / 2 := by
  let u := ‖((X / 2 : ℝ) : UnitAddCircle)‖
  let v := ‖((Y / 2 : ℝ) : UnitAddCircle)‖
  have hu0 : 0 ≤ u := norm_nonneg _
  have hv0 : 0 ≤ v := norm_nonneg _
  have hu : u ≤ 1 / 2 := by
    simpa only [abs_one] using AddCircle.norm_le_half_period (1 : ℝ)
      (x := ((X / 2 : ℝ) : UnitAddCircle)) (by norm_num)
  have hv : v ≤ 1 / 2 := by
    simpa only [abs_one] using AddCircle.norm_le_half_period (1 : ℝ)
      (x := ((Y / 2 : ℝ) : UnitAddCircle)) (by norm_num)
  have hd : |u - v| ≤ |X - Y| / 2 := by
    apply (abs_norm_sub_norm_le (((X / 2 : ℝ) : UnitAddCircle))
      (((Y / 2 : ℝ) : UnitAddCircle))).trans
    rw [← AddCircle.coe_sub]
    calc
      _ ≤ ‖X / 2 - Y / 2‖ := QuotientAddGroup.norm_mk_le_norm
      _ = _ := by rw [← sub_div, Real.norm_eq_abs, abs_div]; norm_num
  change |u ^ 2 - v ^ 2| ≤ _
  calc
    _ = |u - v| * (u + v) := by
      rw [show u ^ 2 - v ^ 2 = (u - v) * (u + v) by ring,
        abs_mul, abs_of_nonneg (add_nonneg hu0 hv0)]
    _ ≤ |u - v| := by
      have h := mul_le_mul_of_nonneg_left (show u + v ≤ 1 by linarith only [hu, hv])
        (abs_nonneg (u - v))
      simpa only [mul_one] using h
    _ ≤ _ := hd

/-- Finite midpoint corrections to the normalized norm-four deficit. -/
def profilePartial (J : ℕ) (X : ℝ) : ℝ :=
  fourDeficit X / X + ∑ j ∈ Finset.range J,
    midpointRounding ((4 : ℝ) ^ (j + 1) * X) / ((4 : ℝ) ^ (j + 1) * X)

private theorem normalized_fourDeficit_step {X : ℝ} (hX : 0 < X) :
    fourDeficit (4 * X) / (4 * X) =
      fourDeficit X / X + midpointRounding (4 * X) / (4 * X) := by
  rw [fourDeficit_four]
  field_simp

theorem profilePartial_eq {X : ℝ} (hX : 0 < X) (J : ℕ) :
    profilePartial J X = fourDeficit ((4 : ℝ) ^ J * X) / ((4 : ℝ) ^ J * X) := by
  induction J with
  | zero => simp only [profilePartial, Finset.range_zero, Finset.sum_empty, add_zero, pow_zero, one_mul]
  | succ J ih =>
    rw [profilePartial, Finset.sum_range_succ, ← add_assoc]
    change profilePartial J X + _ = _
    rw [ih, show (4 : ℝ) ^ (J + 1) * X = 4 * ((4 : ℝ) ^ J * X) by rw [pow_succ]; ring,
      normalized_fourDeficit_step (by positivity)]

/-- The finite correction has a nonnegative remainder bounded at its final geometric scale. -/
theorem profilePartial_error {X : ℝ} (hX : 0 < X) (J : ℕ) :
    0 ≤ fourProfile X - profilePartial J X ∧
      fourProfile X - profilePartial J X ≤ 1 / (12 * (4 : ℝ) ^ J * X) := by
  have hZ : 0 < (4 : ℝ) ^ J * X := by positivity
  have h := fourProfile_approx hZ
  rw [fourProfile_pow hX] at h
  rw [profilePartial_eq hX]
  have he : fourProfile X - fourDeficit ((4 : ℝ) ^ J * X) / ((4 : ℝ) ^ J * X) =
      (((4 : ℝ) ^ J * X) * fourProfile X - fourDeficit ((4 : ℝ) ^ J * X)) /
        ((4 : ℝ) ^ J * X) := by field_simp
  rw [he]
  refine ⟨div_nonneg h.1 hZ.le, ?_⟩
  calc
    _ ≤ (1 / 12 : ℝ) / ((4 : ℝ) ^ J * X) := div_le_div_of_nonneg_right h.2 hZ.le
    _ = _ := by ring

private theorem inverse_difference_half {X Y : ℝ} (hX : 1 / 2 ≤ X) (hY : 1 / 2 ≤ Y) :
    |1 / X - 1 / Y| ≤ 4 * |X - Y| := by
  have hX0 : 0 < X := by linarith only [hX]
  have hY0 : 0 < Y := by linarith only [hY]
  have hXY : 1 / 4 ≤ X * Y := by
    have h := mul_le_mul hX hY (by norm_num : (0 : ℝ) ≤ 1 / 2) hX0.le
    norm_num at h
    exact h
  have he : 1 / X - 1 / Y = (Y - X) / (X * Y) := by field_simp
  rw [he, abs_div, abs_of_pos (mul_pos hX0 hY0), abs_sub_comm Y X]
  calc
    _ ≤ |X - Y| / (1 / 4 : ℝ) :=
      div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hXY
    _ = _ := by ring

/-- A scale-independent modulus for each normalized midpoint correction. -/
theorem midpoint_fraction_difference {scale X Y : ℝ} (hscale : 0 < scale)
    (hX : 1 / 2 ≤ X) (hY : 1 / 2 ≤ Y) :
    |midpointRounding (scale * X) / (scale * X) - midpointRounding (scale * Y) / (scale * Y)| ≤
      (1 + 1 / scale) * |X - Y| := by
  have hX0 : 0 < X := by linarith only [hX]
  have hY0 : 0 < Y := by linarith only [hY]
  have hnum := midpointRounding_lipschitz (scale * X) (scale * Y)
  rw [← mul_sub, abs_mul, abs_of_pos hscale] at hnum
  have hfirst : |(midpointRounding (scale * X) - midpointRounding (scale * Y)) / (scale * X)| ≤
      |X - Y| := by
    rw [abs_div, abs_of_pos (mul_pos hscale hX0)]
    apply (div_le_iff₀ (mul_pos hscale hX0)).mpr
    have h := mul_le_mul_of_nonneg_left hX (mul_nonneg hscale.le (abs_nonneg (X - Y)))
    nlinarith only [hnum, h]
  have hsecond : |(midpointRounding (scale * Y) / scale) * (1 / X - 1 / Y)| ≤ |X - Y| / scale := by
    rw [abs_mul, abs_of_nonneg (div_nonneg (midpointRounding_nonneg _) hscale.le)]
    calc
      _ ≤ ((1 / 4 : ℝ) / scale) * (4 * |X - Y|) :=
        mul_le_mul
          (div_le_div_of_nonneg_right (midpointRounding_le_quarter _) hscale.le)
          (inverse_difference_half hX hY) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have he : midpointRounding (scale * X) / (scale * X) - midpointRounding (scale * Y) / (scale * Y) =
      (midpointRounding (scale * X) - midpointRounding (scale * Y)) / (scale * X) +
        (midpointRounding (scale * Y) / scale) * (1 / X - 1 / Y) := by
    field_simp
    ring
  rw [he]
  calc
    _ ≤ |(midpointRounding (scale * X) - midpointRounding (scale * Y)) / (scale * X)| +
        |(midpointRounding (scale * Y) / scale) * (1 / X - 1 / Y)| := abs_add_le _ _
    _ ≤ |X - Y| + |X - Y| / scale := add_le_add hfirst hsecond
    _ = _ := by ring

private theorem normalized_fourDeficit_small {X : ℝ} (hX : 0 < X) (hX16 : X ≤ 16) :
    fourDeficit X / X = X / 48 + midpointRounding X / X +
      midpointRounding ((1 / 4 : ℝ) * X) / ((1 / 4 : ℝ) * X) := by
  have hcut : |X| ≤ (4 : ℝ) ^ 2 := by
    simpa only [abs_of_pos hX, show (4 : ℝ) ^ 2 = 16 by norm_num] using hX16
  rw [fourDeficit, fourArea_eq_sum 2 hcut]
  norm_num [Finset.sum_range_succ, oddArea]
  simp only [show (1 / 4 : ℝ) * X = X / 4 by ring]
  field_simp
  ring

private theorem normalized_fourDeficit_difference {X Y : ℝ}
    (hX : 1 / 2 ≤ X) (hX8 : X ≤ 8) (hY : 1 / 2 ≤ Y) (hY8 : Y ≤ 8) :
    |fourDeficit X / X - fourDeficit Y / Y| ≤ 8 * |X - Y| := by
  have hX0 : 0 < X := by linarith only [hX]
  have hY0 : 0 < Y := by linarith only [hY]
  have h1 := midpoint_fraction_difference (scale := 1) (by norm_num) hX hY
  have h4 := midpoint_fraction_difference (scale := 1 / 4) (by norm_num) hX hY
  norm_num at h1 h4
  have he : fourDeficit X / X - fourDeficit Y / Y = (X - Y) / 48 +
      (midpointRounding X / X - midpointRounding Y / Y) +
      (midpointRounding ((1 / 4 : ℝ) * X) / ((1 / 4 : ℝ) * X) -
        midpointRounding ((1 / 4 : ℝ) * Y) / ((1 / 4 : ℝ) * Y)) := by
    rw [normalized_fourDeficit_small hX0 (by linarith only [hX8]),
      normalized_fourDeficit_small hY0 (by linarith only [hY8])]
    ring
  rw [he]
  calc
    _ ≤ |(X - Y) / 48| + |midpointRounding X / X - midpointRounding Y / Y| +
        |midpointRounding ((1 / 4 : ℝ) * X) / ((1 / 4 : ℝ) * X) -
          midpointRounding ((1 / 4 : ℝ) * Y) / ((1 / 4 : ℝ) * Y)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ |X - Y| / 48 + 2 * |X - Y| + 5 * |X - Y| := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 48)]
      apply add_le_add (add_le_add le_rfl h1)
      exact h4
    _ ≤ _ := by linarith only [abs_nonneg (X - Y)]

private theorem profilePartial_difference {X Y : ℝ}
    (hX : 1 / 2 ≤ X) (hX8 : X ≤ 8) (hY : 1 / 2 ≤ Y) (hY8 : Y ≤ 8) (J : ℕ) :
    |profilePartial J X - profilePartial J Y| ≤ (2 * (J : ℝ) + 8) * |X - Y| := by
  let u (j : ℕ) := midpointRounding ((4 : ℝ) ^ (j + 1) * X) / ((4 : ℝ) ^ (j + 1) * X) -
    midpointRounding ((4 : ℝ) ^ (j + 1) * Y) / ((4 : ℝ) ^ (j + 1) * Y)
  have hu (j : ℕ) : |u j| ≤ 2 * |X - Y| := by
    have hp : (1 : ℝ) ≤ (4 : ℝ) ^ (j + 1) := one_le_pow₀ (by norm_num)
    have hp0 : 0 < (4 : ℝ) ^ (j + 1) := by positivity
    have hrec : 1 / (4 : ℝ) ^ (j + 1) ≤ 1 := (div_le_one hp0).mpr hp
    have h := midpoint_fraction_difference hp0 hX hY
    apply h.trans
    exact mul_le_mul_of_nonneg_right (by linarith only [hrec]) (abs_nonneg _)
  have hsum : |∑ j ∈ Finset.range J, u j| ≤ (J : ℝ) * (2 * |X - Y|) := by
    apply abs_le.mpr
    constructor
    · have h := Finset.sum_le_sum (s := Finset.range J)
        (fun j _ => (abs_le.mp (hu j)).1)
      simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_neg] using h
    · have h := Finset.sum_le_sum (s := Finset.range J)
        (fun j _ => (abs_le.mp (hu j)).2)
      simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h
  have he : profilePartial J X - profilePartial J Y =
      (fourDeficit X / X - fourDeficit Y / Y) + ∑ j ∈ Finset.range J, u j := by
    dsimp only [profilePartial, u]
    rw [Finset.sum_sub_distrib]
    ring
  rw [he]
  calc
    _ ≤ |fourDeficit X / X - fourDeficit Y / Y| + |∑ j ∈ Finset.range J, u j| := abs_add_le _ _
    _ ≤ 8 * |X - Y| + (J : ℝ) * (2 * |X - Y|) :=
      add_le_add (normalized_fourDeficit_difference hX hX8 hY hY8) hsum
    _ = _ := by ring

/-- An explicit modulus on a compact scale interval, with freely chosen truncation depth. -/
theorem fourProfile_compact_modulus {X Y : ℝ}
    (hX : 1 / 2 ≤ X) (hX8 : X ≤ 8) (hY : 1 / 2 ≤ Y) (hY8 : Y ≤ 8) (J : ℕ) :
    |fourProfile X - fourProfile Y| ≤
      (2 * (J : ℝ) + 8) * |X - Y| + 1 / (3 * (4 : ℝ) ^ J) := by
  have htail {Z : ℝ} (hZ : 1 / 2 ≤ Z) :
      |fourProfile Z - profilePartial J Z| ≤ 1 / (6 * (4 : ℝ) ^ J) := by
    have hz0 : 0 < Z := by linarith only [hZ]
    have h := profilePartial_error hz0 J
    rw [abs_of_nonneg h.1]
    apply h.2.trans
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith only [mul_nonneg (by positivity : 0 ≤ 12 * (4 : ℝ) ^ J) (sub_nonneg.mpr hZ)]
  have he : fourProfile X - fourProfile Y =
      ((fourProfile X - profilePartial J X) + (profilePartial J X - profilePartial J Y)) -
        (fourProfile Y - profilePartial J Y) := by ring
  rw [he]
  calc
    _ ≤ (|fourProfile X - profilePartial J X| + |profilePartial J X - profilePartial J Y|) +
        |fourProfile Y - profilePartial J Y| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (1 / (6 * (4 : ℝ) ^ J) + (2 * (J : ℝ) + 8) * |X - Y|) +
        1 / (6 * (4 : ℝ) ^ J) :=
      add_le_add (add_le_add (htail hX) (profilePartial_difference hX hX8 hY hY8 J)) (htail hY)
    _ = _ := by ring

private theorem log_four_eq_two_log_two : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num

private theorem log_eight_eq_three_log_two : Real.log 8 = 3 * Real.log 2 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
  norm_num

/-- The compact-scale modulus becomes uniform on the logarithmic line. -/
theorem logarithmicProfile_modulus (t d : ℝ) (hd : |d| ≤ Real.log 4 / 2) (J : ℕ) :
    |logarithmicProfile (t + d) - logarithmicProfile t| ≤
      (16 * (J : ℝ) + 64) * |d| + 1 / (3 * (4 : ℝ) ^ J) := by
  have hp : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let n : ℤ := ⌊t / Real.log 4⌋
  let u := t - (n : ℝ) * Real.log 4
  have hu0 : 0 ≤ u := by
    have h := (le_div_iff₀ hp).mp (Int.floor_le (t / Real.log 4))
    dsimp only [u, n]
    linarith only [h]
  have hup : u ≤ Real.log 4 := by
    have h := (div_lt_iff₀ hp).mp (Int.lt_floor_add_one (t / Real.log 4))
    dsimp only [u, n]
    linarith only [h]
  have hdn : -Real.log 2 ≤ d ∧ d ≤ Real.log 2 := by
    have h := abs_le.mp hd
    rw [log_four_eq_two_log_two] at h
    constructor <;> linarith only [h.1, h.2]
  have hudlo : -Real.log 2 ≤ u + d := by linarith only [hu0, hdn.1]
  have hudhi : u + d ≤ Real.log 8 := by
    rw [log_four_eq_two_log_two] at hup
    rw [log_eight_eq_three_log_two]
    linarith only [hup, hdn.2]
  have huhi : u ≤ Real.log 8 := by
    rw [log_four_eq_two_log_two] at hup
    rw [log_eight_eq_three_log_two]
    linarith only [hup, htwo]
  have hx0 : 1 / 2 ≤ Real.exp u := by
    have h := Real.exp_le_exp.mpr hu0
    rw [Real.exp_zero] at h
    linarith only [h]
  have hx8 : Real.exp u ≤ 8 := by
    have h := Real.exp_le_exp.mpr huhi
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 8)] at h
  have hy0 : 1 / 2 ≤ Real.exp (u + d) := by
    have h := Real.exp_le_exp.mpr hudlo
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
    simpa only [one_div] using h
  have hy8 : Real.exp (u + d) ≤ 8 := by
    have h := Real.exp_le_exp.mpr hudhi
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 8)] at h
  have hdist := HTGeometry.abs_exp_sub_exp_le hudhi huhi
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 8), add_sub_cancel_left] at hdist
  have hmod := fourProfile_compact_modulus hy0 hy8 hx0 hx8 J
  change |logarithmicProfile (u + d) - logarithmicProfile u| ≤ _ at hmod
  have hbase : logarithmicProfile u = logarithmicProfile t :=
    (logarithmicProfile_periodic.int_mul n).sub_eq t
  have hshift : logarithmicProfile (u + d) = logarithmicProfile (t + d) := by
    have he : u + d = (t + d) - (n : ℝ) * Real.log 4 := by dsimp only [u]; ring
    rw [he]
    exact (logarithmicProfile_periodic.int_mul n).sub_eq (t + d)
  rw [hbase, hshift] at hmod
  calc
    _ ≤ (2 * (J : ℝ) + 8) * |Real.exp (u + d) - Real.exp u| +
        1 / (3 * (4 : ℝ) ^ J) := hmod
    _ ≤ (2 * (J : ℝ) + 8) * (8 * |d|) + 1 / (3 * (4 : ℝ) ^ J) :=
      add_le_add (mul_le_mul_of_nonneg_left hdist (by positivity)) le_rfl
    _ = _ := by ring

private theorem log_four_power_cutoffs {X : ℝ} (hX : 1 ≤ X) :
    (4 : ℝ) ^ ⌊Real.log X / Real.log 4⌋₊ ≤ X ∧
      X < (4 : ℝ) ^ (⌊Real.log X / Real.log 4⌋₊ + 1) := by
  have hx : 0 < X := zero_lt_one.trans_le hX
  have hp : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlo := Nat.floor_le (div_nonneg (Real.log_nonneg hX) hp.le)
  have hhi := Nat.lt_floor_add_one (Real.log X / Real.log 4)
  constructor
  · apply (Real.log_le_log_iff (by positivity : 0 < (4 : ℝ) ^ ⌊Real.log X / Real.log 4⌋₊) hx).mp
    rw [Real.log_pow]
    exact (le_div_iff₀ hp).mp hlo
  · apply (Real.log_lt_log_iff hx (by positivity : 0 < (4 : ℝ) ^ (⌊Real.log X / Real.log 4⌋₊ + 1))).mp
    rw [Real.log_pow]
    push_cast
    exact (div_lt_iff₀ hp).mp hhi

/-- A logarithmic displacement of size `log 4 / Q` has an explicit uniform profile error. -/
theorem logarithmicProfile_resolution_modulus {Q : ℕ} (hQ : 2 ≤ Q)
    (t d : ℝ) (hd : |d| ≤ Real.log 4 / (Q : ℝ)) :
    |logarithmicProfile (t + d) - logarithmicProfile t| ≤
      (16 * Real.log (Q : ℝ) + 64 * Real.log 4 + 4 / 3) / (Q : ℝ) := by
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < Q := by positivity
  have hp : 0 < Real.log 4 := Real.log_pos (by norm_num)
  let J := ⌊Real.log (Q : ℝ) / Real.log 4⌋₊
  have hd' : |d| ≤ Real.log 4 / 2 := by
    apply hd.trans
    exact div_le_div_of_nonneg_left hp.le (by norm_num) hQR
  have h := logarithmicProfile_modulus t d hd' J
  have hJ : (J : ℝ) ≤ Real.log (Q : ℝ) / Real.log 4 :=
    Nat.floor_le (div_nonneg (Real.log_nonneg (by linarith only [hQR])) hp.le)
  have hJp := (le_div_iff₀ hp).mp hJ
  have hcut := (log_four_power_cutoffs (X := (Q : ℝ)) (by linarith only [hQR])).2
  have htail : 1 / (3 * (4 : ℝ) ^ J) ≤ 4 / (3 * (Q : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 3 * (4 : ℝ) ^ J)
      (by positivity : 0 < 3 * (Q : ℝ))).mpr
    change (Q : ℝ) < (4 : ℝ) ^ (J + 1) at hcut
    rw [pow_succ] at hcut
    linarith only [hcut]
  have hmain : (16 * (J : ℝ) + 64) * |d| ≤
      (16 * Real.log (Q : ℝ) + 64 * Real.log 4) / (Q : ℝ) := by
    calc
      _ ≤ (16 * (J : ℝ) + 64) * (Real.log 4 / (Q : ℝ)) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
      _ = ((16 * (J : ℝ) + 64) * Real.log 4) / (Q : ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [hJp]) hQ0.le
  calc
    _ ≤ (16 * (J : ℝ) + 64) * |d| + 1 / (3 * (4 : ℝ) ^ J) := h
    _ ≤ (16 * Real.log (Q : ℝ) + 64 * Real.log 4) / (Q : ℝ) + 4 / (3 * (Q : ℝ)) :=
      add_le_add hmain htail
    _ = _ := by ring

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCount
