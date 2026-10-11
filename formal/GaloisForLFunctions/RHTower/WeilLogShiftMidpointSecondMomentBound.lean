import GaloisForLFunctions.RHTower.WeilLogShiftArithmeticFourthMoment
import GaloisForLFunctions.RHTower.WeilLogShiftProfileLowerBound
import GaloisForLFunctions.RHTower.WeilLogShiftMidpointBinomialBound

/-! Weighted profile control preserves the binomial second moment at its natural scale. -/

open scoped BigOperators

namespace RHTower

theorem finiteWeilCanonicalMassProfile_weighted_second_error (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    (∑ i, |finiteWeilCanonicalMassProfile r k i - finiteWeilArithmeticAbsProfile r i| *
      (((i : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2) ^ 2) ≤
      finiteWeilArithmeticMass r * Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) := by
  have hn : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
  calc
    _ ≤ ∑ i, ((finiteWeilArithmeticAbsProfile r i *
        |((i : ℕ) : ℝ) - ((finiteWeilArithmeticCenter r : Fin (r + 2)) : ℕ)|) /
          ((r + 1 : ℕ) : ℝ)) * (((i : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2) ^ 2 :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
        (finiteWeilCanonicalMassProfile_error r k hwidth i) (sq_nonneg _)
    _ = (∑ i, finiteWeilArithmeticAbsProfile r i *
        |((i : ℕ) : ℝ) - ((finiteWeilArithmeticCenter r : Fin (r + 2)) : ℕ)| *
          (((i : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2) ^ 2) / ((r + 1 : ℕ) : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ (finiteWeilArithmeticMass r * ((r + 1 : ℕ) : ℝ) *
        Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2)) / ((r + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right (finiteWeilArithmeticAbsProfile_mixed_third_bound r) hn.le
    _ = _ := by field_simp

theorem finiteWeilCanonicalMassProfile_second_centering_error (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    |(∑ i, finiteWeilCanonicalMassProfile r k i *
        (((i : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2) ^ 2) -
      (((r + 1 : ℕ) : ℝ) / 4) * (∑ i, finiteWeilCanonicalMassProfile r k i)| ≤
        2 * finiteWeilArithmeticMass r * Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) := by
  let f := finiteWeilCanonicalMassProfile r k
  let q := finiteWeilArithmeticAbsProfile r
  let F := ∑ i, f i
  let G := finiteWeilArithmeticMass r
  let n : ℝ := ((r + 1 : ℕ) : ℝ)
  let S := Real.sqrt ((n + 1) / 2)
  let x := fun i : Fin (r + 2) => ((i : ℕ) : ℝ) - n / 2
  let B := ∑ i, f i * x i ^ 2
  have hn : 0 < n := by dsimp [n]; positivity
  have hG : 0 < G := lt_of_lt_of_le (by norm_num) (finiteWeilArithmeticMass_ge_two r)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hFG : |F - G| ≤ G * (S / n) := by
    calc
      _ = |∑ i, (f i - q i)| := by rw [Finset.sum_sub_distrib, finiteWeilArithmeticAbsProfile_sum]
      _ ≤ ∑ i, |f i - q i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := finiteWeilCanonicalMassProfile_l1_error r k hwidth
  have hq2 : (∑ i, q i * x i ^ 2) = n / 4 * G := finiteWeilArithmeticAbsProfile_half_second_moment r
  have hdecomp : B - n / 4 * F = (∑ i, (f i - q i) * x i ^ 2) + (n / 4) * (G - F) := by
    simp only [sub_mul, Finset.sum_sub_distrib, hq2]
    dsimp [B]
    ring
  have hweighted : (∑ i, |f i - q i| * x i ^ 2) ≤ G * S :=
    finiteWeilCanonicalMassProfile_weighted_second_error r k hwidth
  change |B - n / 4 * F| ≤ 2 * G * S
  rw [hdecomp]
  calc
    _ ≤ |∑ i, (f i - q i) * x i ^ 2| + |(n / 4) * (G - F)| := abs_add_le _ _
    _ ≤ (∑ i, |f i - q i| * x i ^ 2) + (n / 4) * |F - G| := by
      apply add_le_add
      · calc
          _ ≤ ∑ i, |(f i - q i) * x i ^ 2| := Finset.abs_sum_le_sum_abs _ _
          _ = _ := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [abs_mul, abs_of_nonneg (sq_nonneg (x i))]
      · rw [abs_mul, abs_of_nonneg (show 0 ≤ n / 4 by positivity), abs_sub_comm]
    _ ≤ G * S + (n / 4) * (G * (S / n)) :=
      add_le_add hweighted (mul_le_mul_of_nonneg_left hFG (by positivity))
    _ ≤ _ := by
      have hid : (n / 4) * (G * (S / n)) = G * S / 4 := by field_simp
      rw [hid]
      nlinarith only [mul_nonneg hG.le hS]

theorem finiteWeilCanonicalMixture_midpoint_second_moment_error (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    |(∑ i, finiteWeilCanonicalMixture r k (1 / 2) i *
      (((i : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2) ^ 2) - ((r + 1 : ℕ) : ℝ) / 4| ≤
        4 * Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) := by
  let F := ∑ i, finiteWeilCanonicalMassProfile r k i
  let G := finiteWeilArithmeticMass r
  let n : ℝ := ((r + 1 : ℕ) : ℝ)
  let S := Real.sqrt ((n + 1) / 2)
  let B := ∑ i, finiteWeilCanonicalMassProfile r k i * (((i : ℕ) : ℝ) - n / 2) ^ 2
  have hFbound : G / 2 ≤ F := finiteWeilCanonicalMassProfile_sum_ge_half r k hwidth
  have hG : 0 < G := lt_of_lt_of_le (by norm_num) (finiteWeilArithmeticMass_ge_two r)
  have hF : 0 < F := by linarith only [hFbound, hG]
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hraw : |B - n / 4 * F| ≤ 2 * G * S :=
    finiteWeilCanonicalMassProfile_second_centering_error r k hwidth
  have hnum : |B - n / 4 * F| ≤ 4 * S * F := by
    have hmul := mul_le_mul_of_nonneg_right hFbound hS
    nlinarith only [hraw, hmul]
  have hM : (∑ i, finiteWeilCanonicalMixture r k (1 / 2) i *
      (((i : ℕ) : ℝ) - n / 2) ^ 2) = B / F := by
    change _ = (∑ i, finiteWeilCanonicalMassProfile r k i * (((i : ℕ) : ℝ) - n / 2) ^ 2) / F
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    rw [finiteWeilCanonicalMixture_midpoint_profile]
    change _ / F * _ = _ / F
    ring
  change |(∑ i, finiteWeilCanonicalMixture r k (1 / 2) i * (((i : ℕ) : ℝ) - n / 2) ^ 2) - n / 4| ≤ 4 * S
  rw [hM]
  have hid : B / F - n / 4 = (B - n / 4 * F) / F := by field_simp
  rw [hid, abs_div, abs_of_pos hF]
  exact (div_le_iff₀ hF).mpr hnum

end RHTower
