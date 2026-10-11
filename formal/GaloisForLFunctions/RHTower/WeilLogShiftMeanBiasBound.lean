import GaloisForLFunctions.RHTower.WeilLogShiftArithmeticMixedSecondMoment
import GaloisForLFunctions.RHTower.WeilLogShiftProfileLowerBound
import GaloisForLFunctions.RHTower.WeilLogShiftMidpointProfile
import GaloisForLFunctions.RHTower.WeilLogShiftEdgeMoments

/-! The canonical midpoint and edge means have uniformly bounded displacement from their binomial centers. -/

open scoped BigOperators

namespace RHTower

theorem finiteWeilCanonicalMassProfile_weighted_first_error (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    (∑ i, |finiteWeilCanonicalMassProfile r k i - finiteWeilArithmeticAbsProfile r i| *
      |((i : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2|) ≤ finiteWeilArithmeticMass r := by
  have hn : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
  calc
    _ ≤ ∑ i, ((finiteWeilArithmeticAbsProfile r i *
        |((i : ℕ) : ℝ) - ((finiteWeilArithmeticCenter r : Fin (r + 2)) : ℕ)|) /
          ((r + 1 : ℕ) : ℝ)) * |((i : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2| :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
        (finiteWeilCanonicalMassProfile_error r k hwidth i) (abs_nonneg _)
    _ = (∑ i, finiteWeilArithmeticAbsProfile r i *
        |((i : ℕ) : ℝ) - ((finiteWeilArithmeticCenter r : Fin (r + 2)) : ℕ)| *
          |((i : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2|) / ((r + 1 : ℕ) : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ (((r + 1 : ℕ) : ℝ) * finiteWeilArithmeticMass r) / ((r + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right (finiteWeilArithmeticAbsProfile_mixed_second_bound r) hn.le
    _ = _ := by field_simp

theorem finiteWeilCanonicalMidpointIndexMean_bias_bound (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    |finiteWeilCanonicalMidpointIndexMean r k - ((r + 1 : ℕ) : ℝ) / 2| ≤ 2 := by
  let f := finiteWeilCanonicalMassProfile r k
  let q := finiteWeilArithmeticAbsProfile r
  let F := ∑ i, f i
  let G := finiteWeilArithmeticMass r
  let n : ℝ := ((r + 1 : ℕ) : ℝ)
  let x := fun i : Fin (r + 2) => ((i : ℕ) : ℝ) - n / 2
  let B := ∑ i, f i * x i
  have hFbound : G / 2 ≤ F := finiteWeilCanonicalMassProfile_sum_ge_half r k hwidth
  have hG : 0 < G := lt_of_lt_of_le (by norm_num) (finiteWeilArithmeticMass_ge_two r)
  have hF : 0 < F := by linarith only [hFbound, hG]
  have hqzero : (∑ i, q i * x i) = 0 := finiteWeilArithmeticAbsProfile_half_first_moment r
  have hdiff : (∑ i, (f i - q i) * x i) = B := by
    simp only [sub_mul, Finset.sum_sub_distrib, hqzero, sub_zero]
    rfl
  have habs : |B| ≤ G := by
    rw [← hdiff]
    calc
      _ ≤ ∑ i, |(f i - q i) * x i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |f i - q i| * |x i| := by simp only [abs_mul]
      _ ≤ _ := finiteWeilCanonicalMassProfile_weighted_first_error r k hwidth
  have hM : finiteWeilCanonicalMidpointIndexMean r k = (∑ i, f i * ((i : ℕ) : ℝ)) / F := by
    unfold finiteWeilCanonicalMidpointIndexMean
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    rw [finiteWeilCanonicalMixture_midpoint_profile]
    change _ / F * _ = _ / F
    ring
  have hB : B = (∑ i, f i * ((i : ℕ) : ℝ)) - n / 2 * F := by
    dsimp [B, x]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    dsimp [F]
    ring
  have hid : (∑ i, f i * ((i : ℕ) : ℝ)) / F - n / 2 = B / F := by
    rw [hB]
    field_simp
  change |finiteWeilCanonicalMidpointIndexMean r k - n / 2| ≤ 2
  rw [hM, hid, abs_div, abs_of_pos hF]
  apply (div_le_iff₀ hF).mpr
  linarith only [habs, hFbound]

theorem finiteWeilCanonicalEdgeIndexMean_bias_bound (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    |finiteWeilCanonicalEdgeIndexMean r k - (r : ℝ) / 2| ≤ 2 := by
  have h := finiteWeilCanonicalMidpointIndexMean_bias_bound r k hwidth
  rw [finiteWeilCanonicalMidpointIndexMean_eq_edge] at h
  have hid : finiteWeilCanonicalEdgeIndexMean r k + 1 / 2 - ((r + 1 : ℕ) : ℝ) / 2 =
      finiteWeilCanonicalEdgeIndexMean r k - (r : ℝ) / 2 := by push_cast; ring
  rwa [hid] at h

theorem finiteWeilCanonicalEdgeIndexMean_normalized_bias_bound (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    |finiteWeilCanonicalEdgeIndexMean r k / ((r + 1 : ℕ) : ℝ) - 1 / 2| ≤ 3 / ((r + 1 : ℕ) : ℝ) := by
  have hn : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
  have hb := finiteWeilCanonicalEdgeIndexMean_bias_bound r k hwidth
  have ht := abs_sub (finiteWeilCanonicalEdgeIndexMean r k - (r : ℝ) / 2) ((1 : ℝ) / 2)
  norm_num at ht
  have hid : finiteWeilCanonicalEdgeIndexMean r k - ((r + 1 : ℕ) : ℝ) / 2 =
      (finiteWeilCanonicalEdgeIndexMean r k - (r : ℝ) / 2) - 1 / 2 := by push_cast; ring
  have hraw : |finiteWeilCanonicalEdgeIndexMean r k - ((r + 1 : ℕ) : ℝ) / 2| ≤ 3 := by
    rw [hid]
    linarith only [ht, hb]
  have hdiv : finiteWeilCanonicalEdgeIndexMean r k / ((r + 1 : ℕ) : ℝ) - 1 / 2 =
      (finiteWeilCanonicalEdgeIndexMean r k - ((r + 1 : ℕ) : ℝ) / 2) / ((r + 1 : ℕ) : ℝ) := by field_simp
  rw [hdiv, abs_div, abs_of_pos hn]
  exact div_le_div_of_nonneg_right hraw hn.le

theorem finiteWeilCanonicalEdgeIndexMean_quadratic_bias_bound (r t : ℕ) :
    |finiteWeilCanonicalEdgeIndexMean r (2 * (r + 1) ^ 2 + t) - (r : ℝ) / 2| ≤ 2 := by
  apply finiteWeilCanonicalEdgeIndexMean_bias_bound
  push_cast
  have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
  nlinarith only [ht]

end RHTower
