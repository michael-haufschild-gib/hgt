import GaloisForLFunctions.BiScaleUncertainty.CompensatedHausdorffPhase

/-!
# The quadratic scale of a compensated Hausdorff saddle

A reciprocal-square slope at height `u` lies between `1/u²` and `1/(u²-1)`.
For heights in `[T,T+H]` and powers matched by `r=nT²`, the signed phase costs
`O(nH/T²)`, with cubic remainder `O(n/T³)`. Thus `T² >= 32nH` controls a whole
band even though the separate absolute phases can grow with the order.
-/

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-- Height localization gives both the signed balance and the complementary power budget. -/
theorem hausdorff_saddle_slope_bounds {n r T H u a : ℝ}
    (hn : 0 ≤ n) (hT : 4 ≤ T) (hH : 1 ≤ H) (hHT : H ≤ T)
    (huT : T ≤ u) (huH : u ≤ T + H) (hr : r = n * T ^ 2)
    (haL : 1 / u ^ 2 ≤ a) (haU : a ≤ 1 / (u ^ 2 - 1)) :
    0 ≤ a ∧ a ≤ 1 ∧ r * a ≤ 2 * n ∧ |n - r * a| ≤ 4 * n * H / T := by
  have hT0 : 0 < T := by linarith
  have hu0 : 0 < u := by linarith
  have hT2 : 0 < T ^ 2 := sq_pos_of_pos hT0
  have hu2 : 0 < u ^ 2 := sq_pos_of_pos hu0
  have hTu : T ^ 2 ≤ u ^ 2 := by nlinarith
  have hu21 : 0 < u ^ 2 - 1 := by nlinarith
  have ha0 : 0 ≤ a := (by positivity : (0 : ℝ) ≤ 1 / u ^ 2).trans haL
  have haDen : a * (u ^ 2 - 1) ≤ 1 := (le_div_iff₀ hu21).mp haU
  have haT : a * (T ^ 2 - 1) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (by linarith : T ^ 2 - 1 ≤ u ^ 2 - 1) ha0).trans haDen
  have ha1 : a ≤ 1 := by nlinarith [mul_nonneg ha0 (show 0 ≤ T ^ 2 - 2 by nlinarith)]
  have haT2 : a * T ^ 2 ≤ 2 := by linarith
  have hra : r * a ≤ 2 * n := by
    rw [hr]
    nlinarith [mul_le_mul_of_nonneg_left haT2 hn]
  have haTH : a * T ≤ H := by
    have hTT : T ≤ T ^ 2 - 1 := by nlinarith
    exact ((mul_le_mul_of_nonneg_left hTT ha0).trans haT).trans hH
  have hU : r * a - n ≤ n * H / T := by
    have h1 : r * a - n ≤ n * a := by
      rw [hr]
      nlinarith [mul_le_mul_of_nonneg_left haT hn]
    have h2 : n * a ≤ n * H / T := by
      rw [le_div_iff₀ hT0]
      nlinarith [mul_le_mul_of_nonneg_left haTH hn]
    exact h1.trans h2
  have hdiff : u ^ 2 - T ^ 2 ≤ 3 * T * H := by
    have huSq : u ^ 2 ≤ (T + H) ^ 2 := by nlinarith
    have hHsq : H ^ 2 ≤ T * H := by nlinarith
    nlinarith
  have hratio : (u ^ 2 - T ^ 2) / u ^ 2 ≤ 3 * H / T := by
    calc
      _ ≤ (3 * T * H) / u ^ 2 := div_le_div_of_nonneg_right hdiff hu2.le
      _ ≤ (3 * T * H) / T ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) hT2 hTu
      _ = 3 * H / T := by field_simp
  have h1 : 1 - T ^ 2 * a ≤ (u ^ 2 - T ^ 2) / u ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left haL hT2.le
    have hid : (u ^ 2 - T ^ 2) / u ^ 2 = 1 - T ^ 2 * (1 / u ^ 2) := by
      field_simp
    rw [hid]
    linarith
  have hL : n - r * a ≤ 3 * n * H / T := by
    have hh := mul_le_mul_of_nonneg_left (h1.trans hratio) hn
    calc
      n - r * a = n * (1 - T ^ 2 * a) := by rw [hr]; ring
      _ ≤ n * (3 * H / T) := hh
      _ = 3 * n * H / T := by ring
  refine ⟨ha0, ha1, hra, abs_le.mpr ⟨?_, ?_⟩⟩
  · have hnonneg : 0 ≤ n * H / T := by positivity
    ring_nf at hU hnonneg ⊢
    linarith
  · have hnonneg : 0 ≤ n * H / T := by positivity
    ring_nf at hL hnonneg ⊢
    linarith

/-- A quadratic height budget controls the signed phase of the whole band. -/
theorem signedPowerPhaseBudget_le_of_saddle_bounds (n r : ℕ) {T H a τ : ℝ}
    (hT : 4 ≤ T) (hH : 1 ≤ H) (hscale : 32 * (n : ℝ) * H ≤ T ^ 2)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hra : (r : ℝ) * a ≤ 2 * n)
    (hbalance : |(n : ℝ) - (r : ℝ) * a| ≤ 4 * n * H / T)
    (hτ : |τ| ≤ 2 / T) :
    signedPowerPhaseBudget n r τ (a * τ) ≤ 5 / 16 := by
  have hT0 : 0 < T := by linarith
  have hT2 : 0 < T ^ 2 := sq_pos_of_pos hT0
  have ha3 : a ^ 3 ≤ a := by
    have ha2 : a ^ 2 ≤ a := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left ha2 ha0]
  have hcoef : (n : ℝ) + (r : ℝ) * a ^ 3 ≤ 3 * n := by
    nlinarith [mul_le_mul_of_nonneg_left ha3 (Nat.cast_nonneg r)]
  have hlin : |(n : ℝ) * τ - (r : ℝ) * (a * τ)| ≤ 8 * n * H / T ^ 2 := by
    rw [show (n : ℝ) * τ - (r : ℝ) * (a * τ) =
      τ * ((n : ℝ) - (r : ℝ) * a) by ring, abs_mul]
    calc
      _ ≤ (2 / T) * (4 * n * H / T) :=
        mul_le_mul hτ hbalance (abs_nonneg _) (by positivity)
      _ = 8 * n * H / T ^ 2 := by ring
  have hcubic : ((n : ℝ) * |τ| ^ 3 + (r : ℝ) * |a * τ| ^ 3) / 3 ≤
      8 * n / T ^ 3 := by
    rw [abs_mul, abs_of_nonneg ha0, mul_pow]
    calc
      _ = |τ| ^ 3 * ((n : ℝ) + (r : ℝ) * a ^ 3) / 3 := by ring
      _ ≤ (2 / T) ^ 3 * (3 * n) / 3 := by gcongr
      _ = 8 * n / T ^ 3 := by ring
  have hlinSmall : 8 * (n : ℝ) * H / T ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ hT2]
    linarith
  have h32 : 32 * (n : ℝ) ≤ T ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hH (show 0 ≤ 32 * (n : ℝ) by positivity)
    nlinarith
  have hT3 : 4 * T ^ 2 ≤ T ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_right hT hT2.le]
  have hcubicSmall : 8 * (n : ℝ) / T ^ 3 ≤ 1 / 16 := by
    rw [div_le_iff₀ (pow_pos hT0 3)]
    linarith
  unfold signedPowerPhaseBudget
  linarith

end

end GaloisForLFunctions.BiScaleUncertainty
