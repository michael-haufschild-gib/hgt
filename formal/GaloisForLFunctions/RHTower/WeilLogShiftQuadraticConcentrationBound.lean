import GaloisForLFunctions.RHTower.WeilLogShiftCanonicalMassProfile

/-! Summed and maximal distortion control the normalized logarithmic mass at quadratic starts. -/

open scoped BigOperators
noncomputable section
namespace RHTower

theorem finiteWeilCanonicalMassProfile_sum_error (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    |(∑ i, finiteWeilCanonicalMassProfile r k i) - finiteWeilArithmeticMass r| ≤
      finiteWeilArithmeticMass r *
        (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)) := by
  rw [← finiteWeilArithmeticAbsProfile_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |finiteWeilCanonicalMassProfile r k i - finiteWeilArithmeticAbsProfile r i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (finiteWeilArithmeticAbsProfile r i *
        |((i : ℕ) : ℝ) - ((finiteWeilArithmeticCenter r : Fin (r + 2)) : ℕ)|) /
          ((r + 1 : ℕ) : ℝ) :=
      Finset.sum_le_sum fun i _ => finiteWeilCanonicalMassProfile_error r k hwidth i
    _ ≤ _ := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul, finiteWeilArithmeticAbsProfile_sum]
      simpa only [div_eq_mul_inv, mul_assoc] using mul_le_mul_of_nonneg_right
        (finiteWeilArithmeticAbsProfile_center_first_moment r) (by positivity :
          0 ≤ (((r + 1 : ℕ) : ℝ))⁻¹)

theorem finiteWeilCanonicalMassProfile_norm_error (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    ‖finiteWeilCanonicalMassProfile r k‖ - 1 ≤
      Real.sqrt (((((r + 1 : ℕ) : ℝ) + 1) / 2) * finiteWeilArithmeticMass r) /
        ((r + 1 : ℕ) : ℝ) := by
  apply sub_le_iff_le_add.mpr
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs, abs_of_pos (finiteWeilCanonicalMassProfile_pos r k i)]
  have he := (le_abs_self _).trans (finiteWeilCanonicalMassProfile_error r k hwidth i)
  have hp := div_le_div_of_nonneg_right
    (finiteWeilArithmeticAbsProfile_center_pointwise r i) (by positivity :
      0 ≤ ((r + 1 : ℕ) : ℝ))
  have hq := finiteWeilArithmeticAbsProfile_le_one r i
  linarith only [he, hp, hq]

/-- Both errors vanish: the average distortion and the movement of the maximum weight. -/
theorem finiteWeilCanonicalCluster_quadratic_concentration_error (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    |finiteWeilAbsMass (finiteWeilCanonicalCluster r k) / finiteWeilArithmeticMass r - 1| ≤
      Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ) +
      Real.sqrt (((((r + 1 : ℕ) : ℝ) + 1) / 2) * finiteWeilArithmeticMass r) /
        ((r + 1 : ℕ) : ℝ) := by
  let F := ∑ i, finiteWeilCanonicalMassProfile r k i
  let N := ‖finiteWeilCanonicalMassProfile r k‖
  let G := finiteWeilArithmeticMass r
  let e := Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)
  let d := Real.sqrt (((((r + 1 : ℕ) : ℝ) + 1) / 2) * G) / ((r + 1 : ℕ) : ℝ)
  have hN1 : 1 ≤ N := finiteWeilCanonicalMassProfile_norm_ge_one r k
  have hN : 0 < N := by linarith only [hN1]
  have hG : 0 < G := lt_of_lt_of_le (by norm_num) (finiteWeilArithmeticMass_ge_two r)
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have he : |F - G| ≤ G * e := finiteWeilCanonicalMassProfile_sum_error r k hwidth
  have hd : N - 1 ≤ d := finiteWeilCanonicalMassProfile_norm_error r k hwidth
  have hnum : |F - N * G| ≤ G * (e + d) := by
    calc
      _ = |(F - G) - G * (N - 1)| := by congr 1; ring
      _ ≤ |F - G| + |G * (N - 1)| := abs_sub _ _
      _ = |F - G| + G * (N - 1) := by
        rw [abs_of_nonneg (mul_nonneg hG.le (sub_nonneg.mpr hN1))]
      _ ≤ _ := by nlinarith only [he, mul_le_mul_of_nonneg_left hd hG.le]
  rw [finiteWeilCanonicalCluster_mass_eq_profile]
  change |F / N / G - 1| ≤ e + d
  have hid : F / N / G - 1 = (F - N * G) / (N * G) := by field_simp
  rw [hid, abs_div, abs_of_pos (mul_pos hN hG)]
  apply (div_le_iff₀ (mul_pos hN hG)).mpr
  calc
    _ ≤ G * (e + d) := hnum
    _ ≤ (e + d) * (N * G) := by
      nlinarith only [mul_le_mul_of_nonneg_right hN1 (mul_nonneg hG.le (add_nonneg he0 hd0))]

end RHTower
