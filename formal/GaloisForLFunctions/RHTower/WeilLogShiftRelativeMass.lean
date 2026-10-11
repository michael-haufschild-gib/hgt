import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticMass

/-! Quantitative error between arithmetic and logarithmic nodal masses. -/

noncomputable section
namespace RHTower

/-- Keep the full Bernoulli error instead of replacing its lower bound by one half. -/
theorem finiteWeil_power_bernoulli_error (n : ℕ) (A : ℝ) (hA : 0 < A) :
    (A + n - (n : ℝ) ^ 2) * (A + n) ^ n ≤ (A + n) * A ^ n := by
  have hU : 0 < A + n := by positivity
  have hfrac : (n : ℝ) / (A + n) ≤ 1 := (div_le_iff₀ hU).mpr (by linarith)
  have hb := one_add_mul_le_pow (a := -((n : ℝ) / (A + n))) (by linarith) n
  have hbase : 1 + -((n : ℝ) / (A + n)) = A / (A + n) := by
    field_simp
    ring
  rw [hbase, div_pow] at hb
  have hp := (le_div_iff₀ (pow_pos hU n)).mp hb
  have hm := mul_le_mul_of_nonneg_left hp hU.le
  have heq : (A + n) * ((1 + (n : ℝ) * -((n : ℝ) / (A + n))) *
      (A + n) ^ n) = (A + n - (n : ℝ) ^ 2) * (A + n) ^ n := by
    field_simp
    ring
  rwa [heq] at hm

/-- Both one-sided errors hold for every cluster start, before any width restriction. -/
theorem finiteWeilCanonicalCluster_mass_error_bounds (r k : ℕ) :
    ((k + r + 3 : ℕ) : ℝ) *
        (finiteWeilArithmeticMass r - finiteWeilAbsMass (finiteWeilCanonicalCluster r k)) ≤
      ((r + 1 : ℕ) : ℝ) ^ 2 * finiteWeilArithmeticMass r ∧
    (((k + r + 3 : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) ^ 2) *
        (finiteWeilAbsMass (finiteWeilCanonicalCluster r k) - finiteWeilArithmeticMass r) ≤
      ((r + 1 : ℕ) : ℝ) ^ 2 * finiteWeilArithmeticMass r := by
  let A : ℝ := ((k + 2 : ℕ) : ℝ)
  let U : ℝ := ((k + r + 3 : ℕ) : ℝ)
  let n := r + 1
  let G := finiteWeilArithmeticMass r
  let S := finiteWeilAbsMass (finiteWeilCanonicalCluster r k)
  have hU : 0 < U := by dsimp [U]; positivity
  have hP : 0 < U ^ n := pow_pos hU n
  have hG : 0 ≤ G := by dsimp [G]; linarith only [finiteWeilArithmeticMass_ge_two r]
  have hS : 0 ≤ S := by
    dsimp [S, finiteWeilAbsMass]
    exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have heq : A + n = U := by dsimp [A, U, n]; push_cast; ring
  have hb := finiteWeil_power_bernoulli_error n A (by dsimp [A]; positivity)
  rw [heq] at hb
  obtain ⟨hl, hu⟩ := finiteWeilCanonicalCluster_arithmetic_mass_comparison r k
  change A ^ n * G ≤ U ^ n * S at hl
  change A ^ n * S ≤ U ^ n * G at hu
  have hleft : (U - (n : ℝ) ^ 2) * G ≤ U * S := by
    apply (mul_le_mul_iff_right₀ hP).mp
    calc
      _ = ((U - (n : ℝ) ^ 2) * U ^ n) * G := by ring
      _ ≤ (U * A ^ n) * G := mul_le_mul_of_nonneg_right hb hG
      _ = U * (A ^ n * G) := by ring
      _ ≤ U * (U ^ n * S) := mul_le_mul_of_nonneg_left hl hU.le
      _ = _ := by ring
  have hright : (U - (n : ℝ) ^ 2) * S ≤ U * G := by
    apply (mul_le_mul_iff_right₀ hP).mp
    calc
      _ = ((U - (n : ℝ) ^ 2) * U ^ n) * S := by ring
      _ ≤ (U * A ^ n) * S := mul_le_mul_of_nonneg_right hb hS
      _ = U * (A ^ n * S) := by ring
      _ ≤ U * (U ^ n * G) := mul_le_mul_of_nonneg_left hu hU.le
      _ = _ := by ring
  change U * (G - S) ≤ (n : ℝ) ^ 2 * G ∧
    (U - (n : ℝ) ^ 2) * (S - G) ≤ (n : ℝ) ^ 2 * G
  constructor <;> nlinarith only [hleft, hright]

theorem finiteWeilCanonicalCluster_relative_mass_error (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    ((k + 2 : ℕ) : ℝ) *
        |finiteWeilAbsMass (finiteWeilCanonicalCluster r k) - finiteWeilArithmeticMass r| ≤
      2 * ((r + 1 : ℕ) : ℝ) ^ 2 * finiteWeilArithmeticMass r := by
  let A : ℝ := ((k + 2 : ℕ) : ℝ)
  let U : ℝ := ((k + r + 3 : ℕ) : ℝ)
  let n := r + 1
  let G := finiteWeilArithmeticMass r
  let S := finiteWeilAbsMass (finiteWeilCanonicalCluster r k)
  have hAU : A ≤ U := by dsimp [A, U]; exact_mod_cast (show k + 2 ≤ k + r + 3 by omega)
  have hG : 0 ≤ G := by dsimp [G]; linarith only [finiteWeilArithmeticMass_ge_two r]
  have hdelta : 0 ≤ (n : ℝ) ^ 2 * G := mul_nonneg (sq_nonneg _) hG
  obtain ⟨hl, hu⟩ := finiteWeilCanonicalCluster_mass_error_bounds r k
  change U * (G - S) ≤ (n : ℝ) ^ 2 * G at hl
  change (U - (n : ℝ) ^ 2) * (S - G) ≤ (n : ℝ) ^ 2 * G at hu
  change 2 * (n : ℝ) ^ 2 ≤ A at hwidth
  change A * |S - G| ≤ 2 * (n : ℝ) ^ 2 * G
  by_cases h : G ≤ S
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have hc := mul_le_mul_of_nonneg_right
      (show A ≤ 2 * (U - (n : ℝ) ^ 2) by linarith only [hAU, hwidth])
      (sub_nonneg.mpr h)
    nlinarith only [hc, hu]
  · have hSG : S ≤ G := le_of_not_ge h
    rw [abs_of_nonpos (sub_nonpos.mpr hSG)]
    have hc := mul_le_mul_of_nonneg_right hAU (sub_nonneg.mpr hSG)
    nlinarith only [hc, hl, hdelta]

/-- Relative error is controlled by the ratio of squared order to cluster start. -/
theorem finiteWeilCanonicalCluster_relative_mass_ratio (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    |finiteWeilAbsMass (finiteWeilCanonicalCluster r k) / finiteWeilArithmeticMass r - 1| ≤
      2 * ((r + 1 : ℕ) : ℝ) ^ 2 / ((k + 2 : ℕ) : ℝ) := by
  let G := finiteWeilArithmeticMass r
  let S := finiteWeilAbsMass (finiteWeilCanonicalCluster r k)
  let A : ℝ := ((k + 2 : ℕ) : ℝ)
  have hA : 0 < A := by dsimp [A]; positivity
  have hG : 0 < G := by dsimp [G]; linarith only [finiteWeilArithmeticMass_ge_two r]
  have hc := finiteWeilCanonicalCluster_relative_mass_error r k hwidth
  change A * |S - G| ≤ 2 * ((r + 1 : ℕ) : ℝ) ^ 2 * G at hc
  change |S / G - 1| ≤ 2 * ((r + 1 : ℕ) : ℝ) ^ 2 / A
  rw [show S / G - 1 = (S - G) / G by rw [sub_div, div_self hG.ne'],
    abs_div, abs_of_pos hG]
  apply (div_le_iff₀ hG).mpr
  apply (mul_le_mul_iff_right₀ hA).mp
  calc
    _ ≤ 2 * ((r + 1 : ℕ) : ℝ) ^ 2 * G := hc
    _ = _ := by field_simp

end RHTower
