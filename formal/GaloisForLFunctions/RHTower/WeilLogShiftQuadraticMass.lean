import GaloisForLFunctions.RHTower.WeilLogShiftArithmeticSqrt

/-! Quadratic cluster starts keep logarithmic nodal-mass distortion uniformly bounded. -/

noncomputable section
namespace RHTower

/-- Bernoulli's inequality controls the accumulated distortion of all nodal gaps. -/
theorem finiteWeil_quadratic_power_distortion (n : ℕ) (A : ℝ) (hA : 0 < A)
    (hwidth : 2 * (n : ℝ) ^ 2 ≤ A) :
    (A + n) ^ n ≤ 2 * A ^ n := by
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hU : 0 < A + n := by positivity
  have hfrac : (n : ℝ) / (A + n) ≤ 1 := (div_le_iff₀ hU).mpr (by linarith)
  have hb := one_add_mul_le_pow (a := -((n : ℝ) / (A + n))) (by linarith) n
  have hbase : 1 + -((n : ℝ) / (A + n)) = A / (A + n) := by
    field_simp
    ring
  rw [hbase, div_pow] at hb
  have hratio : (n : ℝ) ^ 2 / (A + n) ≤ 1 / 2 :=
    (div_le_iff₀ hU).mpr (by nlinarith only [hwidth, hn])
  have hhalf : (1 / 2 : ℝ) ≤ 1 + (n : ℝ) * -((n : ℝ) / (A + n)) := by
    have heq : 1 + (n : ℝ) * -((n : ℝ) / (A + n)) =
        1 - (n : ℝ) ^ 2 / (A + n) := by ring
    rw [heq]
    linarith only [hratio]
  have hcross := (le_div_iff₀ (pow_pos hU n)).mp (hhalf.trans hb)
  linarith only [hcross]

theorem finiteWeilCanonicalCluster_quadratic_mass_comparison (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    finiteWeilArithmeticMass r ≤ 2 * finiteWeilAbsMass (finiteWeilCanonicalCluster r k) ∧
    finiteWeilAbsMass (finiteWeilCanonicalCluster r k) ≤ 2 * finiteWeilArithmeticMass r := by
  let A : ℝ := ((k + 2 : ℕ) : ℝ) ^ (r + 1)
  let U : ℝ := ((k + r + 3 : ℕ) : ℝ) ^ (r + 1)
  let G := finiteWeilArithmeticMass r
  let S := finiteWeilAbsMass (finiteWeilCanonicalCluster r k)
  have hA : 0 < A := by dsimp [A]; positivity
  have hG : 0 ≤ G := by dsimp [G]; linarith only [finiteWeilArithmeticMass_ge_two r]
  have hS : 0 ≤ S := by
    dsimp [S, finiteWeilAbsMass]
    exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hU : U ≤ 2 * A := by
    have h := finiteWeil_quadratic_power_distortion (r + 1) ((k + 2 : ℕ) : ℝ)
      (by positivity) hwidth
    have heq : ((k + 2 : ℕ) : ℝ) + (r + 1 : ℕ) = ((k + r + 3 : ℕ) : ℝ) := by
      push_cast
      ring
    simpa only [heq] using h
  obtain ⟨hl, hu⟩ := finiteWeilCanonicalCluster_arithmetic_mass_comparison r k
  change A * G ≤ U * S at hl
  change A * S ≤ U * G at hu
  constructor
  · have h := hl.trans (mul_le_mul_of_nonneg_right hU hS)
    have hc : A * G ≤ A * (2 * S) := by nlinarith only [h]
    exact (mul_le_mul_iff_right₀ hA).mp hc
  · have h := hu.trans (mul_le_mul_of_nonneg_right hU hG)
    have hc : A * S ≤ A * (2 * G) := by nlinarith only [h]
    exact (mul_le_mul_iff_right₀ hA).mp hc

theorem finiteWeilCanonicalCluster_quadratic_sqrt_lower (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    Real.sqrt ((r + 2 : ℕ) : ℝ) ≤
      2 * finiteWeilAbsMass (finiteWeilCanonicalCluster r k) :=
  (finiteWeilArithmeticMass_sqrt_lower r).trans
    (finiteWeilCanonicalCluster_quadratic_mass_comparison r k hwidth).1

/-- One fixed quadratic width implies both the analytic and distortion widths. -/
theorem finiteWeil_quadratic_width (L : ℝ) (hL : 1 ≤ L) (r k : ℕ)
    (hwidth : (4 * L + 2) * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    4 * L * ((r + 1 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) ∧
    2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ) := by
  have hn : 1 ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ r + 1 by omega)
  have hsq : ((r + 1 : ℕ) : ℝ) ≤ ((r + 1 : ℕ) : ℝ) ^ 2 := by nlinarith only [hn]
  have hlinear := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4 * L by linarith)
  have hquad := mul_le_mul_of_nonneg_right (show 2 ≤ 4 * L + 2 by linarith)
    (sq_nonneg (((r + 1 : ℕ) : ℝ)))
  constructor <;> nlinarith only [hwidth, hlinear, hquad, sq_nonneg (((r + 1 : ℕ) : ℝ))]

end RHTower
