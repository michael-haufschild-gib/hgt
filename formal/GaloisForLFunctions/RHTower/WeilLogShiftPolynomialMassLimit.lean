import GaloisForLFunctions.RHTower.WeilLogShiftStandardMassLimit

/-! Every polynomial start of degree at least three has the same normalized mass limit. -/

open Filter Topology
noncomputable section
namespace RHTower

def finiteWeilPolynomialClusterStart (d r : ℕ) : ℕ := 2 * (r + 1) ^ (d + 3)

theorem finiteWeilPolynomialClusterStart_ge_cubic (d r : ℕ) :
    finiteWeilCubicClusterStart r ≤ finiteWeilPolynomialClusterStart d r := by
  unfold finiteWeilCubicClusterStart finiteWeilPolynomialClusterStart
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (show 1 ≤ r + 1 by omega) (show 3 ≤ d + 3 by omega)) (by omega)

/-- The cubic formula can be replaced by a lower bound on the start. -/
theorem finiteWeilCanonicalCluster_mass_ratio_error_of_cubic_start (r k : ℕ)
    (hstart : finiteWeilCubicClusterStart r ≤ k) :
    |finiteWeilAbsMass (finiteWeilCanonicalCluster r k) / finiteWeilArithmeticMass r - 1| ≤
      1 / ((r + 1 : ℕ) : ℝ) := by
  have hstart' : ((finiteWeilCubicClusterStart r + 2 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show finiteWeilCubicClusterStart r + 2 ≤ k + 2 by omega)
  have hwidth := (finiteWeilCubicClusterStart_width r).trans hstart'
  apply (finiteWeilCanonicalCluster_relative_mass_ratio r k hwidth).trans
  have hA : 0 < ((k + 2 : ℕ) : ℝ) := by positivity
  have hn : 0 < ((r + 1 : ℕ) : ℝ) := by positivity
  apply (div_le_iff₀ hA).mpr
  apply (mul_le_mul_iff_right₀ hn).mp
  calc
    _ = 2 * ((r + 1 : ℕ) : ℝ) ^ 3 := by ring
    _ ≤ ((finiteWeilCubicClusterStart r + 2 : ℕ) : ℝ) := by
      dsimp [finiteWeilCubicClusterStart]
      push_cast
      linarith
    _ ≤ ((k + 2 : ℕ) : ℝ) := hstart'
    _ = _ := by field_simp

/-- The reciprocal-order error is uniform in the polynomial degree. -/
theorem finiteWeilCanonicalCluster_polynomial_mass_ratio_error (d r : ℕ) :
    |finiteWeilAbsMass (finiteWeilCanonicalCluster r (finiteWeilPolynomialClusterStart d r)) /
        finiteWeilArithmeticMass r - 1| ≤ 1 / ((r + 1 : ℕ) : ℝ) :=
  finiteWeilCanonicalCluster_mass_ratio_error_of_cubic_start r _
    (finiteWeilPolynomialClusterStart_ge_cubic d r)

theorem tendsto_finiteWeilCanonicalCluster_polynomial_mass_ratio (d : ℕ) :
    Tendsto (fun r : ℕ =>
      finiteWeilAbsMass (finiteWeilCanonicalCluster r (finiteWeilPolynomialClusterStart d r)) /
        finiteWeilArithmeticMass r) atTop (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  exact squeeze_zero (fun r => abs_nonneg _)
    (finiteWeilCanonicalCluster_polynomial_mass_ratio_error d)
    ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1))

/-- Every degree at least three gives the same explicit square-root mass constant. -/
theorem tendsto_finiteWeilCanonicalCluster_polynomial_mass_div_sqrt_order (d : ℕ) :
    Tendsto (fun r : ℕ =>
      finiteWeilAbsMass (finiteWeilCanonicalCluster r (finiteWeilPolynomialClusterStart d r)) /
        Real.sqrt ((r + 1 : ℕ) : ℝ)) atTop (𝓝 (Real.sqrt (Real.pi / 2))) := by
  have h := (tendsto_finiteWeilCanonicalCluster_polynomial_mass_ratio d).mul
    tendsto_finiteWeilArithmeticMass_div_sqrt_order
  rw [one_mul] at h
  convert h using 1
  funext r
  have hG : 0 < finiteWeilArithmeticMass r := by
    linarith only [finiteWeilArithmeticMass_ge_two r]
  have hn : 0 < Real.sqrt ((r + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  field_simp

end RHTower
