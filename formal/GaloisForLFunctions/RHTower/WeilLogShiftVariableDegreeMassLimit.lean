import GaloisForLFunctions.RHTower.WeilLogShiftPolynomialMassLimit

/-! The polynomial degree may vary arbitrarily without changing the mass limit. -/

open Filter Topology
noncomputable section
namespace RHTower

theorem tendsto_finiteWeilCanonicalCluster_variable_degree_mass_ratio (d : ℕ → ℕ) :
    Tendsto (fun r : ℕ =>
      finiteWeilAbsMass (finiteWeilCanonicalCluster r (finiteWeilPolynomialClusterStart (d r) r)) /
        finiteWeilArithmeticMass r) atTop (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  exact squeeze_zero (fun r => abs_nonneg _)
    (fun r => finiteWeilCanonicalCluster_polynomial_mass_ratio_error (d r) r)
    ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1))

/-- No growth or regularity premise on the degree function is needed. -/
theorem tendsto_finiteWeilCanonicalCluster_variable_degree_mass_div_sqrt_order (d : ℕ → ℕ) :
    Tendsto (fun r : ℕ =>
      finiteWeilAbsMass (finiteWeilCanonicalCluster r (finiteWeilPolynomialClusterStart (d r) r)) /
        Real.sqrt ((r + 1 : ℕ) : ℝ)) atTop (𝓝 (Real.sqrt (Real.pi / 2))) := by
  have h := (tendsto_finiteWeilCanonicalCluster_variable_degree_mass_ratio d).mul
    tendsto_finiteWeilArithmeticMass_div_sqrt_order
  rw [one_mul] at h
  convert h using 1
  funext r
  have hG : 0 < finiteWeilArithmeticMass r := by
    linarith only [finiteWeilArithmeticMass_ge_two r]
  have hn : 0 < Real.sqrt ((r + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  field_simp

end RHTower
