import GaloisForLFunctions.RHTower.WeilLogShiftCubicMassLimit

/-! Standard order normalization removes the finite parity correction from nodal mass. -/

open Filter Topology
noncomputable section
namespace RHTower

theorem finiteWeil_halfOrder_ratio_error (r : ℕ) :
    |((r / 2 + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) : ℝ) - 1 / 2| ≤
      (1 / 2 : ℝ) / ((r + 1 : ℕ) : ℝ) := by
  let m : ℝ := ((r / 2 + 1 : ℕ) : ℝ)
  let n : ℝ := ((r + 1 : ℕ) : ℝ)
  have hn : 0 < n := by dsimp [n]; positivity
  have hlo : n ≤ 2 * m := by
    dsimp [n, m]
    exact_mod_cast (show r + 1 ≤ 2 * (r / 2 + 1) by omega)
  have hhi : 2 * m ≤ n + 1 := by
    dsimp [n, m]
    exact_mod_cast (show 2 * (r / 2 + 1) ≤ (r + 1) + 1 by omega)
  have hhalf : (1 / 2 : ℝ) ≤ m / n := (le_div_iff₀ hn).mpr (by linarith only [hlo])
  change |m / n - 1 / 2| ≤ (1 / 2 : ℝ) / n
  rw [abs_of_nonneg (sub_nonneg.mpr hhalf)]
  apply (mul_le_mul_iff_right₀ hn).mp
  have heq : n * (m / n - 1 / 2) = m - n / 2 := by
    field_simp
  have hcancel : n * ((1 / 2 : ℝ) / n) = 1 / 2 := by field_simp
  rw [heq, hcancel]
  linarith only [hhi]

theorem tendsto_finiteWeil_halfOrder_ratio :
    Tendsto (fun r : ℕ => ((r / 2 + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) : ℝ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  exact squeeze_zero (fun r => abs_nonneg _) finiteWeil_halfOrder_ratio_error
    ((tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ)).comp (tendsto_add_atTop_nat 1))

/-- The parity correction is an exact scalar change of normalization. -/
theorem finiteWeil_sqrt_halfOrder_normalization (r : ℕ) (x : ℝ) :
    x / Real.sqrt ((r + 1 : ℕ) : ℝ) =
      (x / Real.sqrt ((r / 2 + 1 : ℕ) : ℝ)) *
        Real.sqrt (((r / 2 + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) : ℝ)) := by
  have hm : 0 < Real.sqrt ((r / 2 + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hn : 0 < Real.sqrt ((r + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  rw [Real.sqrt_div (by positivity)]
  field_simp

theorem tendsto_finiteWeilArithmeticMass_div_sqrt_order :
    Tendsto (fun r : ℕ => finiteWeilArithmeticMass r / Real.sqrt ((r + 1 : ℕ) : ℝ))
      atTop (𝓝 (Real.sqrt (Real.pi / 2))) := by
  have h := tendsto_finiteWeilArithmeticMass_div_sqrt_halfOrder.mul
    tendsto_finiteWeil_halfOrder_ratio.sqrt
  rw [← Real.sqrt_mul Real.pi_pos.le, show Real.pi * (1 / 2) = Real.pi / 2 by ring] at h
  convert h using 1
  funext r
  exact finiteWeil_sqrt_halfOrder_normalization r (finiteWeilArithmeticMass r)

/-- The cubic logarithmic cluster has the standard square-root constant sqrt(pi/2). -/
theorem tendsto_finiteWeilCanonicalCluster_cubic_mass_div_sqrt_order :
    Tendsto (fun r : ℕ =>
      finiteWeilAbsMass (finiteWeilCanonicalCluster r (finiteWeilCubicClusterStart r)) /
        Real.sqrt ((r + 1 : ℕ) : ℝ)) atTop (𝓝 (Real.sqrt (Real.pi / 2))) := by
  have h := tendsto_finiteWeilCanonicalCluster_cubic_mass_div_sqrt_halfOrder.mul
    tendsto_finiteWeil_halfOrder_ratio.sqrt
  rw [← Real.sqrt_mul Real.pi_pos.le, show Real.pi * (1 / 2) = Real.pi / 2 by ring] at h
  convert h using 1
  funext r
  exact finiteWeil_sqrt_halfOrder_normalization r _

end RHTower
