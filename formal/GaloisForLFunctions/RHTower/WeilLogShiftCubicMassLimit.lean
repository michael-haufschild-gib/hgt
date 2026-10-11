import GaloisForLFunctions.RHTower.WeilLogShiftRelativeMass

/-! An explicit cubic cluster sequence inherits the exact central-binomial mass limit. -/

open Filter Topology
noncomputable section
namespace RHTower
open GaloisForLFunctions.HTGeometry

def finiteWeilCubicClusterStart (r : ℕ) : ℕ := 2 * (r + 1) ^ 3

theorem finiteWeilCubicClusterStart_width (r : ℕ) :
    2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((finiteWeilCubicClusterStart r + 2 : ℕ) : ℝ) := by
  have hn : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ r + 1 by omega)
  have hmul := mul_le_mul_of_nonneg_right hn (sq_nonneg (((r + 1 : ℕ) : ℝ)))
  dsimp [finiteWeilCubicClusterStart]
  push_cast at hmul ⊢
  nlinarith only [hmul]

/-- The concrete cubic sequence has relative error at most the reciprocal order. -/
theorem finiteWeilCanonicalCluster_cubic_mass_ratio_error (r : ℕ) :
    |finiteWeilAbsMass (finiteWeilCanonicalCluster r (finiteWeilCubicClusterStart r)) /
        finiteWeilArithmeticMass r - 1| ≤ 1 / ((r + 1 : ℕ) : ℝ) := by
  have hc := finiteWeilCanonicalCluster_relative_mass_ratio r (finiteWeilCubicClusterStart r)
    (finiteWeilCubicClusterStart_width r)
  apply hc.trans
  have hA : 0 < ((finiteWeilCubicClusterStart r + 2 : ℕ) : ℝ) := by positivity
  have hn : 0 < ((r + 1 : ℕ) : ℝ) := by positivity
  apply (div_le_iff₀ hA).mpr
  apply (mul_le_mul_iff_right₀ hn).mp
  calc
    _ = 2 * ((r + 1 : ℕ) : ℝ) ^ 3 := by ring
    _ ≤ ((finiteWeilCubicClusterStart r + 2 : ℕ) : ℝ) := by
      dsimp [finiteWeilCubicClusterStart]
      push_cast
      linarith
    _ = _ := by field_simp

theorem tendsto_finiteWeilCanonicalCluster_cubic_mass_ratio :
    Tendsto (fun r : ℕ =>
      finiteWeilAbsMass (finiteWeilCanonicalCluster r (finiteWeilCubicClusterStart r)) /
        finiteWeilArithmeticMass r) atTop (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  exact squeeze_zero (fun r => abs_nonneg _)
    finiteWeilCanonicalCluster_cubic_mass_ratio_error
    ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1))

/-- Exact parity normalization exposes the existing Wallis limit at every order. -/
theorem tendsto_finiteWeilArithmeticMass_div_sqrt_halfOrder :
    Tendsto (fun r : ℕ => finiteWeilArithmeticMass r / Real.sqrt ((r / 2 + 1 : ℕ) : ℝ))
      atTop (𝓝 (Real.sqrt Real.pi)) := by
  have hm : Tendsto (fun r : ℕ => r / 2 + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (2 * b)] with r hr
    omega
  have hW : Tendsto (fun r : ℕ =>
      Real.sqrt ((r / 2 + 1 : ℕ) : ℝ) * normalizedCentralBinom (r / 2 + 1))
      atTop (𝓝 (1 / Real.sqrt Real.pi)) :=
    tendsto_sqrtNat_mul_normalizedCentralBinom.comp hm
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hi := hW.inv₀ (show (1 / Real.sqrt Real.pi : ℝ) ≠ 0 by positivity)
  have hlim : Tendsto (fun r : ℕ =>
      (Real.sqrt ((r / 2 + 1 : ℕ) : ℝ) * normalizedCentralBinom (r / 2 + 1))⁻¹)
      atTop (𝓝 (Real.sqrt Real.pi)) := by
    simpa only [one_div, inv_inv] using hi
  convert hlim using 1
  funext r
  have hc : 0 < normalizedCentralBinom (r / 2 + 1) := by
    unfold normalizedCentralBinom
    exact div_pos (by exact_mod_cast Nat.centralBinom_pos (r / 2 + 1)) (by positivity)
  have hs : 0 < Real.sqrt ((r / 2 + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  calc
    _ = (finiteWeilArithmeticMass r * normalizedCentralBinom (r / 2 + 1)) /
        (Real.sqrt ((r / 2 + 1 : ℕ) : ℝ) * normalizedCentralBinom (r / 2 + 1)) := by
      field_simp
    _ = _ := by rw [finiteWeilArithmeticMass_mul_normalizedCentralBinom, one_div]

/-- A concrete logarithmic cluster has the exact square-root mass constant. -/
theorem tendsto_finiteWeilCanonicalCluster_cubic_mass_div_sqrt_halfOrder :
    Tendsto (fun r : ℕ =>
      finiteWeilAbsMass (finiteWeilCanonicalCluster r (finiteWeilCubicClusterStart r)) /
        Real.sqrt ((r / 2 + 1 : ℕ) : ℝ)) atTop (𝓝 (Real.sqrt Real.pi)) := by
  have h := tendsto_finiteWeilCanonicalCluster_cubic_mass_ratio.mul
    tendsto_finiteWeilArithmeticMass_div_sqrt_halfOrder
  rw [one_mul] at h
  convert h using 1
  funext r
  have hG : 0 < finiteWeilArithmeticMass r := by
    linarith only [finiteWeilArithmeticMass_ge_two r]
  have hs : 0 < Real.sqrt ((r / 2 + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  field_simp

end RHTower
