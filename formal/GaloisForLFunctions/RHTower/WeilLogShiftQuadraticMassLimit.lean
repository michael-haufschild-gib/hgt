import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticConcentrationBound
import GaloisForLFunctions.RHTower.WeilLogShiftStandardMassLimit

/-! Quadratic starts, with arbitrary nonnegative offsets, have the arithmetic mass asymptotic. -/

open Filter Topology
noncomputable section
namespace RHTower

theorem tendsto_finiteWeilArithmeticMass_div_order :
    Tendsto (fun r : ℕ => finiteWeilArithmeticMass r / ((r + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
  have hi : Tendsto (fun r : ℕ => (((r + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hs : Tendsto (fun r : ℕ => (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa only [Real.sqrt_inv, Real.sqrt_zero] using hi.sqrt
  have h := tendsto_finiteWeilArithmeticMass_div_sqrt_order.mul hs
  simp only [mul_zero] at h
  convert h using 1
  funext r
  have hn : 0 < ((r + 1 : ℕ) : ℝ) := by positivity
  have hs0 := Real.sqrt_pos.mpr hn
  have hsq := Real.sq_sqrt hn.le
  field_simp
  nlinarith only [congrArg (fun x => finiteWeilArithmeticMass r * x) hsq]

theorem tendsto_finiteWeil_quadratic_concentration_error :
    Tendsto (fun r : ℕ =>
      Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ) +
      Real.sqrt (((((r + 1 : ℕ) : ℝ) + 1) / 2) * finiteWeilArithmeticMass r) /
        ((r + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hi : Tendsto (fun r : ℕ => (((r + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hfirst := ((((tendsto_const_nhds (x := (1 : ℝ))).add hi).mul hi).div_const (2 : ℝ)).sqrt
  have hsecond := ((((tendsto_const_nhds (x := (1 : ℝ))).add hi).mul
    tendsto_finiteWeilArithmeticMass_div_order).div_const (2 : ℝ)).sqrt
  have h : Tendsto (fun r : ℕ =>
      Real.sqrt ((1 + (((r + 1 : ℕ) : ℝ))⁻¹) * (((r + 1 : ℕ) : ℝ))⁻¹ / 2) +
      Real.sqrt ((1 + (((r + 1 : ℕ) : ℝ))⁻¹) *
        (finiteWeilArithmeticMass r / ((r + 1 : ℕ) : ℝ)) / 2)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_div, Real.sqrt_zero, add_zero] using hfirst.add hsecond
  convert h using 1
  funext r
  have hn : 0 < ((r + 1 : ℕ) : ℝ) := by positivity
  have hG : 0 < finiteWeilArithmeticMass r :=
    lt_of_lt_of_le (by norm_num) (finiteWeilArithmeticMass_ge_two r)
  have key (x : ℝ) (hx : 0 ≤ x) :
      Real.sqrt x / ((r + 1 : ℕ) : ℝ) =
        Real.sqrt (x / (((r + 1 : ℕ) : ℝ)) ^ 2) := by
    rw [Real.sqrt_div hx, Real.sqrt_sq hn.le]
  rw [key _ (by positivity), key _ (by positivity)]
  congr 2 <;> field_simp

/-- No condition on the offset sequence is needed. -/
theorem tendsto_finiteWeilCanonicalCluster_quadratic_mass_ratio (t : ℕ → ℕ) :
    Tendsto (fun r : ℕ =>
      finiteWeilAbsMass (finiteWeilCanonicalCluster r (2 * (r + 1) ^ 2 + t r)) /
        finiteWeilArithmeticMass r) atTop (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun r => abs_nonneg _)
    (fun r => finiteWeilCanonicalCluster_quadratic_concentration_error r _ ?_)
    tendsto_finiteWeil_quadratic_concentration_error
  push_cast
  have ht : (0 : ℝ) ≤ (t r : ℝ) := Nat.cast_nonneg _
  nlinarith only [ht]

/-- Quadratic logarithmic grids have the exact arithmetic square-root constant. -/
theorem tendsto_finiteWeilCanonicalCluster_quadratic_mass_div_sqrt_order (t : ℕ → ℕ) :
    Tendsto (fun r : ℕ =>
      finiteWeilAbsMass (finiteWeilCanonicalCluster r (2 * (r + 1) ^ 2 + t r)) /
        Real.sqrt ((r + 1 : ℕ) : ℝ)) atTop (𝓝 (Real.sqrt (Real.pi / 2))) := by
  have h := (tendsto_finiteWeilCanonicalCluster_quadratic_mass_ratio t).mul
    tendsto_finiteWeilArithmeticMass_div_sqrt_order
  rw [one_mul] at h
  convert h using 1
  funext r
  have hG : 0 < finiteWeilArithmeticMass r :=
    lt_of_lt_of_le (by norm_num) (finiteWeilArithmeticMass_ge_two r)
  field_simp

end RHTower
