import GaloisForLFunctions.RHTower.WeilLogShiftPhaseBounds

/-! The scalar binomial Gaussian limit follows from the exact sinc identity. -/

open Filter Topology

namespace RHTower

theorem tendsto_finiteWeil_inverse_sqrt :
    Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

theorem finiteWeil_cosine_scaled_identity (n : ℕ) (z : ℝ) (hn : 0 < n) :
    (n : ℝ) * (Real.cos (z / Real.sqrt (n : ℝ)) - 1) =
      -(z ^ 2 / 2) * Real.sinc (z / (2 * Real.sqrt (n : ℝ))) ^ 2 := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hsin (x : ℝ) : Real.sin x = x * Real.sinc x := by
    by_cases hx : x = 0
    · simp [hx]
    · rw [Real.sinc_of_ne_zero hx]
      field_simp
  rw [show z / Real.sqrt (n : ℝ) = 2 * (z / (2 * Real.sqrt (n : ℝ))) by ring,
    Real.cos_two_mul_eq_one_sub, hsin]
  field_simp
  rw [hs2]
  ring

theorem tendsto_finiteWeil_cosine_gaussian (z : ℝ) :
    Tendsto (fun n : ℕ => Real.cos (z / Real.sqrt (n : ℝ)) ^ n)
      atTop (𝓝 (Real.exp (-(z ^ 2 / 2)))) := by
  have harg : Tendsto (fun n : ℕ => z / (2 * Real.sqrt (n : ℝ))) atTop (𝓝 0) := by
    have h := tendsto_finiteWeil_inverse_sqrt.const_mul (z / 2)
    convert h using 1
    · funext n
      ring
    · simp
  have hs := (Real.continuous_sinc.tendsto 0).comp harg
  simp only [Real.sinc_zero] at hs
  have hbase := (hs.mul hs).const_mul (-(z ^ 2 / 2))
  simp only [mul_one] at hbase
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) * (Real.cos (z / Real.sqrt (n : ℝ)) - 1))
      atTop (𝓝 (-(z ^ 2 / 2))) := by
    apply hbase.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    simpa only [pow_two, Function.comp_apply] using (finiteWeil_cosine_scaled_identity n z (by omega)).symm
  have h := Real.tendsto_one_add_pow_exp_of_tendsto hlim
  convert h using 1
  funext n
  congr 1
  ring

theorem tendsto_finiteWeil_inverse_sqrt_succ :
    Tendsto (fun r : ℕ => (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_finiteWeil_inverse_sqrt.comp
    (tendsto_atTop_mono (fun r : ℕ => Nat.le_succ r) tendsto_id)

end RHTower
