import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Data.Nat.Log

/-! # Comparing a prefix size to its dyadic field scale -/
open Filter
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Largest j for which a prefix of n+2 sites contains 2 (2ʲ)⁴⁸ sites. -/
def isolatedFieldScaleIndex (n : ℕ) : ℕ := Nat.log (2^48) ((n+2)/2)

theorem tendsto_isolatedFieldScaleIndex : Tendsto isolatedFieldScaleIndex atTop atTop := by
  rw [tendsto_atTop]
  intro m
  refine eventually_atTop.2 ⟨2*(2^48)^m,fun n hn => ?_⟩
  apply Nat.le_log_of_pow_le (by decide : 1 < 2^48)
  omega

/-- At the selected scale, k⁴⁸ pairs fit, k²⁴ controls the square root of
the size, and times up to one quarter of its 48th root are at most k. -/
theorem isolatedFieldScale_bounds (n : ℕ) :
    let k : ℕ := 2^isolatedFieldScaleIndex n
    2*k^48 ≤ n+2 ∧ Real.sqrt ((n+2:ℕ):ℝ) ≤ 2^25*(k:ℝ)^24 ∧
      ((n+2:ℕ):ℝ)^((48:ℝ)⁻¹)/4 ≤ k := by
  let j := isolatedFieldScaleIndex n
  let k : ℕ := 2^j
  have he : (2^48)^j = k^48 := by dsimp [k]; rw [← pow_mul,← pow_mul,Nat.mul_comm 48 j]
  have hlo := Nat.pow_log_le_self (2^48) (show (n+2)/2 ≠ 0 by omega)
  have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < 2^48) ((n+2)/2)
  change (2^48)^j ≤ (n+2)/2 at hlo
  change (n+2)/2 < (2^48)^(j+1) at hhi
  rw [he] at hlo
  rw [pow_succ,he] at hhi
  have hN : ((n+2:ℕ):ℝ) ≤ 2^49*(k:ℝ)^48 := by
    exact_mod_cast (show n+2 ≤ 2^49*k^48 by norm_num at hhi ⊢; omega)
  refine ⟨by change 2*k^48 ≤ n+2; omega,?_,?_⟩
  · apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,hN.trans (by
      rw [mul_pow,← pow_mul]
      norm_num
      linarith only [pow_nonneg (Nat.cast_nonneg k : 0 ≤ (k:ℝ)) 48])⟩
  · have h4 : ((n+2:ℕ):ℝ) ≤ (4*(k:ℝ))^48 := hN.trans (by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
    have hr := Real.rpow_le_rpow (Nat.cast_nonneg _) h4 (by norm_num : 0 ≤ (48:ℝ)⁻¹)
    rw [show (48:ℝ)⁻¹ = ((48:ℕ):ℝ)⁻¹ by norm_num,
      Real.pow_rpow_inv_natCast (by positivity) (by decide)] at hr
    change _ ≤ (k:ℝ)
    linarith only [hr]

end
end GaloisForLFunctions.HTGeometry
