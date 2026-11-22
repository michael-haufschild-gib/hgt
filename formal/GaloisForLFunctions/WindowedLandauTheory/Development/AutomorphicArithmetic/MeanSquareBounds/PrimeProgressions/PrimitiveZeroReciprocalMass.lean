import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ZeroEndpointDistances
import GaloisForLFunctions.ShortIntervalPrimesInProgressions.SiegelWalfisz

/-! The reciprocal mass of the primitive zero kernel grows at most polynomially in the conductor. -/

open Complex
open GaloisForLFunctions.ShortIntervalPrimesInProgressions

noncomputable section

namespace QH.PrimeProgressions

/-- Summation over all zeros is bounded after factoring out the uniform endpoint distance. -/
theorem primitive_zero_reciprocal_mass :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → χ.IsPrimitive →
      Summable (fun q : LZero χ => 1 / (‖q.point‖ * ‖1 - q.point‖)) ∧
      ∑' q : LZero χ, 1 / (‖q.point‖ * ‖1 - q.point‖) ≤ C * (N : ℝ) ^ 3 := by
  obtain ⟨c, hc, hdist⟩ := primitive_zero_endpoint_distances
  refine ⟨640 * (2 * Real.log 4 + 8 * c ^ 2) / c ^ 2, by positivity, ?_⟩
  intro N _ χ hχ hp
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hN₀ : (0 : ℝ) < N := zero_lt_one.trans_le hN
  let Y : ℝ := (c / N) ^ 2
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hYle : Y ≤ c ^ 2 := by
    dsimp [Y]
    exact pow_le_pow_left₀ (by positivity) (div_le_self hc.le hN) 2
  have hweight (q : LZero χ) : (1 / (‖q.point‖ * ‖1 - q.point‖)) =
      Y⁻¹ * RHTower.zeroShortWeight 1 Y q.point := by
    obtain ⟨h₀, h₁⟩ := zero_re_mem hχ hp q
    obtain ⟨ha, hb⟩ := hdist N χ q.point hχ hp (LFunction_point_eq_zero hχ hp q) h₀ h₁
    have hproduct : Y ≤ ‖q.point‖ * ‖1 - q.point‖ := by
      rw [show Y = (c / (N : ℝ)) * (c / (N : ℝ)) by simp [Y, pow_two]]
      exact mul_le_mul ha hb (by positivity) (norm_nonneg _)
    have hproduct₀ : 0 < ‖q.point‖ * ‖1 - q.point‖ := hY.trans_le hproduct
    unfold RHTower.zeroShortWeight
    rw [Real.one_rpow, one_mul, min_eq_right ((div_le_one hproduct₀).mpr hproduct)]
    rw [← mul_div_assoc, inv_mul_cancel₀ hY.ne']
  simp_rw [hweight]
  have hs := summable_zeroShortWeight hχ hp (x := 1) le_rfl hY.le
  refine ⟨hs.mul_left _, ?_⟩
  rw [tsum_mul_left]
  have hmass := tsum_zeroShortWeight_le_uniform hχ hp (x := 1) (E := 1)
    le_rfl hY.le zero_le_one (T := 1) le_rfl (fun _ _ => by simp)
  have hmass' : ∑' q : LZero χ, RHTower.zeroShortWeight 1 Y q.point ≤
      4 * localCountConst N * (2 * Real.log 4 + 8 * Y) := by
    norm_num at hmass ⊢
    exact hmass
  have hcnt : localCountConst N ≤ 160 * N :=
    (localCountConst_le (NeZero.pos N)).trans (by
      linarith [Real.log_le_sub_one_of_pos hN₀])
  have hbound : ∑' q : LZero χ, RHTower.zeroShortWeight 1 Y q.point ≤
      640 * (N : ℝ) * (2 * Real.log 4 + 8 * c ^ 2) := by
    refine hmass'.trans ?_
    have hlog : 0 ≤ Real.log 4 := by positivity
    have ha : 4 * localCountConst N ≤ 640 * (N : ℝ) := by linarith
    have hb : 2 * Real.log 4 + 8 * Y ≤ 2 * Real.log 4 + 8 * c ^ 2 := by linarith
    exact mul_le_mul ha hb (by positivity) (by positivity)
  refine (mul_le_mul_of_nonneg_left hbound (by positivity)).trans_eq ?_
  dsimp [Y]
  field_simp

end QH.PrimeProgressions
