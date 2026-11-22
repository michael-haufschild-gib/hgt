import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.FiniteZeroPackets
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.NearZeroCount
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.PrimitiveNormalizedFormula
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.PrimitiveZeroTruncation
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.TruncatedRampStatement
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ZeroCopyOrders

/-! The conductor-uniform truncated Cesàro formula for a nonprincipal primitive character. -/

open Complex Finset WindowedLandauTheory.HC WindowedLandauTheory.ZeroFreeDirichlet
open GaloisForLFunctions.ShortIntervalPrimesInProgressions

noncomputable section

namespace QH.PrimeProgressions

theorem primitive_truncated_ramp :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → χ.IsPrimitive → ∀ κ T : ℝ, 0 < κ → κ ≤ 1 / 20 → 2 ≤ T →
        TruncatedRamp χ κ T C := by
  obtain ⟨A, hA, hfull⟩ := primitive_normalized_formula
  obtain ⟨B, hB, htail⟩ := primitive_zero_truncation
  obtain ⟨D, hD, hcount⟩ := nonprincipal_near_zero_count
  obtain ⟨E, hE, hmass⟩ := primitive_zero_reciprocal_mass
  refine ⟨3 * A + B + D, by positivity, ?_⟩
  intro N _ χ hχ hp κ T hκ hκ' hT
  let m := analyticOrderNatAt χ.LFunction
  have hfinite : {q : LZero χ | Cutoff κ T q.point}.Finite :=
    (finite_primitive_height hχ hp T).subset fun q hq => hq.2
  obtain ⟨Z, hZ, hm, -, hsum⟩ := finite_zero_packet LZero.point (Cutoff κ T) hfinite m
    (fun ρ hρ _ => primitive_zero_copy_count hχ (by have := hρ.1; linarith))
  have hzeros (ρ : ℂ) : ρ ∈ Z ↔ IsLZero χ ρ ∧ Cutoff κ T ρ := by
    rw [hZ]
    constructor
    · rintro ⟨hρ, q, rfl⟩
      exact ⟨⟨Or.inl hχ, LFunction_point_eq_zero hχ hp q⟩, hρ⟩
    · rintro ⟨hz, hρ⟩
      exact ⟨hρ, primitive_zero_copy_exists hχ (by have := hρ.1; linarith) hz.2⟩
  obtain ⟨K, hK⟩ := hfull N χ hχ hp
  refine ⟨Z, K, hzeros, hm, ?_, ?_⟩
  · intro t
    have h := hcount N χ hχ (Z.filter fun ρ => |ρ.im - t| ≤ 1) t fun ρ hρ => by
      obtain ⟨hρZ, him⟩ := mem_filter.mp hρ
      obtain ⟨hz, hρ⟩ := (hzeros ρ).mp hρZ
      exact ⟨hz.2, by have := hρ.1; linarith, him⟩
    refine h.trans (mul_le_mul_of_nonneg_right (by linarith) ?_)
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
    exact Real.log_nonneg ((show (1 : ℝ) ≤ |t| + 2 by linarith [abs_nonneg t]).trans
      (le_mul_of_one_le_left (by positivity) hN))
  · intro y hy
    have hy₁ : 1 ≤ y := by linarith
    have hs : Summable (fun q : LZero χ => QH.zeroKernel y q.point) := by
      refine Summable.of_norm_bounded (hmass N χ hχ hp).1 (fun q => ?_)
      rw [QH.norm_zeroKernel (by linarith : 0 < y)]
      exact div_le_div_of_nonneg_right
        (Real.rpow_le_one_of_one_le_of_nonpos hy₁ (sub_nonpos.mpr (zero_re_mem hχ hp q).2.le))
        (by positivity)
    let S := ∑ ρ ∈ Z, (m ρ : ℂ) * QH.zeroKernel y ρ
    let W := ∑' q : LZero χ, if Cutoff κ T q.point then 0 else QH.zeroKernel y q.point
    let R := An.sumLamChi χ y / (y : ℂ) - K + S
    have hnorm : ‖R + W‖ ≤ A * (N : ℝ) ^ 3 * (1 + Real.log y) / y := by
      have h := hK y hy
      rw [hsum _ hs, ← add_assoc] at h
      exact h
    have hnormW : ‖W‖ ≤ B * ((N : ℝ) ^ 3 * y ^ (-κ) + Real.log ((N : ℝ) * T) ^ 2 / T) :=
      htail N χ hχ hp y κ T hy₁ hκ hT
    change ‖An.sumLamChi χ y / (y : ℂ) - K - rampMain χ y + S‖ ≤ _
    rw [rampMain, if_neg hχ, sub_zero]
    change ‖R‖ ≤ _
    have hR := (norm_sub_le (R + W) W).trans (add_le_add hnorm hnormW)
    rw [add_sub_cancel_right] at hR
    refine hR.trans ?_
    have hcomp := Real.rpow_le_rpow_of_exponent_le hy₁ (show -κ ≤ -(κ / 2) by linarith)
    have h₁ := mul_le_mul_of_nonneg_left (inverse_log_error hy (by linarith : κ ≤ 1))
      (show 0 ≤ A * (N : ℝ) ^ 3 by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hcomp (show 0 ≤ B * (N : ℝ) ^ 3 by positivity)
    have h₃ : 0 ≤ Real.log ((N : ℝ) * T) ^ 2 / T := by positivity
    have h₄ : 0 ≤ (N : ℝ) ^ 3 * y ^ (-(κ / 2)) := by positivity
    rw [mul_div_assoc]
    nlinarith only [h₁, h₂, mul_nonneg hA.le h₃, mul_nonneg hD.le h₃, mul_nonneg hD.le h₄]

end QH.PrimeProgressions
