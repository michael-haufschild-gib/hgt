import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.FiniteZeroPackets
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.PrincipalZeroTruncation
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.TruncatedRampStatement
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ZeroChangeLevel
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ZeroCopyOrders

/-! The principal truncated Cesàro formula at level one. -/

open Complex Finset RHTower WindowedLandauTheory.HC WindowedLandauTheory.ZeroFreeDirichlet

noncomputable section

namespace QH.PrimeProgressions

theorem principal_truncated_ramp :
    ∃ C : ℝ, 0 < C ∧ ∀ κ T : ℝ, 0 < κ → κ ≤ 1 / 20 → 2 ≤ T →
      TruncatedRamp (1 : DirichletCharacter ℂ 1) κ T C := by
  let A : ℝ := |Real.log (2 * Real.pi)| + 2
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨B, hB, htail⟩ := principal_zero_truncation
  obtain ⟨D, hD, hcount⟩ := principal_unit_count
  refine ⟨3 * A + 2 * B + D, by positivity, ?_⟩
  intro κ T hκ hκ' hT
  let χ : DirichletCharacter ℂ 1 := 1
  let point (q : XiZeroCopy) := (q.1 : ℂ)
  let m := analyticOrderNatAt χ.LFunction
  have hL : χ.LFunction = riemannZeta := DirichletCharacter.LFunction_modOne_eq
  have hfinite : {q : XiZeroCopy | Cutoff κ T (point q)}.Finite :=
    (finite_xiOrdinateWindow T 0).subset (fun q hq => by simpa [xiOrdinateWindow, point] using hq.2)
  obtain ⟨Z, hZ, hm, hcard, hsum⟩ := finite_zero_packet point (Cutoff κ T) hfinite m (by
    rintro ρ hρ ⟨q, rfl⟩
    dsimp only [m, point]
    rw [hL]
    exact xi_zero_copy_count ⟨xiZeroCopy_re_pos q, xiZeroCopy_re_lt_one q⟩)
  have hzeros (ρ : ℂ) : ρ ∈ Z ↔ IsLZero χ ρ ∧ Cutoff κ T ρ := by
    rw [hZ]
    constructor
    · rintro ⟨hρ, q, rfl⟩
      have hn : point q ≠ 1 := fun h => by
        have hp := xiZeroCopy_re_lt_one q
        change (q.1 : ℂ) = 1 at h
        rw [h, one_re] at hp
        exact (lt_irrefl _ hp)
      exact ⟨⟨Or.inr hn, by rw [hL]; exact
        (xi_eq_zero_iff (xiZeroCopy_re_pos q) hn).mp (xi_xiZeroCopy_eq_zero q)⟩, hρ⟩
    · rintro ⟨hz, hρ⟩
      have hp : 0 < ρ.re := by have := hρ.1; linarith
      have hζ := hz.2
      rw [hL] at hζ
      exact ⟨hρ, xi_zero_copy_exists ⟨hp, re_lt_one_of_isLZero hz⟩ hζ⟩
  refine ⟨Z, (-Real.eulerMascheroniConstant : ℂ), hzeros, hm, ?_, ?_⟩
  · intro t
    have hk := congrArg (fun n : ℕ => (n : ℝ)) (hcard t)
    push_cast at hk
    change (∑ ρ ∈ Z.filter (fun ρ => |ρ.im - t| ≤ 1), (m ρ : ℝ)) ≤ _
    rw [hk, Nat.cast_one, one_mul]
    refine (hcount (hfinite.toFinset.filter (fun q => |(point q).im - t| ≤ 1)) t
      (fun q hq => (mem_filter.mp hq).2)).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.log_nonneg (by linarith [abs_nonneg t]))
  · intro y hy
    have hy₁ : 1 ≤ y := by linarith
    have hy₀ : 0 < y := by linarith
    have hs : Summable (fun q : XiZeroCopy => QH.zeroKernel y (point q)) := by
      simpa only [point, xiZeroKernel_eq_neg_lag hy₀] using (summable_cpow_sub_one_div hy₁).neg
    let S := ∑ ρ ∈ Z, (m ρ : ℂ) * QH.zeroKernel y ρ
    let W := ∑' q : XiZeroCopy, if Cutoff κ T (point q) then 0 else QH.zeroKernel y (point q)
    let R := An.sumLamChi χ y / (y : ℂ) - (-Real.eulerMascheroniConstant : ℂ) - rampMain χ y + S
    have hmain : rampMain χ y = ((Real.log y - 1 : ℝ) : ℂ) := if_pos rfl
    have hnorm : ‖R + W‖ ≤ A / y := by
      have h := principal_normalized_formula y hy
      rw [hsum _ hs, ← add_assoc] at h
      simpa only [R, S, W, hmain, χ, A] using h
    have hnormW : ‖W‖ ≤ B * (y ^ (-κ) + Real.log T / T) := htail y κ T hy₁ hT
    change ‖R‖ ≤ _
    have hR := (norm_sub_le (R + W) W).trans (add_le_add hnorm hnormW)
    rw [add_sub_cancel_right] at hR
    refine hR.trans ?_
    simp only [Nat.cast_one, one_pow, one_mul]
    have hcomp := Real.rpow_le_rpow_of_exponent_le hy₁ (show -κ ≤ -(κ / 2) by linarith)
    have hl := Real.log_nonneg hy₁
    have h₁ : A / y ≤ 3 * A * y ^ (-(κ / 2)) := by
      rw [mul_comm (3 : ℝ) A, mul_assoc, ← mul_one_div]
      exact mul_le_mul_of_nonneg_left ((div_le_div_of_nonneg_right (by linarith : (1 : ℝ) ≤ 1 + Real.log y)
        hy₀.le).trans (inverse_log_error hy (by linarith : κ ≤ 1))) hA.le
    have hlT : (1 / 2 : ℝ) ≤ Real.log T :=
      (by linarith [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
        (Real.log_le_log (by norm_num) hT)
    have h₂ : Real.log T / T ≤ 2 * (Real.log T ^ 2 / T) := by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (by linarith)
      exact le_mul_of_one_le_left (by linarith : 0 ≤ Real.log T) (by linarith : (1 : ℝ) ≤ 2 * Real.log T)
        |>.trans_eq (by ring)
    have hp : 0 ≤ y ^ (-(κ / 2)) := by positivity
    have hq : 0 ≤ Real.log T ^ 2 / T := by positivity
    nlinarith only [h₁, mul_le_mul_of_nonneg_left hcomp hB.le, mul_le_mul_of_nonneg_left h₂ hB.le,
      mul_nonneg hA.le hq, mul_nonneg hD.le hq, mul_nonneg hB.le hp, mul_nonneg hD.le hp]

end QH.PrimeProgressions
