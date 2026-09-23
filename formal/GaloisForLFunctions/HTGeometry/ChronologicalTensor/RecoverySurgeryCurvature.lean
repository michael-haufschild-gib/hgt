import GaloisForLFunctions.HTGeometry.ChronologicalTensor.RecoverySurgeryCosts

/-!
# Strict adjacent curvature survives the first geometric moment failure

The inscribed core loses at most eleven over thirty-two times the square of
the surgery degree. This quantitative bound preserves every adjacent strict
log-convexity inequality through the first altered recovery cost.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Polynomial Set

theorem recoverySurgeryCorePower_deficit (n : ℕ) :
    1-recoverySurgeryCorePower n =
      recoverySurgeryEpsilon n*(4*(n+2 : ℝ)+3/2)/recoverySurgeryEnvelope n := by
  have he : recoverySurgeryEnvelope n ≠ 0 := ne_of_gt (lt_trans zero_lt_one (recoverySurgeryEnvelope_gt_one n))
  unfold recoverySurgeryCorePower
  field_simp
  unfold recoverySurgeryEnvelope recoverySurgeryHeight
  ring

theorem recoverySurgeryCorePower_deficit_bound (n : ℕ) :
    1-recoverySurgeryCorePower n ≤ 11/(32*(n+2 : ℝ)^(2 : ℕ)) := by
  rw [recoverySurgeryCorePower_deficit]
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have he := recoverySurgeryEpsilon_pos n
  calc
    _ ≤ recoverySurgeryEpsilon n*(4*(n+2 : ℝ)+3/2) :=
      div_le_self (by positivity) (le_of_lt (recoverySurgeryEnvelope_gt_one n))
    _ ≤ _ := by
      unfold recoverySurgeryEpsilon
      rw [one_div_mul_eq_div]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_nonneg (sq_nonneg (n+2 : ℝ)) (show 0 ≤ (n+2 : ℝ)-1 by linarith)]

theorem recoverySurgeryCorePower_curvature_boundary (n : ℕ) :
    1-1/(n+1 : ℝ)^(2 : ℕ) < recoverySurgeryCorePower n := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have he : 11/(32*(n+2 : ℝ)^(2 : ℕ)) < 1/(n+1 : ℝ)^(2 : ℕ) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  linarith [recoverySurgeryCorePower_deficit_bound n]

theorem recoveryWedgeGap_curvature_ratio (k : ℕ) :
    (recoveryWedgeGap (k+1))^(2 : ℕ) =
      (1-1/(k+2 : ℝ)^(2 : ℕ))*recoveryWedgeGap k*recoveryWedgeGap (k+2) := by
  unfold recoveryWedgeGap
  push_cast
  rw [pow_succ (2 : ℝ) (k+2), pow_succ (2 : ℝ) (k+1)]
  field_simp
  ring

theorem recoveryWedgeGap_strict_logconvex (k : ℕ) :
    (recoveryWedgeGap (k+1))^(2 : ℕ) < recoveryWedgeGap k*recoveryWedgeGap (k+2) := by
  rw [recoveryWedgeGap_curvature_ratio]
  have h : 0 < 1/(k+2 : ℝ)^(2 : ℕ) := by positivity
  nlinarith [mul_pos (recoveryWedgeGap_positive k) (recoveryWedgeGap_positive (k+2))]

theorem recoverySurgeryGap_prefix_strict_logconvex (n : ℕ) (k : Fin n) :
    (recoverySurgeryGap n (k.val+1))^(2 : ℕ) <
      recoverySurgeryGap n k.val * recoverySurgeryGap n (k.val+2) := by
  obtain ⟨k,hk⟩ := k
  rw [recoverySurgeryGap_prefix n ⟨k+1,by omega⟩,
    recoverySurgeryGap_prefix n ⟨k,by omega⟩]
  by_cases hlast : k+2 < n+1
  · rw [recoverySurgeryGap_prefix n ⟨k+2,hlast⟩]
    exact recoveryWedgeGap_strict_logconvex k
  · have hn : n=k+1 := by omega
    subst n
    have ha := recoverySurgeryCorePower_curvature_boundary (k+1)
    push_cast at ha
    have he : (k : ℝ)+1+1=k+2 := by ring
    rw [he] at ha
    have hm := mul_lt_mul_of_pos_right ha
      (mul_pos (recoveryWedgeGap_positive k) (recoveryWedgeGap_positive (k+2)))
    have hb := mul_le_mul_of_nonneg_left (recoverySurgeryGap_drop_lower (k+1))
      (le_of_lt (recoveryWedgeGap_positive k))
    rw [recoveryWedgeGap_curvature_ratio]
    nlinarith

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
