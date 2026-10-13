import GaloisForLFunctions.HTGeometry.WalshPowerWeights
import GaloisForLFunctions.HTGeometry.WalshLpBlocks
import GaloisForLFunctions.HTGeometry.LpInjectionCoordinates

/-! # Compact weighted Walsh levels and their geometric norm budget -/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open RHTower

namespace WalshPowerKernel

def level (D : WalshPowerKernel) (k : ℕ) :
    lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  (Real.sqrt ((2 ^ k : ℕ) : ℝ) : ℂ) • (D.leftOperator k).comp
    ((lpScalarInjection (dyadicChild k 0) (dyadicChild_injective k 0)).toContinuousLinearMap.comp
      ((walshBlockIsometry ℕ k).toLinearIsometry.toContinuousLinearMap.comp
        ((lpCoordinatePullback (E := ℂ) (dyadicChild k 1) (dyadicChild_injective k 1)).comp
          (D.rightOperator k))))

theorem level_compact (D : WalshPowerKernel) (k : ℕ) : IsCompactOperator (D.level k) :=
  ((((D.rightOperator_compact k).clm_comp
    (lpCoordinatePullback (E := ℂ) (dyadicChild k 1) (dyadicChild_injective k 1))).clm_comp
      (walshBlockIsometry ℕ k).toLinearIsometry.toContinuousLinearMap).clm_comp
        (lpScalarInjection (dyadicChild k 0) (dyadicChild_injective k 0)).toContinuousLinearMap).clm_comp
          (D.leftOperator k) |>.smul (Real.sqrt ((2 ^ k : ℕ) : ℝ) : ℂ)

def majorant (D : WalshPowerKernel) (k : ℕ) : ℝ :=
  Real.sqrt ((2 ^ k : ℕ) : ℝ) * (D.bound * (2 : ℝ) ^ D.alpha) *
    (D.bound * ((2 ^ k : ℕ) : ℝ) ^ (D.alpha + D.beta))

theorem majorant_nonneg (D : WalshPowerKernel) (k : ℕ) : 0 ≤ D.majorant k := by
  unfold majorant
  positivity [D.bound_nonneg]

theorem norm_level_le (D : WalshPowerKernel) (k : ℕ) : ‖D.level k‖ ≤ D.majorant k := by
  apply ContinuousLinearMap.opNorm_le_bound _ (D.majorant_nonneg k)
  intro x
  let R := lpCoordinatePullback (E := ℂ) (dyadicChild k 1) (dyadicChild_injective k 1)
  let U := walshBlockIsometry ℕ k
  let I := lpScalarInjection (dyadicChild k 0) (dyadicChild_injective k 0)
  change ‖(Real.sqrt ((2 ^ k : ℕ) : ℝ) : ℂ) • D.leftOperator k (I (U (R (D.rightOperator k x))))‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hL := norm_lpDiagonalLM_le (D.leftWeight k)
    (mul_nonneg D.bound_nonneg (by positivity)) (D.leftWeight_bound k) (I (U (R (D.rightOperator k x))))
  have hR := norm_lpDiagonalLM_le (D.rightWeight k)
    (mul_nonneg D.bound_nonneg (by positivity)) (D.rightWeight_bound k) x
  have hP := lpCoordinatePullbackLinear_norm_le (dyadicChild k 1) (dyadicChild_injective k 1)
    (D.rightOperator k x)
  calc
    _ ≤ Real.sqrt ((2 ^ k : ℕ) : ℝ) *
        ((D.bound * (2 : ℝ) ^ D.alpha) * ‖I (U (R (D.rightOperator k x)))‖) :=
      mul_le_mul_of_nonneg_left hL (Real.sqrt_nonneg _)
    _ = Real.sqrt ((2 ^ k : ℕ) : ℝ) *
        ((D.bound * (2 : ℝ) ^ D.alpha) * ‖R (D.rightOperator k x)‖) := by
      rw [I.norm_map, U.norm_map]
    _ ≤ Real.sqrt ((2 ^ k : ℕ) : ℝ) *
        ((D.bound * (2 : ℝ) ^ D.alpha) *
          ((D.bound * ((2 ^ k : ℕ) : ℝ) ^ (D.alpha + D.beta)) * ‖x‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hP.trans hR)
          (mul_nonneg D.bound_nonneg (by positivity))) (Real.sqrt_nonneg _)
    _ = _ := by unfold majorant; ring

theorem majorant_geometric (D : WalshPowerKernel) (k : ℕ) :
    D.majorant k = (D.bound ^ 2 * (2 : ℝ) ^ D.alpha) *
      ((2 : ℝ) ^ (D.alpha + D.beta + 1 / 2)) ^ k := by
  have hs : Real.sqrt ((2 ^ k : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ) ^ (D.alpha + D.beta) =
      ((2 : ℝ) ^ (D.alpha + D.beta + 1 / 2)) ^ k := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity), Nat.cast_pow, Nat.cast_ofNat,
      ← Real.rpow_natCast_mul (by norm_num), mul_comm, Real.rpow_mul_natCast (by norm_num)]
    congr 2
    ring
  unfold majorant
  rw [← hs]
  ring

theorem majorant_summable (D : WalshPowerKernel) : Summable D.majorant := by
  have hg : Summable (fun k : ℕ => ((2 : ℝ) ^ (D.alpha + D.beta + 1 / 2)) ^ k) := by
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_of_nonneg (by positivity)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [D.sum_lt])
  exact (hg.mul_left (D.bound ^ 2 * (2 : ℝ) ^ D.alpha)).congr
    (fun k => (D.majorant_geometric k).symm)

theorem level_summable (D : WalshPowerKernel) : Summable D.level :=
  Summable.of_norm_bounded D.majorant_summable D.norm_level_le

end WalshPowerKernel
end
end GaloisForLFunctions.HTGeometry
