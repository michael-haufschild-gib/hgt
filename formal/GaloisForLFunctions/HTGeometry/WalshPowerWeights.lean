import GaloisForLFunctions.HTGeometry.DyadicParentBase
import GaloisForLFunctions.HTGeometry.LaplaceFormationCompletionTopology

/-! # Bounded dyadic factors for power-controlled separated kernels

The common sibling scale transfers growing row weights to a decaying input
diagonal. The input diagonal is compact; the output multiplier stays bounded.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter
open scoped Topology

structure WalshPowerKernel where
  row : ℕ → ℂ
  column : ℕ → ℂ
  alpha : ℝ
  beta : ℝ
  bound : ℝ
  alpha_nonneg : 0 ≤ alpha
  sum_lt : alpha + beta < -(1 / 2)
  bound_nonneg : 0 ≤ bound
  row_bound : ∀ n, ‖row n‖ ≤ bound * ((n : ℝ) + 1) ^ alpha
  column_bound : ∀ n, ‖column n‖ ≤ bound * ((n : ℝ) + 1) ^ beta

namespace WalshPowerKernel

theorem beta_neg (D : WalshPowerKernel) : D.beta < 0 := by
  linarith [D.alpha_nonneg, D.sum_lt]

theorem sum_neg (D : WalshPowerKernel) : D.alpha + D.beta < 0 :=
  D.sum_lt.trans (by norm_num)

def leftWeight (D : WalshPowerKernel) (k n : ℕ) : ℂ :=
  D.row n / (((dyadicParentBase k n : ℝ) ^ D.alpha : ℝ) : ℂ)

def rightWeight (D : WalshPowerKernel) (k n : ℕ) : ℂ :=
  if n / 2 ^ k % 2 = 1 then
    (((dyadicParentBase k n : ℝ) ^ D.alpha : ℝ) : ℂ) * D.column n else 0

theorem leftWeight_bound (D : WalshPowerKernel) (k n : ℕ) :
    ‖D.leftWeight k n‖ ≤ D.bound * (2 : ℝ) ^ D.alpha := by
  have hb : (0 : ℝ) < dyadicParentBase k n := by exact_mod_cast dyadicParentBase_pos k n
  have hn : (n : ℝ) + 1 ≤ 2 * (dyadicParentBase k n : ℝ) := by
    exact_mod_cast succ_le_twice_dyadicParentBase k n
  rw [leftWeight, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg hb.le _)]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hb _)).mpr
  calc
    ‖D.row n‖ ≤ D.bound * ((n : ℝ) + 1) ^ D.alpha := D.row_bound n
    _ ≤ D.bound * (2 * (dyadicParentBase k n : ℝ)) ^ D.alpha :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hn D.alpha_nonneg) D.bound_nonneg
    _ = _ := by rw [Real.mul_rpow (by norm_num) hb.le]; ring

theorem rightWeight_norm_le_scale (D : WalshPowerKernel) (k n : ℕ) :
    ‖D.rightWeight k n‖ ≤ D.bound * (dyadicParentBase k n : ℝ) ^ (D.alpha + D.beta) := by
  have hb : (0 : ℝ) < dyadicParentBase k n := by exact_mod_cast dyadicParentBase_pos k n
  unfold rightWeight
  split_ifs with hn
  · have hbn : (dyadicParentBase k n : ℝ) ≤ (n : ℝ) + 1 := by
      exact_mod_cast (dyadicParentBase_le_of_right hn).trans (Nat.le_succ n)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hb.le _)]
    calc
      _ ≤ (dyadicParentBase k n : ℝ) ^ D.alpha *
          (D.bound * ((n : ℝ) + 1) ^ D.beta) :=
        mul_le_mul_of_nonneg_left (D.column_bound n) (Real.rpow_nonneg hb.le _)
      _ ≤ (dyadicParentBase k n : ℝ) ^ D.alpha *
          (D.bound * (dyadicParentBase k n : ℝ) ^ D.beta) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hb hbn D.beta_neg.le)
            D.bound_nonneg) (Real.rpow_nonneg hb.le _)
      _ = _ := by rw [Real.rpow_add hb]; ring
  · rw [norm_zero]
    exact mul_nonneg D.bound_nonneg (Real.rpow_nonneg hb.le _)

theorem rightWeight_bound (D : WalshPowerKernel) (k n : ℕ) :
    ‖D.rightWeight k n‖ ≤ D.bound * ((2 ^ k : ℕ) : ℝ) ^ (D.alpha + D.beta) := by
  apply (D.rightWeight_norm_le_scale k n).trans
  apply mul_le_mul_of_nonneg_left _ D.bound_nonneg
  exact Real.rpow_le_rpow_of_nonpos (by positivity)
    (by exact_mod_cast dyadicParentBase_lower k n) D.sum_neg.le

theorem rightWeight_tendsto (D : WalshPowerKernel) (k : ℕ) :
    Tendsto (fun n => ‖D.rightWeight k n‖) atTop (𝓝 0) := by
  have hb : Tendsto (fun n => (dyadicParentBase k n : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono (dyadicParentBase_real_lower k)
    exact Filter.Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2)
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hp : Tendsto (fun n => (dyadicParentBase k n : ℝ) ^ (D.alpha + D.beta)) atTop (𝓝 0) := by
    simpa only [neg_neg, Function.comp_def] using
      (tendsto_rpow_neg_atTop (neg_pos.mpr D.sum_neg)).comp hb
  exact squeeze_zero (fun _ => norm_nonneg _) (D.rightWeight_norm_le_scale k)
    (by simpa using hp.const_mul D.bound)

theorem leftWeight_mul_rightWeight (D : WalshPowerKernel) {k n j : ℕ} (h : DyadicSibling k n j) :
    D.leftWeight k n * D.rightWeight k j = D.row n * D.column j := by
  have hb : (0 : ℝ) < dyadicParentBase k j := by exact_mod_cast dyadicParentBase_pos k j
  have hp : (((dyadicParentBase k j : ℝ) ^ D.alpha : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hb D.alpha).ne'
  rw [leftWeight, rightWeight, if_pos h.2.2, h.parentBase_eq]
  field_simp

def leftOperator (D : WalshPowerKernel) (k : ℕ) :
    lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  lpDiagonalCLM (D.leftWeight k) (mul_nonneg D.bound_nonneg (by positivity)) (D.leftWeight_bound k)

def rightOperator (D : WalshPowerKernel) (k : ℕ) :
    lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  lpDiagonalCLM (D.rightWeight k) (mul_nonneg D.bound_nonneg (by positivity)) (D.rightWeight_bound k)

theorem rightOperator_compact (D : WalshPowerKernel) (k : ℕ) : IsCompactOperator (D.rightOperator k) :=
  isCompactOperator_lpDiagonalCLM _ _ _ (D.rightWeight_tendsto k)

end WalshPowerKernel
end
end GaloisForLFunctions.HTGeometry
