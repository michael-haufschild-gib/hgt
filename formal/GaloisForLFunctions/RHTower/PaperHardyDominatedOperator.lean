import GaloisForLFunctions.RHTower.EulerDeletionPrimitiveHardy
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix

/-! # Complete complex operators dominated by the native Hardy tail

The existing positive infinite-tail estimate supplies both ordinary row
summability and the full output energy. No finite-section admission is assumed.
-/

namespace RHTower.PaperHardy
noncomputable section
open DeletionPrimitiveHardy

local notation "History" => lp (fun _ : ℕ => ℂ) 2

/-- Matrices with the already proved positive Hardy majorant. -/
structure Kernel where
  entry : ℕ → ℕ → ℂ
  bound : ∀ n j, ‖entry n j‖ ≤ tailKernel (3 / 4) n j

theorem inverse_le_tail (n j : ℕ) (hnj : n ≤ j) :
    1 / ((j : ℝ) + 1) ≤ tailKernel (3 / 4) n j := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hj : (0 : ℝ) < j + 1 := by positivity
  have hnj' : (n : ℝ) + 1 ≤ j + 1 := by exact_mod_cast Nat.add_le_add_right hnj 1
  have h := mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos hn hnj' (by norm_num : (-1 / 4 : ℝ) ≤ 0))
    (Real.rpow_nonneg hj.le (-3 / 4))
  rw [← Real.rpow_add hj] at h
  norm_num only [show (-1 / 4 : ℝ) + -3 / 4 = -1 by norm_num, Real.rpow_neg_one] at h
  simpa only [tailKernel, if_pos hnj, show (3 / 4 : ℝ) - 1 = -1 / 4 by norm_num,
    neg_div, one_div] using h

private theorem majorant_row_summable (f : History) (n : ℕ) :
    Summable (fun j => tailKernel (3 / 4) n j * ‖f j‖) :=
  summable_tail_row (by norm_num) (by norm_num) (fun j => norm_nonneg _)
    (HilbertSchmidt.summable_coe_sq f) n

theorem Kernel.row_summable (K : Kernel) (f : History) (n : ℕ) :
    Summable (fun j => K.entry n j * f j) :=
  Summable.of_norm_bounded (majorant_row_summable f n) fun j => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (K.bound n j) (norm_nonneg _)

theorem Kernel.row_norm_le (K : Kernel) (f : History) (n : ℕ) :
    ‖∑' j, K.entry n j * f j‖ ≤ tailTransform (3 / 4) (fun j => ‖f j‖) n := by
  apply (norm_tsum_le_tsum_norm (K.row_summable f n).norm).trans
  exact Summable.tsum_le_tsum (fun j => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (K.bound n j) (norm_nonneg _))
    (K.row_summable f n).norm (majorant_row_summable f n)

private theorem output_mem (K : Kernel) (f : History) :
    Memℓp (fun n => ∑' j, K.entry n j * f j) 2 := by
  apply HilbertSchmidt.memℓp_of_sq
  exact Summable.of_nonneg_of_le (fun n => sq_nonneg _)
    (fun n => pow_le_pow_left₀ (norm_nonneg _) (K.row_norm_le f n) 2)
    (tail_energy_summable_le (by norm_num) (by norm_num) (fun j => norm_nonneg _)
      (HilbertSchmidt.summable_coe_sq f)).1

private theorem output_norm_le (K : Kernel) (f : History) :
    ‖(⟨fun n => ∑' j, K.entry n j * f j, output_mem K f⟩ : History)‖ ≤ 5 * ‖f‖ := by
  let g : History := ⟨fun n => ∑' j, K.entry n j * f j, output_mem K f⟩
  have hmajor := tail_energy_summable_le (by norm_num : (1 / 2 : ℝ) < 3 / 4)
    (by norm_num : (3 / 4 : ℝ) < 1) (fun j => norm_nonneg (f j)) (HilbertSchmidt.summable_coe_sq f)
  have hsq : ‖g‖ ^ 2 ≤ 25 * ‖f‖ ^ 2 := by
    rw [HilbertSchmidt.lp_norm_sq_eq g, HilbertSchmidt.lp_norm_sq_eq f]
    have h := (Summable.tsum_le_tsum
      (fun n => pow_le_pow_left₀ (norm_nonneg _) (K.row_norm_le f n) 2)
      (HilbertSchmidt.summable_coe_sq g) hmajor.1).trans hmajor.2
    norm_num [schurConstant] at h ⊢
    exact h
  change ‖g‖ ≤ 5 * ‖f‖
  nlinarith [norm_nonneg g, norm_nonneg f]

/-- The actual complete row action on every square-summable complex history. -/
def Kernel.toOperator (K : Kernel) : History →L[ℂ] History :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun n => ∑' j, K.entry n j * f j, output_mem K f⟩
      map_add' := fun f g => by
        apply lp.ext
        funext n
        show ∑' j, K.entry n j * (f + g) j =
          (∑' j, K.entry n j * f j) + ∑' j, K.entry n j * g j
        rw [← (K.row_summable f n).tsum_add (K.row_summable g n)]
        exact tsum_congr fun j => by rw [lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := fun c f => by
        apply lp.ext
        funext n
        show ∑' j, K.entry n j * (c • f) j = c • ∑' j, K.entry n j * f j
        rw [smul_eq_mul, ← tsum_mul_left]
        apply tsum_congr
        intro j
        rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        ring }
    5 (output_norm_le K)

theorem Kernel.toOperator_apply (K : Kernel) (f : History) (n : ℕ) :
    K.toOperator f n = ∑' j, K.entry n j * f j := rfl

theorem Kernel.norm_toOperator_le (K : Kernel) : ‖K.toOperator‖ ≤ 5 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

theorem Kernel.toOperator_single (K : Kernel) (n j : ℕ) :
    K.toOperator (lp.single 2 j (1 : ℂ)) n = K.entry n j := by
  rw [K.toOperator_apply,
    tsum_eq_single j (fun k hk => by rw [lp.single_apply_ne _ _ _ hk, mul_zero])]
  rw [lp.single_apply_self, mul_one]

end
end RHTower.PaperHardy
