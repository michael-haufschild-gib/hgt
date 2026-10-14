import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-! # Exponential limit of finite infinitesimal products

The number of factors may vary arbitrarily. Nonnegative factors whose largest
increment tends to zero retain exactly their total first-order mass.
-/

namespace GaloisForLFunctions.HTGeometry
open Filter Topology
noncomputable section

theorem sum_log_one_add_bounds {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {δ : ℝ} (hx : ∀ i ∈ s, 0 ≤ x i)
    (hbound : ∀ i ∈ s, x i ≤ δ) :
    (∑ i ∈ s, x i) / (1 + δ) ≤ ∑ i ∈ s, Real.log (1 + x i) ∧
      (∑ i ∈ s, Real.log (1 + x i)) ≤ ∑ i ∈ s, x i := by
  constructor
  · rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro i hi
    have hp : 0 < 1 + x i := by linarith [hx i hi]
    calc
      x i / (1 + δ) ≤ x i / (1 + x i) :=
        div_le_div_of_nonneg_left (hx i hi) hp (by linarith [hbound i hi])
      _ = 1 - (1 + x i)⁻¹ := by field_simp; ring
      _ ≤ Real.log (1 + x i) := Real.one_sub_inv_le_log_of_pos hp
  · apply Finset.sum_le_sum
    intro i hi
    simpa only [add_sub_cancel_left] using
      Real.log_le_sub_one_of_pos (show 0 < 1 + x i by linarith [hx i hi])

theorem tendsto_sum_log_one_add {ι : Type*} (s : ℕ → Finset ι)
    (x : ℕ → ι → ℝ) (δ : ℕ → ℝ) {E : ℝ}
    (hx : ∀ n i, i ∈ s n → 0 ≤ x n i)
    (hbound : ∀ n i, i ∈ s n → x n i ≤ δ n)
    (hsmall : Tendsto δ atTop (𝓝 0))
    (hmass : Tendsto (fun n => ∑ i ∈ s n, x n i) atTop (𝓝 E)) :
    Tendsto (fun n => ∑ i ∈ s n, Real.log (1 + x n i)) atTop (𝓝 E) := by
  have hden : Tendsto (fun n => 1 + δ n) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.add hsmall
  have hlo := hmass.div hden (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at hlo
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hmass
    (fun n => (sum_log_one_add_bounds (s n) (x n) (hx n) (hbound n)).1)
    (fun n => (sum_log_one_add_bounds (s n) (x n) (hx n) (hbound n)).2)

theorem tendsto_prod_one_add {ι : Type*} (s : ℕ → Finset ι)
    (x : ℕ → ι → ℝ) (δ : ℕ → ℝ) {E : ℝ}
    (hx : ∀ n i, i ∈ s n → 0 ≤ x n i)
    (hbound : ∀ n i, i ∈ s n → x n i ≤ δ n)
    (hsmall : Tendsto δ atTop (𝓝 0))
    (hmass : Tendsto (fun n => ∑ i ∈ s n, x n i) atTop (𝓝 E)) :
    Tendsto (fun n => ∏ i ∈ s n, (1 + x n i)) atTop (𝓝 (Real.exp E)) := by
  have h := (Real.continuous_exp.tendsto E).comp
    (tendsto_sum_log_one_add s x δ hx hbound hsmall hmass)
  convert h using 1
  funext n
  rw [Function.comp_apply, Real.exp_sum]
  exact Finset.prod_congr rfl fun i hi =>
    (Real.exp_log (by linarith [hx n i hi])).symm

end
end GaloisForLFunctions.HTGeometry
