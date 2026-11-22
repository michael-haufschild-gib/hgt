import GaloisForLFunctions.RHTower.SelbergPrimePolynomialHighMoments
import GaloisForLFunctions.RHTower.VonMangoldtMollifierPolynomialMeanSquare
import GaloisForLFunctions.RHTower.XiWardInteriorTraceSplit

/-! Absolute Dirichlet masses for the full Mangoldt sequence and for proper prime powers. -/

open ArithmeticFunction Finset

namespace QH.PrimeProgressions

theorem mangoldt_right_mass {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    Summable (fun n : ℕ => Λ n / (n : ℝ) ^ (1 + r)) ∧
      ∑' n : ℕ, Λ n / (n : ℝ) ^ (1 + r) ≤ 12 / r := by
  have hs : 1 < 1 + r := by linarith only [hr]
  refine ⟨RHTower.summable_vonMangoldt_div_rpow hs, ?_⟩
  refine (RHTower.tsum_vonMangoldt_div_rpow_le_six hs).trans ?_
  rw [add_sub_cancel_left]
  exact div_le_div_of_nonneg_right (by linarith only [hr₁]) hr.le

theorem summable_nonPrime_mangoldt_three_quarters :
    Summable (fun n : ℕ => (if n.Prime then 0 else Λ n) / (n : ℝ) ^ (3 / 4 : ℝ)) := by
  let f (n : ℕ) := (if n.Prime then 0 else Λ n) / (n : ℝ) ^ (3 / 4 : ℝ)
  have hf (n : ℕ) : 0 ≤ f n := by
    dsimp only [f]
    split_ifs
    · positivity
    · exact div_nonneg vonMangoldt_nonneg (by positivity)
  refine summable_of_sum_range_le (c := 144) hf fun N => ?_
  have he : Icc 0 N = insert 0 (Icc 1 N) := by
    ext n
    simp only [mem_Icc, mem_insert]
    omega
  have hzero : f 0 = 0 := by simp [f]
  calc
    ∑ n ∈ range N, f n ≤ ∑ n ∈ Icc 0 N, f n :=
      sum_le_sum_of_subset_of_nonneg (fun n hn => mem_Icc.mpr ⟨Nat.zero_le n, (mem_range.mp hn).le⟩)
        (fun n _ _ => hf n)
    _ = ∑ n ∈ Icc 1 N, f n := by
      rw [he, sum_insert (by simp), hzero, zero_add]
    _ = ∑ n ∈ (Icc 1 N).filter (fun n => ¬ n.Prime), Λ n * (n : ℝ) ^ (-(1 / 2 + 1 / 4 : ℝ)) := by
      rw [sum_filter]
      refine sum_congr rfl fun n _ => ?_
      by_cases hp : n.Prime
      · simp [f, hp]
      · simp only [f, hp, if_false, not_false_eq_true, if_true]
        rw [show (1 / 2 + 1 / 4 : ℝ) = 3 / 4 by norm_num, Real.rpow_neg (Nat.cast_nonneg n),
          div_eq_mul_inv]
    _ ≤ 144 := by
      convert RHTower.sum_nonprime_vonMangoldt_rpow_le (δ := 1 / 4) (by norm_num) (by norm_num) N using 1 <;>
        norm_num

end QH.PrimeProgressions
