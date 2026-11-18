import GaloisForLFunctions.ExceptionalLayerTheory.PositiveWeightsForTheTwoSignsOfThePrimeError
import GaloisForLFunctions.ExceptionalLayerTheory.ALocalPrimeWaveAtEveryRightZero

/-!
# A positive comparison for the complex prime detector

At every real cutoff the alternating mean test has a positive divisor kernel,
while its convolution with the centred Mangoldt coefficients has square-root
size. Its divisor kernel dominates the modulus of each right-zero detector.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ExceptionalLayerTheory

private theorem meanTest_zero {x : ℝ} (hx : x ≤ 1) : primeMeanTest x = 0 := by
  rcases hx.lt_or_eq with h | rfl
  · simp [primeMeanTest,not_le.mpr h]
  · norm_num [primeMeanTest]

/-- On the log ray the test is increasing and has slope at most one. -/
private theorem meanTest_gap {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    0 ≤ primeMeanTest y - primeMeanTest x ∧
      primeMeanTest y - primeMeanTest x ≤ Real.log y-Real.log x := by
  have hx0 := zero_lt_one.trans_le hx
  have hy0 := hx0.trans_le hxy
  have hlog := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
  rw [Real.log_div hx0.ne' hy0.ne'] at hlog
  have hdiv : 0 ≤ 1-x/y := sub_nonneg.2 ((div_le_one hy0).2 hxy)
  have hbound := mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hx) hdiv
  have heq : x⁻¹*(1-x/y) = x⁻¹-y⁻¹ := by field_simp; ring
  rw [heq,one_mul] at hbound
  have hinv := inv_anti₀ hx0 hxy
  simp only [primeMeanTest,if_pos hx,if_pos (hx.trans hxy)]
  constructor <;> linarith only [hinv,hbound,hlog]

private theorem meanTest_divisor_gap {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : (n:ℝ) ≤ x) :
    |primeMeanTest (x/n)-primeMeanTest (x/(n+1))| ≤ 1/n := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hx0 := hn0.trans_le hx
  have h1 : (0:ℝ) < n+1 := by positivity
  have hy : 1 ≤ x/n := (one_le_div hn0).2 hx
  have hh := Real.log_le_sub_one_of_pos (div_pos h1 hn0)
  rw [Real.log_div h1.ne' hn0.ne',show ((n:ℝ)+1)/n-1=1/n by field_simp; ring] at hh
  by_cases h : (n:ℝ)+1 ≤ x
  · have hs := meanTest_gap ((one_le_div h1).2 h)
      (div_le_div_of_nonneg_left hx0.le hn0 (by linarith : (n:ℝ) ≤ n+1))
    rw [abs_of_nonneg hs.1]
    apply hs.2.trans
    rw [Real.log_div hx0.ne' hn0.ne',Real.log_div hx0.ne' h1.ne']
    linarith only [hh]
  · have hs := meanTest_gap (x := 1) le_rfl hy
    rw [meanTest_zero le_rfl,Real.log_one,sub_zero,sub_zero] at hs
    rw [meanTest_zero ((div_le_one h1).2 (le_of_not_ge h)),sub_zero,abs_of_nonneg hs.1]
    apply hs.2.trans
    rw [Real.log_div hx0.ne' hn0.ne']
    linarith only [Real.log_le_log hx0 (le_of_not_ge h),hh]

/-- The positive comparison has square-root signed response at every real cutoff. -/
theorem abs_alternatingPrimeExcess_meanTest {x : ℝ} (hx : 1 ≤ x) :
    |arithmeticKernel alternatingPrimeExcess primeMeanTest x| ≤
      2*(75+2*|Real.eulerMascheroniConstant|)*Real.sqrt x := by
  let B := 75+2*|Real.eulerMascheroniConstant|
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let N := ⌊x⌋₊
  have hf : (N:ℝ) ≤ x := Nat.floor_le (zero_le_one.trans hx)
  have hcut : x/((N:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).2 (Nat.lt_floor_add_one x).le
  rw [arithmeticKernel,sum_smul_eq_prefix_differences]
  simp only [Nat.cast_add_one,meanTest_zero hcut,smul_zero,zero_add,smul_eq_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ n ∈ Icc 1 N, B*(n:ℝ)^(-(1/2:ℝ)) := by
         refine sum_le_sum fun n hn => ?_
         obtain ⟨h1,h2⟩ := mem_Icc.mp hn
         have hp : 0 < (n:ℝ) := by exact_mod_cast h1
         rw [abs_mul]
         apply (mul_le_mul (abs_prefix_alternatingPrimeExcess n)
           (meanTest_divisor_gap h1 ((show (n:ℝ) ≤ N by exact_mod_cast h2).trans hf)) (abs_nonneg _)
           (mul_nonneg hB (Real.sqrt_nonneg _))).trans_eq
         change B*Real.sqrt n*(1/n) = _
         rw [mul_assoc,Real.sqrt_eq_rpow,one_div (n:ℝ),← div_eq_mul_inv,← Real.rpow_sub_one hp.ne',
           show (1/2:ℝ)-1 = -(1/2) by ring]
    _ ≤ _ := by
         rw [← mul_sum]
         have hs := mul_le_mul_of_nonneg_left (_root_.RHTower.sum_rpow_neg_half_le N) hB
         have hr := Real.sqrt_le_sqrt hf
         exact hs.trans (by change B*(2*Real.sqrt N) ≤ 2*B*Real.sqrt x; linarith only [mul_le_mul_of_nonneg_left hr hB])

private theorem detector_at_one (k : ℕ) (ρ : ℂ) :
    arithmeticKernel alternatingDivisorCoeff (centeredDirichletTest k ρ) 1 = 0 := by
  simp [arithmeticKernel,centeredDirichletTest]

/-- One positive divisor kernel dominates every zero's detector and has bounded
signed response after square-root normalization. -/
theorem exists_dominated_prime_zero_detector {ρ : ℂ} (hhalf : 1/2 < ρ.re) (hone : ρ.re < 1)
    (hz : riemannZeta ρ = 0) :
    ∃ (k : ℕ) (d : ℂ) (C : ℝ), d ≠ 0 ∧ 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      ‖arithmeticKernel alternatingDivisorCoeff (centeredDirichletTest k ρ) x‖ ≤ 6*C*primeMeanKernel x ∧
      ‖arithmeticKernel alternatingPrimeExcess (centeredDirichletTest k ρ) x - (x:ℂ)^ρ*d‖ ≤ C*Real.sqrt x ∧
      |arithmeticKernel alternatingPrimeExcess primeMeanTest x| ≤
         2*(75+2*|Real.eulerMascheroniConstant|)*Real.sqrt x := by
  obtain ⟨k,d,C,hd,hC,ha,hb⟩ := exists_alternating_prime_kernel_at_zero hhalf hone hz
  refine ⟨k,d,C,hd,hC,fun x hx => ⟨?_,hb x hx,abs_alternatingPrimeExcess_meanTest hx⟩⟩
  have h := ha 1 x le_rfl hx
  have hp := (primeMeanKernel_increment_bounds le_rfl hx).1
  rw [detector_at_one,sub_zero,Real.log_one,sub_zero] at h
  rw [primeMeanKernel_eq_zero le_rfl,sub_zero,Real.log_one,sub_zero] at hp
  exact h.trans (by linarith only [mul_le_mul_of_nonneg_left hp hC])

#print axioms exists_dominated_prime_zero_detector

end GaloisForLFunctions.ExclusionOfTheCriticalState
