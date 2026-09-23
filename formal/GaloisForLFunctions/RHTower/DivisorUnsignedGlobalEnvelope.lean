import GaloisForLFunctions.RHTower.DivisorSmoothWeightedBlockCeiling
import GaloisForLFunctions.RHTower.DivisorSmoothSourcePositivity
import GaloisForLFunctions.RHTower.DivisorUnsignedChannelExactMean

/-!
# Global unsigned envelope and uniform large-prime pair control

Every smooth weighted block has its exact mean ceiling, and every source term
is nonnegative. Completing the terminal block gives a global smooth envelope;
centered cancellation and exact clipped homothety transfer it to all unsigned
dilations. Its strict margin against twice the unit mean removes the quotient
restriction from eventual factor-two control. Every sufficiently large
multiplier then obeys that comparison at every cutoff and cofactor, and any
two sufficiently large distinct active primes respect the original diagonal.
Arbitrary processed signed states and an exhaustive order remain open.
-/

noncomputable section
open Finset Filter Topology HTGeometry
namespace RHTower

private lemma smooth_abel_monotone : Monotone divisorHyperbolaSmoothAbel := by
  intro M N hMN
  unfold divisorHyperbolaSmoothAbel
  apply sum_le_sum_of_subset_of_nonneg (range_mono hMN)
  intro n _ _
  exact mul_nonneg (divisorHyperbolaSmoothRemainder_nonneg n) (halfOrderAbelStep_nonneg 0 n)

private lemma smooth_square_prefix (s : ℕ) :
    divisorHyperbolaSmoothAbel ((s+1)*(s+1)) ≤ divisorHyperbolaSmoothMean*s := by
  induction s with
  | zero => norm_num [divisorHyperbolaSmoothAbel,divisorHyperbolaSmoothRemainder]
  | succ s ih =>
    have h := sum_divisorHyperbolaSmooth_square_block_mul_sqrtStep_le_mean (s:=s+1) (by omega)
    rw [sum_Ico_eq_sub _ (show (s+1)*(s+1) ≤ (s+1+1)*(s+1+1) by nlinarith)] at h
    change divisorHyperbolaSmoothAbel ((s+1+1)*(s+1+1))-
      divisorHyperbolaSmoothAbel ((s+1)*(s+1)) ≤ divisorHyperbolaSmoothMean at h
    push_cast
    linarith only [h,ih]

/-- Complete weighted blocks and nonnegative source tails bound every actual
smooth Abel cutoff by its exact asymptotic coefficient. -/
theorem divisorHyperbolaSmoothAbel_le_exact_mean_sqrt (M : ℕ) :
    divisorHyperbolaSmoothAbel M ≤ divisorHyperbolaSmoothMean*Real.sqrt M := by
  let s := Nat.sqrt M
  have hnext : M ≤ (s+1)*(s+1) := (Nat.lt_succ_sqrt M).le
  have h := (smooth_abel_monotone hnext).trans (smooth_square_prefix s)
  have hs : (s:ℝ) ≤ Real.sqrt M := by
    have hsq : (s:ℝ)^(2 : ℕ) ≤ M := by rw [pow_two]; exact_mod_cast Nat.sqrt_le M
    have hroot := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) M)
    have hs0 := Nat.cast_nonneg (α:=ℝ) s
    have hr0 := Real.sqrt_nonneg (M:ℝ)
    nlinarith only [hsq,hroot,hs0,hr0]
  have ha : 0 ≤ divisorHyperbolaSmoothMean := by linarith only [divisorHyperbolaSmoothMean_gt_one_sixth]
  exact h.trans (mul_le_mul_of_nonneg_left hs ha)

private lemma unit_le_smooth_mean (M : ℕ) :
    divisorUnsignedDilationChannel M 1 ≤ divisorHyperbolaSmoothMean*Real.sqrt M := by
  have hid := mobiusDivisorDilationChannel_one_eq_hyperbola M
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned] at hid
  simp only [ArithmeticFunction.moebius_apply_one,Int.cast_one,one_mul] at hid
  have hc := (centeredDivisorHyperbolaAbel_bounds M).2
  have hs := divisorHyperbolaSmoothAbel_le_exact_mean_sqrt M
  linarith only [hid,hc,hs]

/-- Exact clipped homothety transfers the global smooth mean ceiling to
every unsigned dilation, uniformly in both cutoff and dilation. -/
theorem divisorUnsignedDilationChannel_le_smoothMean_sqrt (M d : ℕ) :
    divisorUnsignedDilationChannel M d ≤ divisorHyperbolaSmoothMean*Real.sqrt M := by
  have ha : 0 ≤ divisorHyperbolaSmoothMean := by linarith only [divisorHyperbolaSmoothMean_gt_one_sixth]
  by_cases hd : d=0
  · subst d
    simp [divisorUnsignedDilationChannel,primeFreeDivisorDefect,
      mul_nonneg ha (Real.sqrt_nonneg (M:ℝ))]
  have hd0 : 0<d := by omega
  have hw0 := divisorPrimeClipWeight_nonneg M d hd0
  have hw1 : 0 ≤ 1-divisorPrimeClipWeight M d := by
    have h := divisorPrimeClipWeight_lt_one M d hd0
    linarith
  have hA := mul_le_mul_of_nonneg_left (unit_le_smooth_mean (M/d)) hw1
  have hB := mul_le_mul_of_nonneg_left (unit_le_smooth_mean (M/d+1)) hw0
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hA hB) (Real.sqrt_nonneg (d:ℝ))
  have hc := divisorUnsignedDilationChannel_prime_interpolation M d 1 hd0
  simp only [Nat.mul_one] at hc
  have hclock := divisorPrimeClipWeight_mul_step M d hd0
  push_cast at hclock
  rw [Real.sqrt_mul (Nat.cast_nonneg d)] at hclock
  rw [hc]
  push_cast at hsum ⊢
  have hclockmul := congrArg (fun x : ℝ => divisorHyperbolaSmoothMean*x) hclock
  nlinarith only [hsum,hclockmul]

private lemma smooth_mean_lt_nine_fiftieths : divisorHyperbolaSmoothMean < (9/50:ℝ) := by
  have hg := divisorHyperbolaSmoothRemainder_nonneg 2
  norm_num [divisorHyperbolaSmoothRemainder,harmonic,Finset.sum_range_succ,Finset.sum_Icc_succ_top] at hg
  have hp := Real.log_le_log (by positivity : (0:ℝ)<2*Real.pi)
    (by linarith [Real.pi_lt_d2] : 2*Real.pi ≤ (63/10:ℝ))
  have hl := Real.log_le_sub_one_of_pos (x:=(126/125:ℝ)) (by norm_num)
  have he : Real.log (63/10:ℝ)=2*Real.log 5-2*Real.log 2+Real.log (126/125:ℝ) := by
    rw [show (63/10:ℝ)=(5^(2 : ℕ)/2^(2 : ℕ))*(126/125) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_div (by norm_num) (by norm_num),Real.log_pow,Real.log_pow]
    norm_num
  rw [he] at hp
  dsimp [divisorHyperbolaSmoothMean]
  linarith only [hg,hp,hl,Real.log_five_lt_d9,Real.log_two_gt_d9]

private lemma unit_mean_gt_nine_hundredths : (9/100:ℝ) <
    Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/4 := by
  have hlog := Real.log_le_log (by norm_num : (0:ℝ)<157/25)
    (by linarith [Real.pi_gt_d2] : (157/25:ℝ) ≤ 2*Real.pi)
  have hr := Real.log_le_sub_one_of_pos (x:=(625/628:ℝ)) (by norm_num)
  have he : Real.log (157/25:ℝ)+Real.log (625/628:ℝ)=2*Real.log 5-2*Real.log 2 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
    rw [show (25/4:ℝ)=5^(2 : ℕ)/2^(2 : ℕ) by norm_num,Real.log_div (by norm_num) (by norm_num),Real.log_pow,Real.log_pow]
    norm_num
  have hg := eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  linarith only [hlog,hr,he,hg,Real.log_five_gt_d9,Real.log_two_lt_d9]

/-- At every sufficiently large unit cutoff, all integer dilations obey the
factor-two comparison simultaneously. No quotient lower bound is imposed. -/
theorem exists_divisorUnsignedDilationChannel_uniform_unit_double :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ d : ℕ,
      divisorUnsignedDilationChannel N d ≤ 2*divisorUnsignedDilationChannel N 1 := by
  have hevent := tendsto_divisorUnsignedDilationChannel_one_div_sqrt.eventually
    (lt_mem_nhds unit_mean_gt_nine_hundredths)
  obtain ⟨T,hT⟩ := eventually_atTop.mp hevent
  refine ⟨max T 1,fun N hN d => ?_⟩
  have hN1 : 1 ≤ N := (le_max_right T 1).trans hN
  have hroot : 0<Real.sqrt N := Real.sqrt_pos.mpr (by positivity)
  have hl := (lt_div_iff₀ hroot).mp (hT N ((le_max_left T 1).trans hN))
  have hu := divisorUnsignedDilationChannel_le_smoothMean_sqrt N d
  have hm := mul_le_mul_of_nonneg_right smooth_mean_lt_nine_fiftieths.le hroot.le
  nlinarith only [hl,hu,hm]

/-- Every sufficiently large multiplier obeys the factor-two source
comparison at every cutoff and every cofactor, including inactive channels. -/
theorem exists_divisorUnsignedDilationChannel_large_multiplier_double :
    ∃ P₀ : ℕ, ∀ p : ℕ, P₀ ≤ p → ∀ M d : ℕ,
      divisorUnsignedDilationChannel M (p*d) ≤ 2*divisorUnsignedDilationChannel M d := by
  obtain ⟨N₀,hN₀⟩ := exists_divisorUnsignedDilationChannel_uniform_unit_double
  refine ⟨max N₀ 1,fun p hp => ?_⟩
  apply (divisorUnsignedDilation_comparison_iff_unit p 2).mpr
  intro N
  by_cases hN : N₀ ≤ N
  · exact hN₀ N hN p
  have hp0 : 0<p := by have := (le_max_right N₀ 1).trans hp; omega
  have hNp : N ≤ p := by have := (le_max_left N₀ 1).trans hp; omega
  have hz : divisorUnsignedDilationChannel N p=0 := by
    simp [divisorUnsignedDilationChannel,Icc_eq_empty_of_lt (by omega : N-1<p)]
  rw [hz]
  exact mul_nonneg (by norm_num) (divisorUnsignedDilationChannel_nonneg N 1)

/-- Any two sufficiently large distinct active primes preserve the original
complete energy ceiling, uniformly in the parent cutoff and their ratio. -/
theorem exists_mobiusDivisorSelectionEnergy_two_large_primes_le_empty :
    ∃ P₀ : ℕ, ∀ M p q : ℕ, p.Prime → q.Prime → P₀ ≤ p → P₀ ≤ q →
      p<M → q<M → p≠q →
      mobiusDivisorSelectionEnergy M (insert q {p}) ≤ mobiusDivisorSelectionEnergy M ∅ := by
  obtain ⟨N₀,hN₀⟩ := exists_divisorUnsignedDilationChannel_uniform_unit_double
  refine ⟨N₀,fun M p q hp hq hp₀ hq₀ hpM hqM hpq => ?_⟩
  rcases mobiusDivisorSelectionEnergy_two_primes_le_or_unit_failure M hp hq hpM hqM hpq with h|h
  · exact h
  obtain ⟨N,r,hrN,_hNM,hr,hfail⟩ := h
  have hr₀ : N₀ ≤ r := hr.elim (fun he => he ▸ hp₀) (fun he => he ▸ hq₀)
  exact False.elim ((not_lt_of_ge (hN₀ N (hr₀.trans hrN.le) r)) hfail)

end RHTower
