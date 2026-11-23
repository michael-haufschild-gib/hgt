import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.PinnedSpectra.Nodes

/-! # Mixing finite secular probabilities into an infinite occupation law -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology Finset

/-- Native gap lengths define a probability whose inverse-heat moment diverges. -/
def tailLaw (k : ℕ) := occupationWeight k-occupationWeight (k+1)

theorem tailLaw_pos (k : ℕ) : 0 < tailLaw k := sub_pos.mpr (occupationWeight_strictAnti (Nat.lt_succ_self k))

theorem tailLaw_sum : HasSum tailLaw 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun k => (tailLaw_pos k).le) 1).mpr
  have hz : occupationWeight 0 = 1 := by rw [occupationWeight_eq]; norm_num
  simpa only [tailLaw,sum_range_sub',hz,sub_zero] using occupationWeight_tendsto.const_sub (1:ℝ)

private theorem row_summable {m : ℕ} (b : PrefixData m) (i : Fin (m+1)) :
    Summable (fun k => tailLaw k*nodeResidue b k i) :=
  tailLaw_sum.summable.of_nonneg_of_le (fun k => mul_nonneg (tailLaw_pos k).le (nodeResidue_nonneg b k i))
    (fun k => mul_le_of_le_one_right (tailLaw_pos k).le (nodeResidue_le_one b k i))

def prefixProbability {m : ℕ} (b : PrefixData m) (n : ℕ) : ℝ :=
  if h : n < m then ∑' k, tailLaw k*nodeResidue b k (Fin.castSucc ⟨n,h⟩)
  else tailLaw (n-m)*nodeResidue b (n-m) (Fin.last m)

theorem probability_head {m : ℕ} (b : PrefixData m) (i : Fin m) :
    prefixProbability b i.val = ∑' k, tailLaw k*nodeResidue b k i.castSucc := dif_pos i.isLt

theorem probability_tail {m : ℕ} (b : PrefixData m) (k : ℕ) :
    prefixProbability b (m+k) = tailLaw k*nodeResidue b k (Fin.last m) := by
  simp only [prefixProbability,dif_neg (Nat.le_add_right m k).not_gt,Nat.add_sub_cancel_left]

theorem probability_nonneg {m : ℕ} (b : PrefixData m) (n : ℕ) : 0 ≤ prefixProbability b n := by
  unfold prefixProbability
  split
  · exact tsum_nonneg (fun k => mul_nonneg (tailLaw_pos _).le (nodeResidue_nonneg ..))
  · exact mul_nonneg (tailLaw_pos _).le (nodeResidue_nonneg ..)

def prefixCap (m n : ℕ) : ℝ := if n < m then 1 else tailLaw (n-m)

theorem prefixCap_summable (m : ℕ) : Summable (prefixCap m) := by
  apply (summable_nat_add_iff m).mp
  simpa only [prefixCap,if_neg (Nat.le_add_left _ _).not_gt,Nat.add_sub_cancel] using tailLaw_sum.summable

theorem probability_le_cap {m : ℕ} (b : PrefixData m) (n : ℕ) : prefixProbability b n ≤ prefixCap m n := by
  unfold prefixProbability prefixCap
  split_ifs with h
  · exact ((row_summable b _).tsum_le_tsum (fun k => mul_le_of_le_one_right (tailLaw_pos k).le (nodeResidue_le_one b k _))
      tailLaw_sum.summable).trans_eq tailLaw_sum.tsum_eq
  · exact mul_le_of_le_one_right (tailLaw_pos _).le (nodeResidue_le_one b _ _)

theorem probability_continuous {m : ℕ} (n : ℕ) : Continuous (fun b : PrefixData m => prefixProbability b n) := by
  by_cases h : n < m
  · simp only [prefixProbability,dif_pos h]
    exact continuous_tsum (fun k => continuous_const.mul (nodeResidue_continuous k _)) tailLaw_sum.summable (fun k b => by
      rw [Real.norm_of_nonneg (mul_nonneg (tailLaw_pos k).le (nodeResidue_nonneg b k _))]
      exact mul_le_of_le_one_right (tailLaw_pos k).le (nodeResidue_le_one b k _))
  · simp only [prefixProbability,dif_neg h]
    exact continuous_const.mul (nodeResidue_continuous _ _)

/-- A bounded occupation reading of the mixture is the average of the finite insertion readings. -/
theorem mixture_reading {m : ℕ} (b : PrefixData m) (f : ℕ → ℝ) (C : ℝ) (hf : ∀ n, |f n| ≤ C) :
    ∑' n, prefixProbability b n*f n = ∑' k, tailLaw k*∑ i, nodeResidue b k i*f (nodeIndex m k i) := by
  let H (i : Fin m) (k : ℕ) := tailLaw k*nodeResidue b k i.castSucc*f i.val
  let T (k : ℕ) := tailLaw k*nodeResidue b k (Fin.last m)*f (m+k)
  have hh (i : Fin m) : Summable (H i) := (row_summable b i.castSucc).mul_right _
  have ht : Summable T := (tailLaw_sum.summable.mul_right C).of_norm_bounded (fun k => by
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (mul_nonneg (tailLaw_pos _).le (nodeResidue_nonneg b k _))]
    exact mul_le_mul (mul_le_of_le_one_right (tailLaw_pos k).le (nodeResidue_le_one b k _)) (hf _) (abs_nonneg _) (tailLaw_pos k).le)
  have htotal : Summable (fun n => prefixProbability b n*f n) :=
    ((prefixCap_summable m).mul_right C).of_norm_bounded (fun n => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (probability_nonneg b n)]
      exact mul_le_mul (probability_le_cap b n) (hf n) (abs_nonneg _) ((probability_nonneg b n).trans (probability_le_cap b n)))
  have hrow (k : ℕ) : tailLaw k*∑ i, nodeResidue b k i*f (nodeIndex m k i) = ∑ i, H i k + T k := by
    rw [Fin.sum_univ_castSucc,mul_add,Finset.mul_sum]
    simp only [nodeIndex_head,nodeIndex_last,H,T,mul_assoc]
  rw [← htotal.sum_add_tsum_nat_add m,← Fin.sum_univ_eq_sum_range,funext hrow,
    (summable_sum (fun i _ => hh i)).tsum_add ht,Summable.tsum_finsetSum (fun i _ => hh i)]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [probability_head]
    exact ((row_summable b i.castSucc).hasSum.mul_right (f i.val)).tsum_eq.symm
  · apply tsum_congr
    intro k
    rw [Nat.add_comm k m,probability_tail]

theorem probability_hasSum {m : ℕ} (b : PrefixData m) : HasSum (prefixProbability b) 1 := by
  apply ((prefixCap_summable m).of_nonneg_of_le (probability_nonneg b) (probability_le_cap b)).hasSum_iff.mpr
  simpa only [mul_one,nodeResidue_sum,tailLaw_sum.tsum_eq] using mixture_reading b (fun _ => 1) 1 (fun _ => by norm_num)

#print axioms probability_hasSum
#print axioms probability_continuous
#print axioms mixture_reading

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
