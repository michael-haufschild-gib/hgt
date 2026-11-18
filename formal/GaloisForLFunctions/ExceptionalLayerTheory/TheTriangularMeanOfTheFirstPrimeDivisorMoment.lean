import GaloisForLFunctions.ExceptionalLayerTheory.TheSquareRootErrorInTheFirstPrimeDivisorMoment
import GaloisForLFunctions.ExceptionalLayerTheory.ThePowerModesOfTheOddQuotientMean
import GaloisForLFunctions.ExceptionalLayerTheory.TheQuarterExponentOfTheOddQuotientPrimeCount

/-!
# The triangular first prime-divisor moment

The linear centering disappears on taking a dyadic difference. A sublinear
term is determined by that difference at all larger dyadic cutoffs. This
recovers the raw mean from the finite parity count and the two unrestricted
power rows.
-/

noncomputable section
open Finset Filter Complex Topology
open _root_.RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem double_quotient_sum (f : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ range (2*N), f (j/2)) = 2*∑ j ∈ range N, f j := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ,show 2*n+2=2*n+1+1 by omega,sum_range_succ,sum_range_succ,ih,
      sum_range_succ f,show (2*n+1)/2=n by omega,show 2*n/2=n by omega]
    ring

private theorem sharp_moment_deficit (j N : ℕ) (hj : j ≤ N) :
    distinctPrimeLogMoment j - Real.log (j.factorial:ℕ) =
      -(∑ d ∈ Icc 1 N, primePowerPart d*((j/d:ℕ):ℝ)) := by
  have hp : (∑ p ∈ Nat.primesLE j, Real.log p*((j/p:ℕ):ℝ)) =
      ∑ p ∈ Nat.primesLE N, Real.log p*((j/p:ℕ):ℝ) := by
    apply sum_subset (Nat.primesLE_mono hj)
    intro p hp hnot
    have hlt : j<p := lt_of_not_ge fun h => hnot (Nat.mem_primesLE.mpr ⟨h,(Nat.mem_primesLE.mp hp).2⟩)
    simp [Nat.div_eq_of_lt hlt]
  have hm : (∑ d ∈ Icc 1 j, ArithmeticFunction.vonMangoldt d*((j/d:ℕ):ℝ)) =
      ∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d*((j/d:ℕ):ℝ) := by
    apply sum_subset (Icc_subset_Icc_right hj)
    intro d hd hnot
    have hlt : j<d := lt_of_not_ge fun h => hnot (mem_Icc.mpr ⟨(mem_Icc.mp hd).1,h⟩)
    simp [Nat.div_eq_of_lt hlt]
  have hi : Icc 1 j = Ioc 0 j := by ext n; simp only [mem_Icc,mem_Ioc]; omega
  rw [hi,ArithmeticOfSquareRootPrecision.chebyshevTransform_vonMangoldt] at hm
  rw [distinctPrimeLogMoment,hp,hm,Nat.primesLE_eq_filter_Icc_one,sum_filter,← sum_sub_distrib,←sum_neg_distrib]
  exact sum_congr rfl fun d _ => by
    by_cases hd : d.Prime <;> simp [primePowerPart,hd,ArithmeticFunction.vonMangoldt_apply_prime]

/-- Doubling the integer cutoff reads exactly the normalized parity count
of the actual proper-prime-power weights. -/
theorem triangularDistinctPrimeLogMoment_dyadic {N : ℕ} (hN : 0 < N) :
    triangularDistinctPrimeLogMoment (2*N)-2*triangularDistinctPrimeLogMoment N =
      -(∑ d ∈ Icc 1 (2*N), primePowerPart d*
        discreteQuotientMean (fun n => ((n%2:ℕ):ℝ)) d (2*N))/(2*(N:ℝ)) := by
  let F (j : ℕ) := distinctPrimeLogMoment j-Real.log (j.factorial:ℕ)
  have hfloor (j d : ℕ) : ((j/d:ℕ):ℝ)-2*(((j/2)/d:ℕ):ℝ)=((j/d%2:ℕ):ℝ) := by
    have hdiv : (j/2)/d=(j/d)/2 := by
      rw [Nat.div_div_eq_div_mul,Nat.div_div_eq_div_mul,mul_comm 2 d]
    rw [hdiv]
    have h := congrArg (Nat.cast (R := ℝ)) (Nat.mod_add_div (j/d) 2)
    push_cast at h; linarith only [h]
  have hrow (j : ℕ) (hj : j ∈ range (2*N)) :
      F j-2*F (j/2)= -(∑ d ∈ Icc 1 (2*N), primePowerPart d*((j/d%2:ℕ):ℝ)) := by
    dsimp only [F]
    rw [sharp_moment_deficit _ _ (mem_range.mp hj).le,
      sharp_moment_deficit _ _ ((Nat.div_le_self j 2).trans (mem_range.mp hj).le),mul_neg,
      neg_sub_neg,← neg_sub,neg_inj,mul_sum,← sum_sub_distrib]
    exact sum_congr rfl fun d _ => by rw [← hfloor]; ring
  have he := Finset.sum_congr (s₁ := range (2*N)) rfl hrow
  rw [sum_sub_distrib,←mul_sum,double_quotient_sum,sum_neg_distrib] at he
  simp only [discreteQuotientMean,mul_sum]
  rw [sum_comm]
  change (∑ j ∈ range (2*N), F j)/((2*N:ℕ):ℝ)+repeatedPrimeLogDensity*(2*N:ℕ)/2-
    2*((∑ j ∈ range N, F j)/(N:ℝ)+repeatedPrimeLogDensity*N/2)=_
  push_cast
  have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  field_simp
  linear_combination he

/-- A sublinear sequence with a power bound on its dyadic difference has
the same power bound. The geometric constant is explicit. -/
private theorem sublinear_dyadic_inverse (f : ℕ → ℝ) {b K : ℝ} (hb : b<1) (hK : 0≤K)
    (hlim : Tendsto (fun n : ℕ => f n/(n:ℝ)) atTop (𝓝 0))
    (hrec : ∀ n : ℕ, 1 ≤ n → |f (2*n)-2*f n| ≤ K*((2*n:ℕ):ℝ)^b)
    {n : ℕ} (hn : 1 ≤ n) :
    |f n| ≤ K*(2:ℝ)^b/(2-(2:ℝ)^b)*(n:ℝ)^b := by
  let B := K*(2:ℝ)^b/(2-(2:ℝ)^b)
  have h2 : (2:ℝ)^b < 2 := by
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) hb
  have hB : 0 ≤ B := div_nonneg (mul_nonneg hK (by positivity)) (sub_pos.mpr h2).le
  have hid : B*(2-(2:ℝ)^b)=K*(2:ℝ)^b := div_mul_cancel₀ _ (sub_pos.mpr h2).ne'
  have hstep (m : ℕ) (hm : 1 ≤ m) :
      2*(|f m|-B*(m:ℝ)^b) ≤ |f (2*m)|-B*((2*m:ℕ):ℝ)^b := by
    have he := abs_sub (f (2*m)) (f (2*m)-2*f m)
    rw [sub_sub_cancel,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at he
    have h := hrec m hm
    push_cast at h ⊢
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Nat.cast_nonneg _)] at h ⊢
    have hh := congrArg (· * (m:ℝ)^b) hid
    linarith only [h,he,hh]
  have hiter (k : ℕ) : (2:ℝ)^k*(|f n|-B*(n:ℝ)^b) ≤
      |f (2^k*n)|-B*((2^k*n:ℕ):ℝ)^b := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hh := hstep (2^k*n) (Nat.mul_pos (by positivity) hn)
      rw [pow_succ',mul_assoc,pow_succ',mul_assoc]
      exact (mul_le_mul_of_nonneg_left ih (by norm_num : (0:ℝ)≤2)).trans hh
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have ht : Tendsto (fun k : ℕ => (2:ℕ)^k*n) atTop atTop := by
    apply tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_right (2^k) hn)
    exact tendsto_pow_atTop_atTop_of_one_lt (by decide)
  have hlim' : Tendsto (fun k : ℕ => |f (2^k*n)|/(2:ℝ)^k) atTop (𝓝 0) := by
    have h := ((hlim.comp ht).abs.mul_const (n:ℝ))
    simp only [abs_zero,zero_mul] at h
    apply h.congr (fun k => ?_)
    change |f (2^k*n)/((2^k*n:ℕ):ℝ)|*n=_
    rw [abs_div,abs_of_nonneg (Nat.cast_nonneg _)]
    push_cast; field_simp
  have hend : |f n|-B*(n:ℝ)^b ≤ 0 := by
    apply le_of_tendsto_of_tendsto' tendsto_const_nhds hlim'
    intro k
    apply (le_div_iff₀ (by positivity : 0 < (2:ℝ)^k)).mpr
    rw [mul_comm]
    exact (hiter k).trans (sub_le_self _ (mul_nonneg hB (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
  exact sub_nonpos.mp hend

end GaloisForLFunctions.ExceptionalLayerTheory
