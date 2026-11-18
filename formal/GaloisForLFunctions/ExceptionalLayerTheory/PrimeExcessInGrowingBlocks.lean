import GaloisForLFunctions.RHTower.Sieve.PrimeWindowUpper
import GaloisForLFunctions.ExceptionalLayerTheory.DensityCancellationInTheLargeQuotientCells
import GaloisForLFunctions.ExceptionalLayerTheory.IntervalDiscrepancyFromCompleteBlocks
import GaloisForLFunctions.ExceptionalLayerTheory.OrdinaryPrimeCofactorsAboveTheSquareRoot

/-!
# Prime excesses in growing blocks

Replacing the individual prime positions by their average in each consecutive
block costs square-root error in the signed large-prime pairing. The same
precision permits subtracting the normalized density of rough integers.
-/

noncomputable section
open Finset RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Logarithmic ordinary-prime measure up to the divided horizon. -/
def horizonPrime (X n : ℕ) : ℝ := if n ≤ X ∧ n.Prime then Real.log n else 0

/-- The centered quotient weight vanishes beyond the upper end of the large cells. -/
theorem highPair_interval {X : ℕ} (hX : 1 ≤ X) (f : ℕ → ℝ) :
    let R := ⌊(X : ℝ)^(1/100000 : ℝ)⌋₊
    let Y := ⌊(X : ℝ)^(50001/100000 : ℝ)⌋₊
    highPair X f = ∑ m ∈ Ioc Y (X/R), f m*centeredPrimeWeight R (X/m) := by
  intro R Y
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hr : 1 ≤ R := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hx (by norm_num))
  symm
  apply sum_subset (Ioc_subset_Ioc_right (Nat.div_le_self X R))
  intro m hm hnot
  obtain ⟨hl,hu⟩ := mem_Ioc.mp hm
  have hgt : X/R < m := by
    by_contra! hh; exact hnot (mem_Ioc.mpr ⟨hl,hh⟩)
  have hm0 : 0 < m := by omega
  have hlt : X/m < R := (Nat.div_lt_iff_lt_mul hm0).mpr
    (by simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hr).mp hgt)
  rw [centeredPrimeWeight_small ((Nat.one_le_div_iff hm0).mpr hu) hlt,mul_zero]

/-- Pairing the truncated ordinary-prime measure recovers the large-prime row. -/
theorem prime_pair {X : ℕ} (hX : 1 ≤ X) : highPair X (horizonPrime X) = aboveSquareRoot X := by
  rw [highPair_interval hX,aboveSquareRoot,sum_filter]
  apply sum_congr rfl
  intro m hm
  have hle := (mem_Ioc.mp hm).2.trans (Nat.div_le_self ..)
  by_cases hp : m.Prime <;> simp [horizonPrime,hle,hp]

/-- The signed block mean of the ordinary-prime measure in the large cells. -/
def blockPrimeExcess (X : ℕ) : ℝ :=
  let H := ⌊(X : ℝ)^(1/400000 : ℝ)⌋₊
  highPair X (fun n => blockMean H (horizonPrime X) n-1)

/-- A growing primorial for which complete-period discrepancy has square-root cost. -/
def roughModulus (X : ℕ) : ℕ := primorial ⌊Real.log X/400000⌋₊

/-- The log-prime measure relative to the density on rough integers. -/
def roughPrimeExcess (X : ℕ) : ℝ :=
  highPair X (fun n => horizonPrime X n-coprimeDensity (roughModulus X) n)

/-- Every surviving integer in the rough pairing avoids all primes up to
floor(log X/400000), including in the ordinary-prime term. -/
theorem roughPrimeExcess_support {X : ℕ} (hX : 1 ≤ X) :
    let R := ⌊(X : ℝ)^(1/100000 : ℝ)⌋₊
    let Y := ⌊(X : ℝ)^(50001/100000 : ℝ)⌋₊
    let P := roughModulus X
    roughPrimeExcess X = ∑ n ∈ (Ioc Y (X/R)).filter P.Coprime,
      (horizonPrime X n-(P : ℝ)/P.totient)*centeredPrimeWeight R (X/n) := by
  intro R Y P
  rw [roughPrimeExcess,highPair_interval hX,sum_filter]
  apply sum_congr rfl
  intro n hn
  change (horizonPrime X n-coprimeDensity P n)*centeredPrimeWeight R (X/n) =
    if P.Coprime n then (horizonPrime X n-(P : ℝ)/P.totient)*centeredPrimeWeight R (X/n) else 0
  by_cases hc : P.Coprime n
  · simp only [coprimeDensity,if_pos hc]
  have hlog := Real.log_le_rpow_div (Nat.cast_nonneg X) (by norm_num : (0 : ℝ) < 50001/100000)
  have hz : ⌊Real.log X/400000⌋₊ ≤ Y := Nat.floor_mono (by
    linarith only [hlog,Real.rpow_nonneg (Nat.cast_nonneg X : (0 : ℝ) ≤ X) (50001/100000 : ℝ)])
  have hnp : ¬n.Prime := fun hp => hc (Sieve.coprime_primorial_of_prime hp (hz.trans_lt (mem_Ioc.mp hn).1))
  simp [coprimeDensity,horizonPrime,hnp,hc]

private theorem roughModulus_bound {X : ℕ} (hX : 1 ≤ X) : (roughModulus X : ℝ) ≤ (X : ℝ)^(1/200000 : ℝ) := by
  let z := ⌊Real.log X/400000⌋₊
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  have hz : (z : ℝ) ≤ Real.log X/400000 := Nat.floor_le (div_nonneg (Real.log_natCast_nonneg X) (by norm_num))
  have h4 : Real.log 4 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    rw [show (4 : ℝ) = 2*2 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
    linarith only [h]
  calc (roughModulus X : ℝ) ≤ (4 : ℝ)^z := by exact_mod_cast primorial_le_four_pow z
       _ = Real.exp (Real.log 4*(z : ℝ)) := by rw [←Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4)]
       _ ≤ _ := by
           rw [Real.rpow_def_of_pos hx,Real.exp_le_exp]
           linarith only [mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg z),hz]

private theorem sub_pair (X : ℕ) (f g : ℕ → ℝ) :
    highPair X (fun n => f n-g n) = highPair X f-highPair X g := by
  simp only [highPair,sub_mul,sum_sub_distrib]

private theorem pair_transfer {X : ℕ} (hX : 1 ≤ X) {g : ℕ → ℝ} {K C : ℝ}
    (h : |(Chebyshev.psi X-X)-aboveSquareRoot X| ≤ K*Real.sqrt X)
    (hg : |highPair X (fun n => horizonPrime X n-g n)| ≤ C*Real.sqrt X) :
    |(Chebyshev.psi X-X)-highPair X g| ≤ (K+C)*Real.sqrt X := by
  rw [sub_pair,prime_pair hX] at hg
  rw [show (Chebyshev.psi X-X)-highPair X g =
    ((Chebyshev.psi X-X)-aboveSquareRoot X)+(aboveSquareRoot X-highPair X g) by ring]
  exact (abs_add_le _ _).trans ((add_le_add h hg).trans_eq (add_mul ..).symm)

/-- Square-root replacement by the actual prime excess per growing block.
Only the mass of each full block enters the prime-count row. -/
theorem block_prime_excess_row :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℕ, 1 ≤ X → |(Chebyshev.psi X-X)-blockPrimeExcess X| ≤ K*Real.sqrt X := by
  obtain ⟨K,hK,h⟩ := ordinary_primes_above_sqrt_row
  obtain ⟨C,hC,hc⟩ := high_density_bound 800000 (by norm_num)
  refine ⟨K+C,add_nonneg hK hC,fun X hX => ?_⟩
  let H := ⌊(X : ℝ)^(1/400000 : ℝ)⌋₊
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hx0 := zero_lt_one.trans_le hx
  have hH : 0 < H := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hx (by norm_num))
  have hsize : 2*((H : ℝ)*Real.log X) ≤ 800000*(X : ℝ)^(1/200000 : ℝ) := by
    have hl := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1/400000)
    have hh : (H : ℝ) ≤ (X : ℝ)^(1/400000 : ℝ) := Nat.floor_le (by positivity)
    have hh' := mul_le_mul hh hl (Real.log_natCast_nonneg X) (Real.rpow_nonneg hx0.le _)
    have he := (Real.rpow_add hx0 (1/400000 : ℝ) (1/400000 : ℝ)).symm
    norm_num at he
    linarith only [hh',he]
  apply pair_transfer hX (h X hX)
  apply hc X hX
  intro L U hlu
  have hn (n : ℕ) : 0 ≤ horizonPrime X n := by unfold horizonPrime; split <;> simp [Real.log_natCast_nonneg]
  have hu (n : ℕ) : horizonPrime X n ≤ Real.log X := by
    unfold horizonPrime
    split
    next ht => exact Real.log_le_log (by exact_mod_cast ht.2.pos) (by exact_mod_cast ht.1)
    next => exact Real.log_natCast_nonneg X
  have hb := (discrepancy_block_mean hH hn hu hlu).trans hsize
  have he (n : ℕ) : horizonPrime X n-(blockMean H (horizonPrime X) n-1) =
      (horizonPrime X n-blockMean H (horizonPrime X) n)+1 := by ring
  change |(∑ m ∈ Ioc L U, (horizonPrime X m-(blockMean H (horizonPrime X) m-1)))-((U : ℝ)-L)| ≤ _
  simp_rw [he]
  simpa only [sum_add_distrib,sum_const,Nat.card_Ioc,nsmul_eq_mul,mul_one,Nat.cast_sub hlu,add_sub_cancel_right] using hb

/-- Both terms are sieved at the logarithmic prime cutoff, with
square-root error uniform in the divided horizon. -/
theorem rough_prime_excess_row :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℕ, 1 ≤ X → |(Chebyshev.psi X-X)-roughPrimeExcess X| ≤ K*Real.sqrt X := by
  obtain ⟨K,hK,h⟩ := ordinary_primes_above_sqrt_row
  obtain ⟨C,hC,hc⟩ := high_density_bound 2 (by norm_num)
  refine ⟨K+C,add_nonneg hK hC,fun X hX => ?_⟩
  apply pair_transfer hX (h X hX)
  simp only [sub_sub_self]
  apply hc X hX
  intro L U hlu
  exact (coprime_density_discrepancy (P := roughModulus X) (primorial_pos _) hlu).trans
    (mul_le_mul_of_nonneg_left (roughModulus_bound hX) (by norm_num))

/-- A square-root approximation on every divided horizon passes to the signed cofactor count. -/
theorem cofactor_transfer {f : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ X : ℕ, 1 ≤ X → |(Chebyshev.psi X-X)-f X| ≤ K*Real.sqrt X) (V W N : ℕ) :
    |cofactorCountError V W N - ∑ d ∈ Icc 1 (min N W), Sieve.typeIIShort V d*f (N/d)| ≤
      (∑ d ∈ Icc 1 W, |Sieve.typeIIShort V d|)*(K*Real.sqrt N) := by
  rw [cofactorCountError_eq,← sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ d ∈ Icc 1 (min N W), |Sieve.typeIIShort V d| * (K*Real.sqrt N) := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro d hd
      obtain ⟨hl,hu⟩ := mem_Icc.mp hd
      have h1 := (Nat.one_le_div_iff hl).mpr (hu.trans (min_le_left ..))
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (h _ h1).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast Nat.div_le_self N d)) hK)
    _ ≤ _ := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (sum_le_sum_of_subset_of_nonneg
        (Icc_subset_Icc_right (min_le_right N W)) (fun _ _ _ => abs_nonneg _)) (by positivity)

/-- The full cofactor count is carried by prime excesses on blocks of
length floor(X^(1/400000)), separately at each cofactor horizon X. -/
theorem block_prime_excess_cofactors :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ V W N : ℕ,
      |cofactorCountError V W N - ∑ d ∈ Icc 1 (min N W), Sieve.typeIIShort V d*blockPrimeExcess (N/d)| ≤
        (∑ d ∈ Icc 1 W, |Sieve.typeIIShort V d|)*(K*Real.sqrt N) := by
  obtain ⟨K,hK,h⟩ := block_prime_excess_row
  exact ⟨K,hK,cofactor_transfer hK h⟩

/-- The rough-integer subtraction also holds simultaneously on all cofactors. -/
theorem rough_prime_excess_cofactors :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ V W N : ℕ,
      |cofactorCountError V W N - ∑ d ∈ Icc 1 (min N W), Sieve.typeIIShort V d*roughPrimeExcess (N/d)| ≤
        (∑ d ∈ Icc 1 W, |Sieve.typeIIShort V d|)*(K*Real.sqrt N) := by
  obtain ⟨K,hK,h⟩ := rough_prime_excess_row
  exact ⟨K,hK,cofactor_transfer hK h⟩

#print axioms roughPrimeExcess_support
#print axioms block_prime_excess_cofactors
#print axioms rough_prime_excess_cofactors

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
