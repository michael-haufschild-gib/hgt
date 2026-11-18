import GaloisForLFunctions.ExceptionalLayerTheory.BalancedProductsInTheLargePrimeCells
import GaloisForLFunctions.ExceptionalLayerTheory.PrimePowerMassInTheBalancedProduct

/-!
# Removing all products supported on a single prime

The prime-square diagonal matches the original proper-power coefficient
with the opposite sign. The matched error has a power saving over the
square root. Every surviving product has two distinct prime divisors.
-/

noncomputable section
open Finset ArithmeticFunction RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- After matching prime squares the entire single-prime contribution
has error of order at most X to the power 2/5. -/
theorem matched_single_prime_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℕ, 1 ≤ X →
      let D := ⌊(X : ℝ)^(1/400000 : ℝ)⌋₊
      |highPair X (singlePrimeError D)| ≤ K*(X : ℝ)^(2/5 : ℝ) := by
  obtain ⟨F,hF,hsize⟩ := centeredPrimeWeight_uniform
  obtain ⟨K,hK,hmass⟩ := mass_uniform
  let A := 1+2*(1+2*K)*45/Real.log 2
  let B := 5*(Real.log 4+4)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨F*A*(112+B),by positivity,fun X hX => ?_⟩
  intro D
  let R := ⌊(X : ℝ)^(1/100000 : ℝ)⌋₊
  let Y := ⌊(X : ℝ)^(50001/100000 : ℝ)⌋₊
  let s := (X : ℝ)^(1/45 : ℝ)
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hx0 := zero_lt_one.trans_le hx
  have hs : 1 ≤ s := Real.one_le_rpow hx (by norm_num)
  have hs0 := zero_le_one.trans hs
  have hR : 1 ≤ R := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hx (by norm_num))
  have hD : 1 ≤ D := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hx (by norm_num))
  have hr : (R : ℝ) ≤ s := (Nat.floor_le (show 0 ≤ (X : ℝ)^(1/100000 : ℝ) by positivity)).trans
    (Real.rpow_le_rpow_of_exponent_le hx (by norm_num))
  have hd : (D : ℝ) ≤ s := (Nat.floor_le (show 0 ≤ (X : ℝ)^(1/400000 : ℝ) by positivity)).trans
    (Real.rpow_le_rpow_of_exponent_le hx (by norm_num))
  have hd1 : ((D+1 : ℕ) : ℝ) ≤ 2*s := by push_cast; linarith only [hs,hd]
  have hm := (hmass (D+1) (Nat.succ_pos D)).trans (mul_le_mul_of_nonneg_left hd1 hK)
  have hm' : 2*(1+mass (D+1)) ≤ 2*(1+2*K)*s := by linarith only [hm,hs]
  have hl := Real.log_le_rpow_div (Nat.cast_nonneg X) (by norm_num : (0 : ℝ)<1/45)
  change Real.log X ≤ s/(1/45 : ℝ) at hl
  have he : 1+2*(1+mass (D+1))*Real.log X/Real.log 2 ≤ A*s^2 := by
    have hh := div_le_div_of_nonneg_right (mul_le_mul hm' (show Real.log X ≤ 45*s by linarith only [hl])
      (Real.log_natCast_nonneg X) (by positivity)) h2.le
    exact (add_le_add (one_le_pow₀ (n := 2) hs) hh).trans_eq (by dsimp [A]; ring)
  have h₁₅ : s^15 = (X : ℝ)^(1/3 : ℝ) := by
    dsimp [s]; rw [←Real.rpow_natCast _ 15,←Real.rpow_mul hx0.le]; norm_num
  have h₁₈ : s^18 = (X : ℝ)^(2/5 : ℝ) := by
    dsimp [s]; rw [←Real.rpow_natCast _ 18,←Real.rpow_mul hx0.le]; norm_num
  let T := (2*(D+1))^2
  have hT : (T : ℝ) ≤ 16*s^2 := by
    have hh : (((2*(D+1) : ℕ) : ℝ)) ≤ 4*s := by push_cast at hd1 ⊢; linarith only [hd1]
    have hh' := pow_le_pow_left₀ (Nat.cast_nonneg (2*(D+1)) : (0 : ℝ) ≤ (2*(D+1) : ℕ)) hh 2
    dsimp [T]; push_cast at hh' ⊢; linarith only [hh']
  have ht : 7*(T : ℝ)+B*(X : ℝ)^(1/3 : ℝ) ≤ (112+B)*s^15 := by
    rw [←h₁₅]
    linarith only [hT,pow_le_pow_right₀ hs (by norm_num : 2 ≤ 15)]
  have hb := singlePrimeError_mass hD hX
  change _ ≤ _ * (7*(T : ℝ)+B*(X : ℝ)^(1/3 : ℝ)) at hb
  have hsum := hb.trans (mul_le_mul he ht (by positivity) (by positivity))
  change |∑ n ∈ Ioc Y X, singlePrimeError D n*centeredPrimeWeight R (X/n)| ≤ _
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ n ∈ Ioc Y X, (F*s)* |singlePrimeError D n| := by
      apply sum_le_sum
      intro n _
      rw [abs_mul,mul_comm]
      exact mul_le_mul_of_nonneg_right ((hsize hR _).trans (mul_le_mul_of_nonneg_left hr hF)) (abs_nonneg _)
    _ ≤ (F*s)*(A*s^2*((112+B)*s^15)) := by
      rw [←mul_sum]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hF hs0)
      exact (sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_left (Nat.zero_le Y)) (fun _ _ _ => abs_nonneg _)).trans hsum
    _ = _ := by rw [←h₁₈]; ring

/-- Two-factor coefficient on products with more than one prime divisor. -/
def distinctPrimeProduct (D n : ℕ) : ℝ := if IsPrimePow n then 0 else balancedProduct D n

/-- The large-cell row supported away from all single-prime products. -/
def distinctPrimeProductRow (X : ℕ) : ℝ := highPair X (distinctPrimeProduct ⌊(X : ℝ)^(1/400000 : ℝ)⌋₊)

/-- The surviving product has at least two distinct prime divisors, at
both endpoints of the original product window. -/
theorem distinctPrimeProductRow_support {X : ℕ} (hX : 1 ≤ X) :
    let D := ⌊(X : ℝ)^(1/400000 : ℝ)⌋₊
    let R := ⌊(X : ℝ)^(1/100000 : ℝ)⌋₊
    let Y := ⌊(X : ℝ)^(50001/100000 : ℝ)⌋₊
    distinctPrimeProductRow X = ∑ n ∈ (Ioc Y (X/R)).filter (fun n => n.primeFactors.Nontrivial),
      ∑ p ∈ n.divisorsAntidiagonal with (D < p.1 ∧ D < p.2) ∧ p.1 ≠ p.2,
        vonMangoldt p.1*innerJump D p.2*centeredPrimeWeight R (X/n) := by
  classical
  intro D R Y
  have hY : 1 ≤ Y := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow (by exact_mod_cast hX) (by norm_num))
  rw [distinctPrimeProductRow,highPair_interval hX,sum_filter]
  apply sum_congr rfl
  intro n hn
  have hny : Y < n := (mem_Ioc.mp hn).1
  have hh := Nat.not_isPrimePow_iff_nontrivial_of_two_le (show 2 ≤ n by omega)
  by_cases hp : IsPrimePow n
  · simp only [distinctPrimeProduct,if_pos hp,zero_mul,if_neg (fun h => (hh.mpr h) hp)]
  · simp only [distinctPrimeProduct,if_neg hp,if_pos (hh.mp hp),balancedProduct,sum_mul]
    symm
    apply sum_subset ?_ ?_
    · intro p hmem
      obtain ⟨hm,hcut,_⟩ := mem_filter.mp hmem
      exact mem_filter.mpr ⟨hm,hcut⟩
    · intro p hmem hnot
      obtain ⟨hm,hcut⟩ := mem_filter.mp hmem
      have he : p.1=p.2 := by
        by_contra hne; exact hnot (mem_filter.mpr ⟨hm,hcut,hne⟩)
      have hs : p.1^2=n := by simpa only [sq,he] using (Nat.mem_divisorsAntidiagonal.mp hm).1
      have hz := vonMangoldt_eq_zero_iff.mpr hp
      rw [←hs,vonMangoldt_apply_pow (by norm_num)] at hz
      rw [hz,zero_mul,zero_mul]

private theorem matched_identity (X : ℕ) :
    let D := ⌊(X : ℝ)^(1/400000 : ℝ)⌋₊
    balancedProductRow X-distinctPrimeProductRow X =
      highPair X (singlePrimeError D)-highPair X primePowerPart := by
  intro D
  unfold balancedProductRow distinctPrimeProductRow highPair
  rw [←sum_sub_distrib,←sum_sub_distrib]
  apply sum_congr rfl
  intro n _
  by_cases h : IsPrimePow n
  · simp only [distinctPrimeProduct,singlePrimeError,if_pos h]; ring
  · have hz := vonMangoldt_eq_zero_iff.mpr h
    simp [distinctPrimeProduct,singlePrimeError,h,primePowerPart,hz]

/-- All single-prime products, including the diagonal, can be removed from
the signed balanced convolution at square-root cost. -/
theorem distinct_prime_product_row :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℕ, 1 ≤ X →
      |(Chebyshev.psi X-X)-distinctPrimeProductRow X| ≤ K*Real.sqrt X := by
  obtain ⟨K,hK,h⟩ := balanced_product_row
  obtain ⟨A,hA,ha⟩ := high_proper_power_bound
  obtain ⟨C,hC,hc⟩ := matched_single_prime_bound
  refine ⟨K+(C+A),by positivity,fun X hX => ?_⟩
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hpow : (X : ℝ)^(2/5 : ℝ) ≤ Real.sqrt X := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hdiff : |balancedProductRow X-distinctPrimeProductRow X| ≤ (C+A)*Real.sqrt X := by
    rw [matched_identity,add_mul]
    exact (abs_sub _ _).trans (add_le_add ((hc X hX).trans (mul_le_mul_of_nonneg_left hpow hC)) (ha X hX))
  rw [show (Chebyshev.psi X-X)-distinctPrimeProductRow X =
    ((Chebyshev.psi X-X)-balancedProductRow X)+(balancedProductRow X-distinctPrimeProductRow X) by ring,add_mul]
  exact (abs_add_le _ _).trans (add_le_add (h X hX) hdiff)

/-- Both Vaughan widths reduce to the trilinear sum with no single-prime product. -/
theorem distinct_prime_product_cofactors :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ V W N : ℕ,
      |cofactorCountError V W N - ∑ d ∈ Icc 1 (min N W), Sieve.typeIIShort V d*distinctPrimeProductRow (N/d)| ≤
        (∑ d ∈ Icc 1 W, |Sieve.typeIIShort V d|)*(K*Real.sqrt N) := by
  obtain ⟨K,hK,h⟩ := distinct_prime_product_row
  exact ⟨K,hK,cofactor_transfer hK h⟩

#print axioms distinctPrimeProductRow_support
#print axioms matched_single_prime_bound
#print axioms distinct_prime_product_cofactors

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
