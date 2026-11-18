import GaloisForLFunctions.ExceptionalLayerTheory.PrimeExcessInGrowingBlocks
import GaloisForLFunctions.ExceptionalLayerTheory.IntervalDiscrepancyOfTwoGrowingFactors
import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheFloorGraphNormAndTopOctaveBlindnessOfWindowGluing

/-!
# Two growing factors in the large prime cells

The signed error of the original prime row is carried entirely by
composite products in the same interval. The corrected inner coefficients
annihilate the logarithmic density and reproduce the constant density,
which the outer factorial weight absorbs at square-root precision.
-/

noncomputable section
open Finset ArithmeticFunction RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Proper prime powers on the large cells still have square-root cost after
the lower band is removed. Their absolute mass below the split is smaller. -/
theorem high_proper_power_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℕ, 1 ≤ X → |highPair X primePowerPart| ≤ K*Real.sqrt X := by
  obtain ⟨F,hF,hsize⟩ := centeredPrimeWeight_uniform
  obtain ⟨A,hA,hpowers⟩ := proper_powers_of_zero_moment hF
  let P := 3*(Real.log 4+4)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  refine ⟨A+F*P,by positivity,fun X hX => ?_⟩
  let R := ⌊(X : ℝ)^(1/100000 : ℝ)⌋₊
  let Y := ⌊(X : ℝ)^(50001/100000 : ℝ)⌋₊
  let f := fun m => centeredPrimeWeight R (X/m)*primePowerPart m
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hx0 := zero_lt_one.trans_le hx
  have hr : 1 ≤ R := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hx (by norm_num))
  have hR : (R : ℝ) ≤ (X : ℝ)^(1/100000 : ℝ) := Nat.floor_le (by positivity)
  have hY : (Y : ℝ) ≤ (X : ℝ)^(50001/100000 : ℝ) := Nat.floor_le (by positivity)
  have hyX : Y ≤ X := Nat.floor_le_of_le ((Real.rpow_le_rpow_of_exponent_le hx
    (by norm_num : (50001/100000 : ℝ) ≤ 1)).trans_eq (Real.rpow_one _))
  have hprod : (R : ℝ)*Real.sqrt Y ≤ Real.sqrt X := by
    apply (mul_le_mul hR (Real.sqrt_le_sqrt hY) (Real.sqrt_nonneg _) (by positivity)).trans
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul hx0.le,←Real.rpow_add hx0,Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hm : (∑ n ∈ Ioc 0 Y, primePowerPart n) ≤ P*Real.sqrt Y := by
    have he : (∑ n ∈ Ioc 0 Y, primePowerPart n) = Chebyshev.psi Y-Chebyshev.theta Y := by
      rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,Nat.floor_natCast,sum_filter]
      exact sum_congr rfl fun n _ => by by_cases h : n.Prime <;> simp [primePowerPart,h]
    rw [he]
    exact GreenCalculusOfThePrimeFreeWindow.psi_sub_theta_le_three_mul_sqrt Y
  have small : |∑ n ∈ Ioc 0 Y, f n| ≤ F*P*Real.sqrt X := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc _ ≤ ∑ n ∈ Ioc 0 Y, (F*R)*primePowerPart n := by
              apply sum_le_sum
              intro n _
              have hn : 0 ≤ primePowerPart n := by
                unfold primePowerPart; split <;> first | exact le_rfl | exact vonMangoldt_nonneg
              rw [show |f n|=|centeredPrimeWeight R (X/n)| * primePowerPart n by
                dsimp [f]; rw [abs_mul,abs_of_nonneg hn]]
              exact mul_le_mul_of_nonneg_right (hsize hr _) hn
         _ ≤ (F*R)*(P*Real.sqrt Y) := by
              rw [←mul_sum]; exact mul_le_mul_of_nonneg_left hm (by positivity)
         _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_left hprod (mul_nonneg hF hP)]
  have full := hpowers X X R hX le_rfl (hR.trans (Real.rpow_le_rpow_of_exponent_le hx (by norm_num)))
    (centeredPrimeWeight R) (hsize hr) (centered_weight_moment hr)
  have he : highPair X primePowerPart = (∑ m ∈ Ioc 0 X, f m)-(∑ m ∈ Ioc 0 Y, f m) := by
    rw [←sum_Ioc_consecutive f (Nat.zero_le Y) hyX,add_sub_cancel_left]
    exact sum_congr rfl fun _ _ => mul_comm ..
  rw [he,add_mul]
  exact (abs_sub _ _).trans (add_le_add full small)

/-- The high product window may be paired with the full Mangoldt measure. -/
theorem high_mangoldt_row :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℕ, 1 ≤ X →
      |(Chebyshev.psi X-X)-highPair X vonMangoldt| ≤ K*Real.sqrt X := by
  obtain ⟨C,hC,hp⟩ := ordinary_primes_above_sqrt_row
  obtain ⟨A,hA,ha⟩ := high_proper_power_bound
  refine ⟨C+A,add_nonneg hC hA,fun X hX => ?_⟩
  have he : highPair X vonMangoldt = highPair X (horizonPrime X)+highPair X primePowerPart := by
    unfold highPair; rw [←sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    rw [←add_mul]
    congr 1
    by_cases h : n.Prime <;> simp [horizonPrime,(mem_Ioc.mp hn).2,primePowerPart,h,vonMangoldt_apply_prime]
  rw [he,prime_pair hX,←sub_sub,add_mul]
  exact (abs_sub _ _).trans (add_le_add (hp X hX) (ha X hX))

/-- The signed mass on composite products with both factors above the
inner cutoff, restricted to the high cells of the divided horizon. -/
def balancedProductRow (X : ℕ) : ℝ :=
  highPair X (balancedProduct ⌊(X : ℝ)^(1/400000 : ℝ)⌋₊)

/-- The complete two-factor expansion, including both product-window endpoints. -/
theorem balancedProductRow_eq {X : ℕ} (hX : 1 ≤ X) :
    let D := ⌊(X : ℝ)^(1/400000 : ℝ)⌋₊
    let R := ⌊(X : ℝ)^(1/100000 : ℝ)⌋₊
    let Y := ⌊(X : ℝ)^(50001/100000 : ℝ)⌋₊
    balancedProductRow X = ∑ n ∈ Ioc Y (X/R),
      ∑ p ∈ n.divisorsAntidiagonal with D < p.1 ∧ D < p.2,
        vonMangoldt p.1*innerJump D p.2*centeredPrimeWeight R (X/n) := by
  intro D R Y
  rw [balancedProductRow,highPair_interval hX]
  simp only [balancedProduct,sum_mul]
  rfl

private def outerPrefix (R k : ℕ) : ℝ := if k=0 then 0 else centeredPrimeWeight R k

/-- Coefficient of the third factor, obtained by differencing the outer
quotient weight. -/
def outerJump (R k : ℕ) : ℝ := outerPrefix R k-outerPrefix R (k-1)

private theorem sum_outerJump (R t : ℕ) :
    ∑ k ∈ Icc 1 t, outerJump R k = outerPrefix R t := by
  induction t with
  | zero => simp [outerPrefix]
  | succ t ih =>
    rw [sum_Icc_succ_top (by omega),ih,outerJump,Nat.add_sub_cancel]
    ring

/-- All partial sums on the third factor are bounded linearly in its cutoff. -/
theorem outerJump_prefix_bound :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ {R : ℕ}, 1 ≤ R → ∀ t : ℕ, |∑ k ∈ Icc 1 t, outerJump R k| ≤ F*R := by
  obtain ⟨F,hF,h⟩ := centeredPrimeWeight_uniform
  refine ⟨F,hF,?_⟩
  intro R hR t
  rw [sum_outerJump,outerPrefix]
  split
  · rw [abs_zero]; positivity
  · exact h hR t

private theorem sum_long_outerJump {R t : ℕ} (hR : 1 ≤ R) (ht : 1 ≤ t) :
    ∑ k ∈ Icc R t, outerJump R k = centeredPrimeWeight R t := by
  have hz {k : ℕ} (hk : k < R) : outerPrefix R k = 0 := by
    unfold outerPrefix
    split
    · rfl
    · exact centeredPrimeWeight_small (by omega) hk
  rw [←show outerPrefix R t = centeredPrimeWeight R t by simp [outerPrefix,Nat.ne_of_gt ht],
    ←sum_outerJump]
  apply sum_subset (Icc_subset_Icc_left hR)
  intro k hk hn
  have hlt : k < R := by
    by_contra! hh; exact hn (mem_Icc.mpr ⟨hh,(mem_Icc.mp hk).2⟩)
  rw [outerJump,hz hlt,hz (by omega : k-1<R),sub_self]

/-- On the hyperbolic region uvk ≤ X all three factors grow. The last two
coefficients separately have uniformly bounded partial sums at their cutoffs. -/
theorem balancedProductRow_trilinear {X : ℕ} (hX : 1 ≤ X) :
    let D := ⌊(X : ℝ)^(1/400000 : ℝ)⌋₊
    let R := ⌊(X : ℝ)^(1/100000 : ℝ)⌋₊
    let Y := ⌊(X : ℝ)^(50001/100000 : ℝ)⌋₊
    balancedProductRow X = ∑ n ∈ Ioc Y (X/R),
      ∑ p ∈ n.divisorsAntidiagonal with D < p.1 ∧ D < p.2,
        ∑ k ∈ Icc R (X/n), vonMangoldt p.1*innerJump D p.2*outerJump R k := by
  intro D R Y
  have hR : 1 ≤ R := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow (by exact_mod_cast hX) (by norm_num))
  rw [balancedProductRow_eq hX]
  apply sum_congr rfl
  intro n hn
  obtain ⟨hl,hu⟩ := mem_Ioc.mp hn
  have ht : 1 ≤ X/n := (Nat.one_le_div_iff (by omega : 0 < n)).mpr (hu.trans (Nat.div_le_self ..))
  apply sum_congr rfl
  intro p _
  rw [←mul_sum,sum_long_outerJump hR ht]

/-- Polynomially long factors carry the whole prime error with absolute
square-root error and no additional smooth main term. -/
theorem balanced_product_row :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℕ, 1 ≤ X →
      |(Chebyshev.psi X-X)-balancedProductRow X| ≤ K*Real.sqrt X := by
  obtain ⟨K,hK,h⟩ := high_mangoldt_row
  obtain ⟨C,hC,hdisc⟩ := balancedDensity_discrepancy
  obtain ⟨A,hA,ha⟩ := high_density_bound C hC
  refine ⟨K+A,add_nonneg hK hA,fun X hX => ?_⟩
  let D := ⌊(X : ℝ)^(1/400000 : ℝ)⌋₊
  have hh := ha X hX (balancedDensity D X) (hdisc X hX)
  have he : highPair X (balancedDensity D X) = highPair X vonMangoldt-balancedProductRow X := by
    unfold highPair balancedProductRow
    change _ = _ - ∑ n ∈ Ioc _ X, balancedProduct D n*centeredPrimeWeight _ (X/n)
    rw [←sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    rw [balancedDensity,if_pos (mem_Ioc.mp hn).2]
    ring
  rw [he] at hh
  rw [show (Chebyshev.psi X-X)-balancedProductRow X =
    ((Chebyshev.psi X-X)-highPair X vonMangoldt)+(highPair X vonMangoldt-balancedProductRow X) by ring,add_mul]
  exact (abs_add_le _ _).trans (add_le_add (h X hX) hh)

/-- Every Vaughan width admits the same approximation by composite products
at the individual divided horizons. -/
theorem balanced_product_cofactors :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ V W N : ℕ,
      |cofactorCountError V W N - ∑ d ∈ Icc 1 (min N W), Sieve.typeIIShort V d*balancedProductRow (N/d)| ≤
        (∑ d ∈ Icc 1 W, |Sieve.typeIIShort V d|)*(K*Real.sqrt N) := by
  obtain ⟨K,hK,h⟩ := balanced_product_row
  exact ⟨K,hK,cofactor_transfer hK h⟩

#print axioms balancedProductRow_trilinear
#print axioms balanced_product_cofactors

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
