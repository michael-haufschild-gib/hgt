import GaloisForLFunctions.ExceptionalLayerTheory.IntervalDiscrepancyOfTwoGrowingFactors
import GaloisForLFunctions.RHTower.WeilPositivityPrimePowersForced
import GaloisForLFunctions.RHTower.SelbergPairingPrimeSquare
import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheFloorGraphNormAndTopOctaveBlindnessOfWindowGluing

/-!
# The single-prime part of the balanced convolution

At a large prime square the two-factor coefficient is minus log p.
After matching those squares, the remaining prime powers have total
Mangoldt mass of cube-root order, up to the initial short prime squares.
-/

noncomputable section
open Finset ArithmeticFunction RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Differencing two bounded prefixes bounds each complementary coefficient. -/
theorem innerJump_pointwise_bound (D v : ℕ) : |innerJump D v| ≤ 2*(1+mass (D+1)) := by
  rcases v with _ | v
  · rw [show innerJump D 0 = 0 from sub_self _,abs_zero]
    have h := (abs_nonneg _).trans (innerJump_prefix_bound D 0)
    linarith only [h]
  · have hi := sum_Icc_succ_top (by omega : 1 ≤ v+1) (innerJump D)
    have he : innerJump D (v+1) = (∑ i ∈ Icc 1 (v+1), innerJump D i)-(∑ i ∈ Icc 1 v, innerJump D i) := by
      linarith only [hi]
    rw [he]
    exact (abs_sub _ _).trans (by linarith only [innerJump_prefix_bound D (v+1),innerJump_prefix_bound D v])

/-- The divisor convolution has a pointwise logarithmic bound because
the sum of the Mangoldt weights over the divisors is exactly log n. -/
theorem balancedProduct_bound (D n : ℕ) :
    |balancedProduct D n| ≤ (2*(1+mass (D+1)))*Real.log n := by
  let M := 2*(1+mass (D+1))
  have hM : 0 ≤ M := (abs_nonneg _).trans (innerJump_pointwise_bound D 0)
  unfold balancedProduct
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal with D < p.1 ∧ D < p.2, M*vonMangoldt p.1 := by
      apply sum_le_sum
      intro p _
      rw [abs_mul,abs_of_nonneg vonMangoldt_nonneg,mul_comm]
      exact mul_le_mul_of_nonneg_right (innerJump_pointwise_bound D _) vonMangoldt_nonneg
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal, M*vonMangoldt p.1 :=
      sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => mul_nonneg hM vonMangoldt_nonneg)
    _ = _ := by rw [←mul_sum,Nat.sum_divisorsAntidiagonal (fun a _ => vonMangoldt a),vonMangoldt_sum]

/-- Above the stencil support only its unit divisor jumps at a prime. -/
theorem innerJump_at_prime {D p : ℕ} (hD : 1 ≤ D) (hp : p.Prime) (hlarge : 2*(D+1) < p) :
    innerJump D p = -1 := by
  have hstep (d : ℕ) (hd : d ∈ Icc 1 (2*(D+1))) :
      ((p/d : ℕ) : ℝ)-(((p-1)/d : ℕ) : ℝ)-((1/d : ℕ) : ℝ) = 0 := by
    have hh := Nat.succ_div (a := p-1) (b := d)
    rw [Nat.sub_add_cancel hp.pos] at hh
    by_cases he : d = 1
    · subst d
      simp only [Nat.div_one,Nat.cast_one,Nat.cast_sub hp.pos]
      ring
    · have hd₁ := (mem_Icc.mp hd).1
      have hlt := (mem_Icc.mp hd).2.trans_lt hlarge
      have hnd : ¬d ∣ p := fun h => ((Nat.dvd_prime hp).mp h).elim he (by omega)
      rw [if_neg hnd,Nat.add_zero] at hh
      rw [hh,sub_self,Nat.div_eq_of_lt (by omega : 1 < d),Nat.cast_zero,sub_zero]
  have hh := abs_stencil_le (Nat.succ_pos D) (M := 0)
    (fun d => ((p/d : ℕ) : ℝ)-(((p-1)/d : ℕ) : ℝ)-((1/d : ℕ) : ℝ))
    (fun d hd => by rw [hstep d hd,abs_zero])
  rw [mul_zero,abs_nonpos_iff,stencil_sub,stencil_sub] at hh
  change factorialPrefix (D+1) p-factorialPrefix (D+1) (p-1)-factorialPrefix (D+1) 1=0 at hh
  rw [prefix_one le_rfl (by omega)] at hh
  change (if p=0 then 0 else 1-factorialPrefix (D+1) p)-
    (if p-1=0 then 0 else 1-factorialPrefix (D+1) (p-1)) = -1
  rw [if_neg hp.ne_zero,if_neg (by omega)]
  linarith only [hh]

/-- The prime-square diagonal has exactly the opposite sign to the
original proper-power measure. -/
theorem balancedProduct_prime_square {D p : ℕ} (hD : 1 ≤ D) (hp : p.Prime) (hlarge : 2*(D+1) < p) :
    balancedProduct D (p^2) = -vonMangoldt (p^2) := by
  simp only [balancedProduct,divisorsAntidiagonal_prime_sq hp,filter_insert,filter_singleton,
    if_neg (by omega : ¬(D < 1 ∧ D < p^2)),if_neg (by omega : ¬(D < p^2 ∧ D < 1)),
    if_pos (show D < p ∧ D < p by omega),insert_empty_eq,sum_singleton,innerJump_at_prime hD hp hlarge,
    vonMangoldt_apply_pow (by norm_num : (2 : ℕ) ≠ 0)]
  ring

private def primeSquares (X : ℕ) : Finset ℕ :=
  ((Ioc 0 ⌊Real.sqrt X⌋₊).filter Nat.Prime).image (fun p => p^2)

private def higherPowers (X : ℕ) : Finset ℕ :=
  ((Ioc 0 X).filter (fun n => ¬n.Prime)) \ primeSquares X

private theorem square_subset (X : ℕ) : primeSquares X ⊆ (Ioc 0 X).filter (fun n => ¬n.Prime) := by
  intro n hn
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hn
  obtain ⟨hh,hp⟩ := mem_filter.mp hp
  have he : (p : ℝ) ≤ Real.sqrt X := (by exact_mod_cast (mem_Ioc.mp hh).2 :
    (p : ℝ) ≤ (⌊Real.sqrt X⌋₊ : ℕ)).trans (Nat.floor_le (Real.sqrt_nonneg _))
  have hs := (Real.le_sqrt (Nat.cast_nonneg p) (Nat.cast_nonneg X)).mp he
  exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨pow_pos hp.pos _,by exact_mod_cast hs⟩,
    Nat.Prime.not_prime_pow (by norm_num : 2 ≤ 2)⟩

private theorem squares_mass (X : ℕ) :
    (∑ n ∈ primeSquares X, vonMangoldt n) = Chebyshev.theta (Real.sqrt X) := by
  rw [primeSquares,sum_image]
  · unfold Chebyshev.theta
    exact sum_congr rfl fun p hp => by rw [vonMangoldt_apply_pow (by norm_num),vonMangoldt_apply_prime (mem_filter.mp hp).2]
  · intro p _ q _ he
    exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) he

private abbrev cubeConstant : ℝ := 5*(Real.log 4+4)

private theorem higher_mass {X : ℕ} (hX : 1 ≤ X) :
    ∑ n ∈ higherPowers X, vonMangoldt n ≤ cubeConstant*(X : ℝ)^(1/3 : ℝ) := by
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hx0 := zero_lt_one.trans_le hx
  have hs := sum_sdiff (f := fun n => (vonMangoldt n : ℝ)) (square_subset X)
  rw [squares_mass] at hs
  have hid := Chebyshev.psi_sub_theta_eq_sum_not_prime (X : ℝ)
  rw [Nat.floor_natCast,←hs] at hid
  let L := Real.log 4+4
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have ht := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi (X : ℝ)
  rw [show (X : ℝ)^(2 : ℝ)⁻¹ = Real.sqrt X by rw [Real.sqrt_eq_rpow,one_div]] at ht
  have hsq := GreenCalculusOfThePrimeFreeWindow.psi_sub_theta_le_three_mul_sqrt (Real.sqrt X)
  have hpow : Real.sqrt (Real.sqrt X) ≤ (X : ℝ)^(1/3 : ℝ) := by
    simp only [Real.sqrt_eq_rpow,←Real.rpow_mul hx0.le]
    exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have h₃ := Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg hx0.le (3 : ℝ)⁻¹)
  have h₅ := Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg hx0.le (5 : ℝ)⁻¹)
  have h₃' := Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (3 : ℝ)⁻¹ ≤ 1/3)
  have h₅' := Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (5 : ℝ)⁻¹ ≤ 1/3)
  change _ = (∑ n ∈ higherPowers X, vonMangoldt n)+Chebyshev.theta (Real.sqrt X) at hid
  unfold cubeConstant
  dsimp [L] at hL
  linarith only [hid,ht,hsq,h₃,h₅,mul_le_mul_of_nonneg_left hpow (show 0 ≤ 3*(Real.log 4+4) by positivity),
    mul_le_mul_of_nonneg_left h₃' hL,mul_le_mul_of_nonneg_left h₅' hL]

/-- Coefficient left when a prime power in the product variable is
matched against the original proper-power part. -/
def singlePrimeError (D n : ℕ) : ℝ := if IsPrimePow n then balancedProduct D n+primePowerPart n else 0

private theorem error_bound {D n X : ℕ} (hn : n ≤ X) :
    |singlePrimeError D n| ≤ (1+2*(1+mass (D+1))*Real.log X/Real.log 2)*vonMangoldt n := by
  let M := 2*(1+mass (D+1))
  have hm : 0 ≤ M := (abs_nonneg _).trans (innerJump_pointwise_bound D 0)
  have hl := Real.log_natCast_nonneg X
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold singlePrimeError
  split
  next h =>
    have hlower : Real.log 2 ≤ vonMangoldt n := by
      rw [vonMangoldt_apply,if_pos h]
      exact Real.log_le_log (by norm_num) (by exact_mod_cast (Nat.minFac_prime h.ne_one).two_le)
    have hdiv : 1 ≤ vonMangoldt n / Real.log 2 := (le_div_iff₀ h2).mpr (by linarith only [hlower])
    have hp : |primePowerPart n| ≤ vonMangoldt n := by
      unfold primePowerPart; split <;> simp [abs_of_nonneg vonMangoldt_nonneg,vonMangoldt_nonneg]
    have hlog := Real.log_le_log (by exact_mod_cast h.pos : 0 < (n : ℝ)) (by exact_mod_cast hn : (n : ℝ) ≤ X)
    have hb := (balancedProduct_bound D n).trans (mul_le_mul_of_nonneg_left hlog hm)
    apply (abs_add_le _ _).trans
    have h₁ := mul_le_mul_of_nonneg_left hdiv (mul_nonneg hm hl)
    rw [mul_one] at h₁
    calc
      _ ≤ M*Real.log X*(vonMangoldt n/Real.log 2)+vonMangoldt n :=
        add_le_add (hb.trans h₁) hp
      _ = (1+M*Real.log X/Real.log 2)*vonMangoldt n := by ring
  next =>
    rw [abs_zero]
    change 0 ≤ (1+M*Real.log X/Real.log 2)*vonMangoldt n
    positivity

/-- The matched single-prime error has at most cube-root mass apart from
the short prime squares. -/
theorem singlePrimeError_mass {D X : ℕ} (hD : 1 ≤ D) (hX : 1 ≤ X) :
    (∑ n ∈ Ioc 0 X, |singlePrimeError D n|) ≤
      (1+2*(1+mass (D+1))*Real.log X/Real.log 2)*
        ((7 : ℝ)*(((2*(D+1))^2 : ℕ) : ℝ)+5*(Real.log 4+4)*(X : ℝ)^(1/3 : ℝ)) := by
  classical
  let T := (2*(D+1))^2
  let C := 1+2*(1+mass (D+1))*Real.log X/Real.log 2
  have hm := (abs_nonneg _).trans (innerJump_pointwise_bound D 0)
  have hC : 0 ≤ C := by dsimp [C]; have := Real.log_natCast_nonneg X; positivity
  let S := (Ioc 0 T) ∪ higherPowers X
  have hs (n : ℕ) (hn : n ∈ Ioc 0 X) (hnot : n ∉ S) : singlePrimeError D n = 0 := by
    have h₁ : n ∉ Ioc 0 T := fun h => hnot (mem_union_left _ h)
    have h₂ : n ∉ higherPowers X := fun h => hnot (mem_union_right _ h)
    by_cases hp : n.Prime
    · simp [singlePrimeError,balancedProduct_prime hD hp,primePowerPart,hp]
    have hnS : n ∈ primeSquares X := by
      by_contra h
      exact h₂ (mem_sdiff.mpr ⟨mem_filter.mpr ⟨hn,hp⟩,h⟩)
    obtain ⟨p,hp',rfl⟩ := mem_image.mp hnS
    have hlarge : 2*(D+1) < p := by
      by_contra! hle
      exact h₁ (mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1,Nat.pow_le_pow_left hle 2⟩)
    simp [singlePrimeError,balancedProduct_prime_square hD (mem_filter.mp hp').2 hlarge,primePowerPart,hp]
  have hsub : ∑ n ∈ Ioc 0 X, |singlePrimeError D n| ≤ C*∑ n ∈ S, vonMangoldt n := by
    let J := (Ioc 0 X).filter (fun n => n ∈ S)
    have he : (∑ n ∈ J, |singlePrimeError D n|) = ∑ n ∈ Ioc 0 X, |singlePrimeError D n| := by
      apply sum_subset (filter_subset ..)
      intro n hn hnot
      rw [hs n hn (fun h => hnot (mem_filter.mpr ⟨hn,h⟩)),abs_zero]
    rw [←he,mul_sum]
    apply (sum_le_sum (g := fun n => C*vonMangoldt n) (fun n hn =>
      error_bound (D := D) (mem_Ioc.mp (mem_filter.mp hn).1).2)).trans
    exact sum_le_sum_of_subset_of_nonneg (fun n hn => (mem_filter.mp hn).2) (fun _ _ _ => mul_nonneg hC vonMangoldt_nonneg)
  apply hsub.trans
  apply mul_le_mul_of_nonneg_left _ hC
  have hu : (∑ n ∈ S, vonMangoldt n) ≤ (∑ n ∈ Ioc 0 T, vonMangoldt n)+(∑ n ∈ higherPowers X, vonMangoldt n) := by
    have hh := sum_union_inter (s₁ := Ioc 0 T) (s₂ := higherPowers X) (f := fun n => (vonMangoldt n : ℝ))
    have hn := sum_nonneg (s := Ioc 0 T ∩ higherPowers X) (fun n _ => @vonMangoldt_nonneg n)
    dsimp [S]
    linarith only [hh,hn]
  have hI : Ioc 0 T = Icc 1 T := by ext; simp only [mem_Ioc,mem_Icc]; omega
  rw [hI] at hu
  change ∑ n ∈ S, vonMangoldt n ≤ _
  exact hu.trans (add_le_add (chebyshevPsi_le_seven T) (higher_mass hX))

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
