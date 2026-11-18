import GaloisForLFunctions.PrimeExponentialSums.DivisorDilationsInSquareRootProductWindows
import GaloisForLFunctions.ExceptionalLayerTheory.ShortFactorsInTheDualPrimeWindow
import GaloisForLFunctions.ExceptionalLayerTheory.AveragingThePrimeErrorAtAComplementaryBoundary

/-!
# The dual divisor stencil in the square-root product window

At each fixed short divisor the prime window cancels across all second
factors. The harmonic moment then restores the centered complementary
prefix at the quotient without introducing a constant term.
-/

noncomputable section
open Finset RHTower ArithmeticFunction
open GaloisForLFunctions.PrimeExponentialSums GaloisForLFunctions.HTGeometry.SmoothedSawtooth
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def ordinaryLog (p : ℕ) : ℝ := if p.Prime then Real.log p else 0

/-- Membership in the prime interval is exactly the two product inequalities. -/
theorem squareRootWindowPrimes_eq_filter {X F L U v : ℕ} (hv : 0<v) (hu : U≤X) :
    squareRootWindowPrimes F L U v=(Ico (F+1) (X+1)).filter
      (fun p => p.Prime ∧ L<p*v ∧ p*v≤U) := by
  ext p
  have hlo : L/v<p ↔ L<p*v := Nat.div_lt_iff_lt_mul hv
  have hhi : p≤U/v ↔ p*v≤U := Nat.le_div_iff_mul_le hv
  simp only [squareRootWindowPrimes,mem_filter,mem_Ico,max_le_iff]
  constructor
  · rintro ⟨⟨⟨hF,hL⟩,hU⟩,prime⟩
    have hh := Nat.le_of_lt_succ hU
    exact ⟨⟨hF,Nat.lt_succ_of_le ((hh.trans (Nat.div_le_self U v)).trans hu)⟩,prime,hlo.mp hL,hhi.mp hh⟩
  · rintro ⟨⟨hF,_⟩,prime,hL,hU⟩
    exact ⟨⟨⟨hF,hlo.mpr hL⟩,Nat.lt_succ_of_le (hhi.mpr hU)⟩,prime⟩

private theorem rectangle_eq {X e F L U c : ℕ} (hc : 1 ≤ c) (hu : U ≤ X) (β : ℕ → ℝ) :
    ((∑ j ∈ Ico c (X+1), β j*∑ p ∈ squareRootWindowPrimes F L U j,
      Real.log p*centeredQuotient X (p*j) e : ℝ) : ℂ) =
      ∑ p ∈ Ico (F+1) (X+1), ∑ j ∈ Ico c (X+1), fractionalProductTerm ((X : ℝ)/e) L U
        (fun p => (ordinaryLog p : ℂ)) (fun j => (β j : ℂ)) p j := by
  rw [Complex.ofReal_sum,sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [squareRootWindowPrimes_eq_filter (hc.trans (mem_Ico.mp hj).1) hu,sum_filter,mul_sum,Complex.ofReal_sum]
  apply sum_congr rfl
  intro p _
  have hq : centeredQuotient X (p*j) e=saw (((X : ℝ)/e)/j/p) := by
    dsimp only [centeredQuotient,saw]; rw [Nat.cast_mul,mul_comm (p : ℝ) j,div_mul_eq_div_div]
  by_cases window : L<p*j ∧ p*j≤U
  · by_cases prime : p.Prime
    · simp [prime,window,fractionalProductTerm,ordinaryLog,hq]
      ring
    · simp [prime,window,fractionalProductTerm,ordinaryLog]
  · simp [window,fractionalProductTerm]

/-- Uniform square-root saving at every short divisor over all
complementary factors of the sharp prime product window. -/
theorem dual_prime_divisor_window :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {X e F L U : ℕ}, 1 ≤ X → 1 ≤ e →
      64 ≤ (X : ℝ)^(1/25000000 : ℝ) → (e : ℝ) ≤ (X : ℝ)^(1/25000000 : ℝ) →
      ⌊(X : ℝ)^(1/1000000 : ℝ)⌋₊ ≤ F → Real.sqrt X ≤ (L : ℝ)+1 →
      (U : ℝ) ≤ (X : ℝ)^(500000001/1000000000 : ℝ) → ∀ (β : ℕ → ℝ) {B : ℝ}, 0 ≤ B →
      (∀ j ∈ Icc 1 X, |β j| ≤ B) →
      |∑ j ∈ Icc 1 X, β j*∑ p ∈ squareRootWindowPrimes F L U j, Real.log p*centeredQuotient X (p*j) e| ≤
        K*B*(1+Real.log X)^3*Real.sqrt X := by
  obtain ⟨C,hC,hshort⟩ := short_factor_prime_divisor_window
  obtain ⟨K,hK,hlong⟩ := square_root_fractional_divisor_window
  refine ⟨C+4*K,by positivity,?_⟩
  intro X e F L U hx he hbig hd hF hL hU β B hB hβ
  let q := ⌊(X : ℝ)^(1/1000000 : ℝ)⌋₊
  let H := 1+Real.log X
  let f (j : ℕ) := β j*∑ p ∈ squareRootWindowPrimes F L U j, Real.log p*centeredQuotient X (p*j) e
  have hx' : (1 : ℝ) ≤ X := by exact_mod_cast hx
  have hH : 1 ≤ H := le_add_of_nonneg_right (Real.log_natCast_nonneg X)
  have hH₀ := zero_le_one.trans hH
  have hq : q ≤ X := Nat.floor_le_of_le ((Real.rpow_le_rpow_of_exponent_le hx'
    (by norm_num : (1/1000000 : ℝ) ≤ 1)).trans_eq (Real.rpow_one _))
  have hu : U ≤ X := by exact_mod_cast hU.trans ((Real.rpow_le_rpow_of_exponent_le hx'
    (by norm_num : (500000001/1000000000 : ℝ) ≤ 1)).trans_eq (Real.rpow_one _))
  have hsm : |∑ j ∈ Ico 1 (q+1), f j| ≤ C*B*H*Real.sqrt X := by
    rw [show Ico 1 (q+1)=Icc 1 q by ext n; simp]
    exact hshort hx he (hd.trans (Real.rpow_le_rpow_of_exponent_le hx' (by norm_num))) hL hU β hB
      (fun j hj => hβ j (mem_Icc.mpr ⟨(mem_Icc.mp hj).1,(mem_Icc.mp hj).2.trans hq⟩))
  have hl : 1+Real.log (X+1 : ℕ) ≤ 2*H := by
    have hh : ((X+1 : ℕ) : ℝ) ≤ 2*X := by push_cast; linarith only [hx']
    have hh' := Real.log_le_log (by positivity : (0 : ℝ)<(X+1 : ℕ)) hh
    rw [Real.log_mul (by norm_num) (zero_lt_one.trans_le hx').ne'] at hh'
    dsimp [H]; linarith only [hh',Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2),Real.log_natCast_nonneg X]
  have hlg : |∑ j ∈ Ico (q+1) (X+1), f j| ≤ 4*K*B*H^3*Real.sqrt X := by
    have eq := rectangle_eq (e := e) (F := F) (L := L) (show 1≤q+1 from Nat.succ_pos q) hu β
    have eqn := congrArg (fun z : ℂ => ‖z‖) eq
    simp only [Complex.norm_real,Real.norm_eq_abs] at eqn
    change |∑ j ∈ Ico (q+1) (X+1), f j|=_ at eqn
    rw [eqn]
    by_cases hf : F ≤ X
    swap
    · rw [Ico_eq_empty (show ¬F+1<X+1 by omega),sum_empty,norm_zero]; positivity
    have hscale : (X : ℝ)^(1/1000000 : ℝ) ≤ (q+1 : ℕ) := by push_cast; exact (Nat.lt_floor_add_one _).le
    have hα (p : ℕ) (hp : p ∈ Ico (F+1) (X+1)) : ‖(ordinaryLog p : ℂ)‖ ≤ H := by
      simp only [Complex.norm_real,Real.norm_eq_abs]
      by_cases prime : p.Prime
      · rw [ordinaryLog,if_pos prime,abs_of_nonneg (Real.log_natCast_nonneg _)]
        have hh : (p : ℝ) ≤ X := by exact_mod_cast Nat.le_of_lt_succ (mem_Ico.mp hp).2
        exact (Real.log_le_log (by exact_mod_cast prime.pos) hh).trans (by dsimp [H]; linarith)
      · simpa only [ordinaryLog,if_neg prime,abs_zero] using hH₀
    have hβ' (j : ℕ) (hj : j ∈ Ico (q+1) (X+1)) : ‖(β j : ℂ)‖ ≤ B := by
      obtain ⟨h₁,h₂⟩ := mem_Ico.mp hj
      simpa only [Complex.norm_real,Real.norm_eq_abs] using hβ j
        (mem_Icc.mpr ⟨by omega,Nat.le_of_lt_succ h₂⟩)
    have hh := hlong he hx hbig hd (hscale.trans (by exact_mod_cast Nat.succ_le_succ hF)) hscale
      (Nat.succ_le_succ hf) (Nat.succ_le_succ hq) hL hU _ _ hH₀ hB hα hβ'
    apply hh.trans
    have hz : 0 ≤ 1+Real.log (X+1 : ℕ) := by have := Real.log_natCast_nonneg (X+1); positivity
    have hm := mul_le_mul (mul_le_mul_of_nonneg_left hl hK) hl hz (by positivity)
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm (mul_nonneg hH₀ hB))
      (Real.sqrt_nonneg _)).trans_eq (by ring)
  rw [show Icc 1 X=Ico 1 (X+1) by ext n; simp,←sum_Ico_consecutive f (show 1 ≤ q+1 from Nat.succ_pos q)
    (Nat.succ_le_succ hq)]
  apply (abs_add_le _ _).trans ((add_le_add hsm hlg).trans _)
  have hcube : H ≤ H^3 := by simpa only [pow_one] using (pow_le_pow_right₀ hH (by norm_num : 1 ≤ 3))
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcube (mul_nonneg hC hB)) (Real.sqrt_nonneg (X : ℝ))
  change _ ≤ (C+4*K)*B*H^3*Real.sqrt X
  linarith only [hm]

/-- The complementary prefix at the quotient is the original finite
stencil of centered reciprocal remainders. -/
theorem factorialBoundary_quotient {R : ℕ} (hR : 1 ≤ R) (X n : ℕ) :
    factorialBoundary R (X/n)=stencil R (centeredQuotient X n) := by
  have cast (d : ℕ) : ((X/n/d : ℕ) : ℝ) = ((X : ℝ)/n)/d-centeredQuotient X n d-1/2 := by
    rw [Nat.div_div_eq_div_mul,RHTower.natDiv_eq_sub_sawtooth]
    simp only [RHTower.reciprocalSawtooth,centeredQuotient,Nat.cast_mul,←div_div]
    rw [div_right_comm (X : ℝ) n d]; ring
  simp only [factorialBoundary,factorialPrefix,cast,stencil_sub,stencil_linear_quotient hR,zero_sub]
  ring

/-- Full dual stencil window with arbitrary bounded second coefficients. -/
theorem dual_factorial_window :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {X R F L U : ℕ}, 1 ≤ X → 1 ≤ R →
      64 ≤ (X : ℝ)^(1/25000000 : ℝ) → ((2*R : ℕ) : ℝ) ≤ (X : ℝ)^(1/25000000 : ℝ) →
      ⌊(X : ℝ)^(1/1000000 : ℝ)⌋₊ ≤ F → Real.sqrt X ≤ (L : ℝ)+1 →
      (U : ℝ) ≤ (X : ℝ)^(500000001/1000000000 : ℝ) → ∀ (β : ℕ → ℝ) {B : ℝ}, 0 ≤ B →
      (∀ j ∈ Icc 1 X, |β j| ≤ B) →
      |∑ j ∈ Icc 1 X, β j*∑ p ∈ squareRootWindowPrimes F L U j, Real.log p*factorialBoundary R (X/(p*j))| ≤
        mass R*(K*B*(1+Real.log X)^3*Real.sqrt X) := by
  obtain ⟨K,hK,h⟩ := dual_prime_divisor_window
  refine ⟨K,hK,?_⟩
  intro X R F L U hx hR hbig hcut hF hL hU β B hB hβ
  simp_rw [factorialBoundary_quotient hR]
  simp_rw [stencil_weighted_sum]
  apply abs_stencil_le hR
  intro e he
  exact h hx (mem_Icc.mp he).1 hbig ((by exact_mod_cast (mem_Icc.mp he).2 : (e : ℝ) ≤ (2*R : ℕ)).trans hcut)
    hF hL hU β hB hβ

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
