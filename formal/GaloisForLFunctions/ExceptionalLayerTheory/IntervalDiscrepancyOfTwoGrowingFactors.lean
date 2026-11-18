import GaloisForLFunctions.ExceptionalLayerTheory.LogFactorialWeightsForTheMiddlePrimeInterval
import GaloisForLFunctions.RHTower.Sieve.BivariateConvolutionSummatorySwap

/-!
# Interval discrepancy after excluding both short factors

Differencing the corrected Möbius floor prefix produces a signed factor
supported above the inner cutoff. Its convolution with the long Mangoldt
factor pays the prime error on every subinterval, up to the boundary
cost of the short divisor coefficients.
-/

noncomputable section
open Finset ArithmeticFunction RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def innerPrefix (D t : ℕ) : ℝ :=
  if t = 0 then 0 else 1-factorialPrefix (D+1) t

/-- Complementary coefficient of a product with two long factors. -/
def innerJump (D v : ℕ) : ℝ := innerPrefix D v-innerPrefix D (v-1)

private theorem innerPrefix_small {D t : ℕ} (ht : t ≤ D) : innerPrefix D t = 0 := by
  rcases Nat.eq_zero_or_pos t with rfl | hp
  · simp [innerPrefix]
  · simp [innerPrefix,hp.ne',prefix_one hp (by omega : t < D+1)]

theorem innerJump_small {D v : ℕ} (hv : v ≤ D) : innerJump D v = 0 := by
  rw [innerJump,innerPrefix_small hv,innerPrefix_small (by omega : v-1 ≤ D),sub_self]

private theorem sum_jump (D t : ℕ) : ∑ v ∈ Icc 1 t, innerJump D v = innerPrefix D t := by
  induction t with
  | zero => simp [innerPrefix]
  | succ t ih =>
    rw [sum_Icc_succ_top (by omega),ih,innerJump,Nat.add_sub_cancel]
    ring

/-- All partial sums of the complementary coefficient are bounded by the
mass of the inner divisor stencil, independently of the summation length. -/
theorem innerJump_prefix_bound (D t : ℕ) :
    |∑ v ∈ Icc 1 t, innerJump D v| ≤ 1+mass (D+1) := by
  rw [sum_jump,innerPrefix]
  split
  · have h := (abs_nonneg _).trans (abs_prefix_le_mass (Nat.succ_pos D) 0)
    rw [abs_zero]; linarith only [h]
  · exact (abs_sub _ _).trans (by rw [abs_one]; exact add_le_add le_rfl (abs_prefix_le_mass (Nat.succ_pos D) _))

/-- Mangoldt mass paired with the complementary coefficient on factorizations
in which both arguments exceed D. -/
def balancedProduct (D n : ℕ) : ℝ :=
  ∑ p ∈ n.divisorsAntidiagonal with D < p.1 ∧ D < p.2, vonMangoldt p.1*innerJump D p.2

/-- A prime cannot contribute to the new measure at positive cutoff. -/
theorem balancedProduct_prime {D n : ℕ} (hD : 1 ≤ D) (hn : n.Prime) : balancedProduct D n = 0 := by
  apply sum_eq_zero
  intro p hp
  obtain ⟨hh,h₁,h₂⟩ := mem_filter.mp hp
  have he := (Nat.mem_divisorsAntidiagonal.mp hh).1
  have hd : p.1 ∣ n := ⟨p.2,he.symm⟩
  rcases (Nat.dvd_prime hn).mp hd with h | h
  · omega
  · have hpos : 0 < p.1 := by omega
    have ht : p.1*1 < p.1*p.2 := Nat.mul_lt_mul_of_pos_left (by omega) hpos
    rw [Nat.mul_one,he,h] at ht
    exact (lt_irrefl _ ht).elim

/-- Summing the complementary coefficients telescopes to the corrected
factorial prefix at the complementary quotient. -/
theorem sum_balancedProduct (D T : ℕ) :
    ∑ n ∈ Icc 1 T, balancedProduct D n = middle (D+1) D T := by
  simp only [balancedProduct,sum_filter]
  rw [Sieve.sum_Icc_divisorsAntidiagonal_swap (fun u v =>
    if D < u ∧ D < v then vonMangoldt u*innerJump D v else 0)]
  have hs (u : ℕ) : (∑ v ∈ Icc 1 (T/u),
      if D < u ∧ D < v then vonMangoldt u*innerJump D v else 0) =
      if D < u then vonMangoldt u*innerPrefix D (T/u) else 0 := by
    by_cases hu : D < u
    · rw [if_pos hu,←sum_jump, mul_sum]
      apply sum_congr rfl
      intro v _
      by_cases hv : D < v
      · rw [if_pos ⟨hu,hv⟩]
      · simp [hv,innerJump_small (Nat.le_of_not_gt hv)]
    · simp [hu]
  simp_rw [hs]
  have hi : Ioc D (T/(D+1)) = (Icc 1 T).filter (fun u => D < u ∧ u ≤ T/(D+1)) := by
    ext u; simp only [mem_Ioc,mem_filter,mem_Icc]
    have := Nat.div_le_self T (D+1)
    omega
  rw [middle,hi,sum_filter]
  apply sum_congr rfl
  intro u hu
  obtain ⟨hu0,huT⟩ := mem_Icc.mp hu
  have hpos := (Nat.one_le_div_iff hu0).mpr huT
  by_cases hd : D < u
  · rw [if_pos hd]
    by_cases h : u ≤ T/(D+1)
    · rw [if_pos ⟨hd,h⟩,innerPrefix,if_neg (by omega)]
    · have ht : T/u < D+1 := (Nat.div_lt_iff_lt_mul hu0).mpr (by
        simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul (Nat.succ_pos D)).mp (Nat.lt_of_not_ge h))
      simp [h,innerPrefix_small (Nat.le_of_lt_succ ht)]
  · simp [hd]

/-- Density fitted to the horizon, extended by one outside the counted range. -/
def balancedDensity (D X n : ℕ) : ℝ :=
  1+if n ≤ X then vonMangoldt n-balancedProduct D n-1 else 0

private theorem prefix_error {D T : ℕ} :
    |∑ n ∈ Ioc 0 T, (vonMangoldt n-balancedProduct D n-1)| ≤
      mass (D+1)*(3+Real.log (2*(D+1) : ℕ)+2*Real.log T)+(1+mass (D+1))*(7*D) := by
  have hm := (abs_nonneg _).trans (abs_prefix_le_mass (Nat.succ_pos D) 0)
  rcases Nat.eq_zero_or_pos T with rfl | ht
  · simp only [Ioc_self,sum_empty,abs_zero,Nat.cast_zero,Real.log_zero,mul_zero,add_zero]
    have := Real.log_natCast_nonneg (2*(D+1)); positivity
  have hp : ∑ n ∈ Icc 1 T, vonMangoldt n = Chebyshev.psi T := by
    unfold Chebyshev.psi; rw [Nat.floor_natCast]; rfl
  have hI : Ioc 0 T = Icc 1 T := by ext; simp only [mem_Ioc,mem_Icc]; omega
  simp only [hI,sum_sub_distrib,hp,sum_balancedProduct,sum_const,Nat.card_Icc,Nat.add_sub_cancel,
    nsmul_eq_mul,mul_one]
  rw [sub_right_comm]
  exact abs_error_sub_middle (Nat.succ_pos D) ht D

/-- The difference between the Mangoldt measure and the two-factor
measure has unit density with small discrepancy on every integer interval. -/
theorem balancedDensity_discrepancy :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X →
      let D := ⌊(X : ℝ)^(1/400000 : ℝ)⌋₊
      ∀ L U : ℕ, L ≤ U →
        |(∑ n ∈ Ioc L U, balancedDensity D X n)-((U : ℝ)-L)| ≤ C*(X : ℝ)^(1/200000 : ℝ) := by
  obtain ⟨K,hK,hk⟩ := mass_uniform
  refine ⟨2*(2*K*800007+(1+2*K)*7),by positivity,?_⟩
  intro X hX D L U hLU
  let t := (X : ℝ)^(1/400000 : ℝ)
  let e := fun n => vonMangoldt n-balancedProduct D n-1
  let f := fun n => if n ≤ X then e n else 0
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have ht : 1 ≤ t := Real.one_le_rpow hx (by norm_num)
  have ht0 := zero_le_one.trans ht
  have hd : (D : ℝ) ≤ t := Nat.floor_le ht0
  have hm := hk (D+1) (Nat.succ_pos D)
  push_cast at hm
  have hm' : mass (D+1) ≤ 2*K*t := by
    linarith only [hm,mul_le_mul_of_nonneg_left hd hK,mul_le_mul_of_nonneg_left ht hK]
  have hmass := (abs_nonneg _).trans (abs_prefix_le_mass (Nat.succ_pos D) 0)
  have hlog : Real.log (2*(D+1) : ℕ) ≤ 4*t := by
    have h := Real.log_le_sub_one_of_pos (show 0 < ((2*(D+1) : ℕ) : ℝ) by positivity)
    push_cast at h ⊢; linarith only [h,hd,ht]
  have hXlog := Real.log_le_rpow_div (Nat.cast_nonneg X) (by norm_num : (0 : ℝ) < 1/400000)
  change Real.log X ≤ t/(1/400000 : ℝ) at hXlog
  have ht₂ : t*t = (X : ℝ)^(1/200000 : ℝ) := by
    dsimp [t]; rw [← Real.rpow_add (zero_lt_one.trans_le hx)]; norm_num
  have he (T : ℕ) (hle : T ≤ X) : |∑ n ∈ Ioc 0 T, e n| ≤ (2*K*800007+(1+2*K)*7)*(t*t) := by
    have hl : Real.log T ≤ Real.log X := by
      rcases Nat.eq_zero_or_pos T with rfl | h
      · simpa using Real.log_natCast_nonneg X
      · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast hle)
    apply prefix_error.trans
    have h₁ : 3+Real.log (2*(D+1) : ℕ)+2*Real.log T ≤ 800007*t := by linarith only [hlog,hXlog,hl,ht]
    have ha := mul_le_mul hm' h₁ (by have := Real.log_natCast_nonneg (2*(D+1)); have := Real.log_natCast_nonneg T; positivity)
      (show 0 ≤ 2*K*t by positivity)
    have hb := mul_le_mul (show 1+mass (D+1) ≤ (1+2*K)*t by linarith only [hm',ht])
      (mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 7)) (by positivity) (by positivity)
    linarith only [ha,hb]
  have hp (T : ℕ) : (∑ n ∈ Ioc 0 T, f n) = ∑ n ∈ Ioc 0 (min T X), e n := by
    have hi : ((Ioc 0 T).filter (fun n => n ≤ X)) = Ioc 0 (min T X) := by
      ext; simp only [mem_filter,mem_Ioc,le_min_iff]; tauto
    change (∑ n ∈ Ioc 0 T, if n ≤ X then e n else 0) = _
    rw [←sum_filter,hi]
  have hs := sum_Ioc_consecutive f (Nat.zero_le L) hLU
  rw [hp,hp] at hs
  have hsub : (∑ n ∈ Ioc L U, f n) = (∑ n ∈ Ioc 0 (min U X), e n)-(∑ n ∈ Ioc 0 (min L X), e n) := by
    linarith only [hs]
  change |(∑ n ∈ Ioc L U, (1+f n))-((U : ℝ)-L)| ≤ _
  rw [sum_add_distrib,hsub]
  simp only [sum_const,Nat.card_Ioc,nsmul_eq_mul,mul_one,Nat.cast_sub hLU,
    show ∀ x y : ℝ, x+y-x=y from fun x y => by ring]
  rw [←ht₂]
  apply (abs_sub _ _).trans
  linarith only [he (min U X) (min_le_right ..),he (min L X) (min_le_right ..)]

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
