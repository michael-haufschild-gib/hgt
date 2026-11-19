import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheCountWithSmallProductOfSimplePrimeFactors
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheOddSmoothCompositesAtThePrimeMidpoint
import GaloisForLFunctions.RHTower.VerticalProgressionRatioForm

/-!
# The exponent-one factors required at the composite midpoint

For a target abscissa b, composites whose exponent-one prime factors
have product at most k^(2b−1) can be discarded. Their absolute price
is affordable before cancellation. In particular the half-power test
requires only composites carrying a prime of exponent one.
-/

noncomputable section
open Finset
open scoped Classical
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
open private unitaryLog from
  GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheOddSmoothCompositesAtThePrimeMidpoint

private theorem log_price_bound {a : ℝ} (ha : 0 < a) {X k : ℕ} (hk : 1 ≤ k) (hX : k ≤ X) :
    |unitaryLog k| ≤ (_root_.RHTower.Sieve.divisorBoundConst a/a)*(X:ℝ)^(a+a) := by
  let D := _root_.RHTower.Sieve.divisorBoundConst a
  have hd : 0 ≤ D := (_root_.RHTower.Sieve.divisorBoundConst_pos ha).le
  have count : |(unitaryHalfWeight k:ℝ)| ≤ (smallUnitarySubsets k).card := by
    simp only [unitaryHalfWeight,Int.cast_sum,Int.cast_pow,Int.cast_neg,Int.cast_one]
    apply (abs_sum_le_sum_abs ..).trans
    simp only [abs_pow,abs_neg,abs_one,one_pow,sum_const,nsmul_eq_mul,mul_one,le_refl]
  have small : (smallUnitarySubsets k).card ≤ 2^k.primeFactors.card :=
    (card_le_card (filter_subset ..)).trans_eq (card_powerset _)
  have major := count.trans ((Nat.cast_le.mpr small).trans (by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using _root_.RHTower.VerticalAP.two_pow_card_primeFactors_le_card_divisors (n:=k) (by omega)))
  have hw := major.trans (_root_.RHTower.Sieve.card_divisors_le_rpow ha (by omega : k ≠ 0))
  have hx := Real.rpow_le_rpow (Nat.cast_nonneg k) (Nat.cast_le.mpr hX) ha.le
  have hlog := (Real.log_le_rpow_div (Nat.cast_nonneg k) ha).trans (div_le_div_of_nonneg_right hx ha.le)
  rw [unitaryLog,abs_mul,abs_of_nonneg (Real.log_natCast_nonneg k),
    Real.rpow_add (Nat.cast_pos.mpr (hk.trans hX))]
  have hh := mul_le_mul (hw.trans (mul_le_mul_of_nonneg_left hx hd)) hlog
    (Real.log_natCast_nonneg k) (mul_nonneg hd (Real.rpow_nonneg (Nat.cast_nonneg X) a))
  exact hh.trans_eq (by dsimp only [D]; ring)

private abbrev activeTerm (n k : ℕ) : ℝ :=
  if n.Coprime k ∧ oddSmoothSupport k then unitaryLog k else 0

/-- Only balanced odd composites whose product of exponent-one primes
exceeds k^δ contribute to this price. -/
def simplePrimeMidpointPrice (δ : ℝ) (n : ℕ) : ℝ :=
  unitarySignedIntervals (fun k => if (k:ℝ)^δ < simplePrimeProduct k then activeTerm n k else 0) n

private theorem discarded_interval {δ t : ℝ} (hd : 0 ≤ δ) (ht : (1+δ)/2 < t) :
    ∃ C : ℝ, ∀ n X : ℕ, 1 ≤ X → ∀ S : Finset ℕ, S ⊆ Icc 1 X →
      |∑ k ∈ S, (if (simplePrimeProduct k:ℝ) ≤ (k:ℝ)^δ then activeTerm n k else 0)| ≤ C*(X:ℝ)^t := by
  let a := (t-(1+δ)/2)/2
  have ap : 0 < a := half_pos (sub_pos.mpr ht)
  let D := _root_.RHTower.Sieve.divisorBoundConst a/a
  have D0 : 0 ≤ D := div_nonneg (_root_.RHTower.Sieve.divisorBoundConst_pos ap).le ap.le
  refine ⟨24*D,fun n X xp S hs => ?_⟩
  let A := S.filter fun k => (simplePrimeProduct k:ℝ) ≤ (k:ℝ)^δ
  let Y := ⌊(X:ℝ)^δ⌋₊
  have x0 := Nat.cast_pos (α:=ℝ).mpr xp
  have sub : A ⊆ (Icc 1 X).filter (fun k => simplePrimeProduct k ≤ Y) := by
    intro k hk
    obtain ⟨hk,price⟩ := mem_filter.mp hk
    exact mem_filter.mpr ⟨hs hk,Nat.le_floor (price.trans (Real.rpow_le_rpow (Nat.cast_nonneg k)
      (Nat.cast_le.mpr (mem_Icc.mp (hs hk)).2) hd))⟩
  have size := (Nat.cast_le.mpr (card_le_card sub)).trans (small_simple_product_count X Y)
  have scale : Real.sqrt Y ≤ (X:ℝ)^(δ/2) := by
    apply (Real.sqrt_le_sqrt (Nat.floor_le (Real.rpow_nonneg x0.le δ))).trans_eq
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul x0.le]
    congr 1; ring
  have card : (A.card:ℝ) ≤ 24*(X:ℝ)^((1+δ)/2) := by
    apply size.trans ((mul_le_mul_of_nonneg_left scale (by positivity)).trans_eq ?_)
    rw [Real.sqrt_eq_rpow,mul_assoc,←Real.rpow_add x0]
    congr 2; ring
  rw [←sum_filter]
  change |∑ k ∈ A,activeTerm n k| ≤ _
  apply (abs_sum_le_sum_abs ..).trans
  have term (k : ℕ) (hk : k ∈ A) : |activeTerm n k| ≤ D*(X:ℝ)^(a+a) := by
    have bnd := mem_Icc.mp (hs (mem_filter.mp hk).1)
    dsimp only [activeTerm]
    split_ifs
    · exact log_price_bound ap bnd.1 bnd.2
    · rw [abs_zero]; exact mul_nonneg D0 (Real.rpow_nonneg x0.le _)
  have sum := sum_le_sum term
  rw [sum_const,nsmul_eq_mul] at sum
  apply sum.trans ((mul_le_mul_of_nonneg_right card (mul_nonneg D0 (Real.rpow_nonneg x0.le _))).trans_eq ?_)
  calc _ = (24*D)*((X:ℝ)^((1+δ)/2)*(X:ℝ)^(a+a)) := by ring
       _ = _ := by rw [←Real.rpow_add x0,show (1+δ)/2+(a+a)=t by dsimp [a]; ring]

/-- Absolute error of pruning the simple product at exponent δ. -/
theorem simple_prime_pruning_cost {δ t : ℝ} (hd : 0 ≤ δ) (ht : (1+δ)/2 < t) :
    ∃ C : ℝ, ∀ {n : ℕ}, 1 ≤ n →
      |oddSmoothCompositePrice n-simplePrimeMidpointPrice δ n| ≤ C*(n:ℝ)^t := by
  obtain ⟨A,hA⟩ := discarded_interval hd ht
  refine ⟨2*A*(4:ℝ)^t,fun {n} hn => ?_⟩
  let loss := fun k => if (simplePrimeProduct k:ℝ) ≤ (k:ℝ)^δ then activeTerm n k else 0
  have eq (S : Finset ℕ) :
      ∑ k ∈ S,activeTerm n k - ∑ k ∈ S,(if (k:ℝ)^δ < simplePrimeProduct k then activeTerm n k else 0)
        = ∑ k ∈ S, loss k := by
    rw [←sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    rcases lt_or_ge ((k:ℝ)^δ) (simplePrimeProduct k:ℝ) with h | h
    · simp only [loss,if_pos h,if_neg h.not_ge,sub_self]
    · simp only [loss,if_pos h,if_neg h.not_gt,sub_zero]
  have bounds (j l : ℕ) (hl : l ≤ 4*n) : |∑ k ∈ Ioc j l,loss k| ≤ A*((4*n:ℕ):ℝ)^t :=
    hA n _ (by omega) _ (fun _ hk => mem_Icc.mpr ⟨by have := (mem_Ioc.mp hk).1; omega,(mem_Ioc.mp hk).2.trans hl⟩)
  have cost := (abs_sub (∑ k ∈ Ioc (3*n) (4*n),loss k) (∑ k ∈ Ioc (2*n) (3*n),loss k)).trans
    (add_le_add (bounds _ _ le_rfl) (bounds _ _ (by omega)))
  have exactLoss : oddSmoothCompositePrice n-simplePrimeMidpointPrice δ n =
      (∑ k ∈ Ioc (3*n) (4*n),loss k) - ∑ k ∈ Ioc (2*n) (3*n),loss k := by
    unfold oddSmoothCompositePrice simplePrimeMidpointPrice unitarySignedIntervals
    rw [←eq,←eq]
    dsimp only [activeTerm]; ring
  rw [exactLoss]
  apply cost.trans_eq
  push_cast
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (Nat.cast_nonneg n)]
  ring

/-- At every target b≥1/2 the reduced composite price with exponent
2b−1 still detects the exact zeta half-plane. -/
theorem simple_prime_midpoint_spectrum {b : ℝ} (hb : 1/2 ≤ b) :
    (∀ t : ℝ, b<t → t<1 → ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      simplePrimeMidpointPrice (2*b-1) n-oddSmoothIntegralCenter n ≤ C*(n:ℝ)^t) ↔
        _root_.RHTower.zetaZeroAbscissa ≤ b := by
  rw [←odd_smooth_integral_spectrum_iff hb]
  constructor <;> intro h t ht ht1 <;> obtain ⟨C,hC⟩ := h t ht ht1 <;>
    obtain ⟨A,hA⟩ := simple_prime_pruning_cost (δ:=2*b-1) (by linarith only [hb]) (by linarith only [ht] : (1+(2*b-1))/2 < t) <;>
    refine ⟨C+A,fun n hn => ?_⟩
  · linarith only [(abs_le.mp (hA hn)).2,hC n hn]
  · linarith only [(abs_le.mp (hA hn)).1,hC n hn]

#print axioms simple_prime_pruning_cost
#print axioms simple_prime_midpoint_spectrum
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
