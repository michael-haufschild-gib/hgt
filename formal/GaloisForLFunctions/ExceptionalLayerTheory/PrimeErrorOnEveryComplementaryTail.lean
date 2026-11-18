import GaloisForLFunctions.ExceptionalLayerTheory.CancellationOnRepeatedPrimeFactors
import GaloisForLFunctions.ExceptionalLayerTheory.TheCompletedCofactorRowRetainsThePrimeError

/-!
# The prime error on every complementary-factor tail

The factorial approximation at each divided horizon has logarithmic
error. Pairing that error with bounded prefixes of the inner jumps gives
square-root precision for every complementary cutoff.
-/

noncomputable section
open Finset ArithmeticFunction RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Complete Mangoldt row above a complementary cutoff. -/
def completeComplementTail (D R X a : ℕ) : ℝ :=
  ∑ v ∈ Ioc a X, innerJump D v*
    ∑ u ∈ Icc 1 (X/v), vonMangoldt u*centeredPrimeWeight R (X/v/u)

/-- Signed dilation of the ordinary Chebyshev error above the same cutoff. -/
def primeErrorTail (D X a : ℕ) : ℝ :=
  ∑ v ∈ Ioc a X, innerJump D v*(Chebyshev.psi (X/v : ℕ)-(X/v : ℕ))

/-- The complete Mangoldt row may be replaced by one signed dilation of
the genuine prime error, uniformly over the entire range of cutoffs. -/
theorem completeComplementTail_sub_primeErrorTail {R X : ℕ} (hR : 1≤R) (hx : 1≤X) (D a : ℕ) :
    |completeComplementTail D R X a-primeErrorTail D X a|≤
      4*(1+mass (D+1))*(420*(1+mass R)*(3+Real.log (128*(128*R^2+1) : ℕ)+2*Real.log X))*Real.sqrt X := by
  let w (t : ℕ) := (∑ u ∈ Icc 1 t, vonMangoldt u*centeredPrimeWeight R (t/u))-(Chebyshev.psi t-t)
  let H := 3+Real.log (128*(128*R^2+1) : ℕ)+2*Real.log X
  let B := 420*(1+mass R)*H
  have hm := (abs_nonneg _).trans (abs_prefix_le_mass hR 0)
  have hd := (abs_nonneg _).trans (abs_prefix_le_mass (Nat.succ_pos D) 0)
  have hH : 0≤H := by
    dsimp [H]
    have := Real.log_natCast_nonneg (128*(128*R^2+1)); have := Real.log_natCast_nonneg X; positivity
  have hB : 0≤B := by dsimp [B]; positivity
  have hw (t : ℕ) (ht : t≤X) : |w t|≤B := by
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · simpa [w,Chebyshev.psi] using hB
    dsimp only [w]; rw [abs_sub_comm]
    apply (centeredPrimeWeight_factorial hR hpos).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hl := Real.log_le_log (by exact_mod_cast hpos : (0 : ℝ)<t) (by exact_mod_cast ht : (t : ℝ)≤X)
    dsimp [H]; linarith only [hl]
  let W (t : ℕ) := if t≤X then w t else 0
  have bound (t : ℕ) : |W t|≤B := by
    by_cases h : t≤X
    · simpa only [W,if_pos h] using hw t h
    · simpa only [W,if_neg h,abs_zero] using hB
  have prefix (t : ℕ) (_ht : t≤X) : |∑ v ∈ Ioc 0 t, innerJump D v|≤1+mass (D+1) := by
    rw [show Ioc 0 t=Icc 1 t by ext n; simp only [mem_Ioc,mem_Icc]; omega]
    exact innerJump_prefix_bound D t
  have eq : completeComplementTail D R X a-primeErrorTail D X a=
      ∑ v ∈ Ioc a X, innerJump D v*W (X/v) := by
    unfold completeComplementTail primeErrorTail
    rw [←sum_sub_distrib]
    exact sum_congr rfl fun v _ => by rw [←mul_sub]; simp only [W,if_pos (Nat.div_le_self X v),w]
  have hs : ((Nat.sqrt X : ℕ) : ℝ)≤Real.sqrt X :=
    (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr (by
      simpa only [sq,Nat.cast_mul] using (by exact_mod_cast Nat.sqrt_le X :
        ((Nat.sqrt X : ℕ) : ℝ)*Nat.sqrt X≤X))
  rw [eq]
  exact (abs_truncated_quotient_pair a _ W (by positivity) hB prefix bound).trans
    (mul_le_mul_of_nonneg_left hs (by positivity))

private theorem jump_unit_and_divisors (D : ℕ) {v : ℕ} (hv : 1≤v) :
    innerJump D v=(if v=1 then 1 else 0)-stencil (D+1) (fun e => if e∣v then 1 else 0) := by
  by_cases h : v=1
  swap
  · rw [if_neg h,zero_sub]; exact innerJump_divisor_stencil (by omega) D
  subst v
  have div1 (d : ℕ) : ((1/d : ℕ) : ℝ)=(if d∣1 then 1 else 0) := by
    have he : (1/d : ℕ)=if d∣1 then 1 else 0 := by
      simpa only [Nat.zero_add,Nat.zero_div] using Nat.succ_div (a := 0) (b := d)
    by_cases h : d∣1
    · rw [if_pos h] at he ⊢; exact_mod_cast he
    · rw [if_neg h] at he ⊢; exact_mod_cast he
  change (if (1 : ℕ)=0 then 0 else 1-factorialPrefix (D+1) 1)-
    (if (1 : ℕ)-1=0 then 0 else 1-factorialPrefix (D+1) (1-1))=_
  simp only [if_neg Nat.one_ne_zero,Nat.sub_self,if_pos rfl,sub_zero,factorialPrefix,div1]

/-- Completing the inner error dilation leaves exactly the factorial
stencil of the unweighted complete divisor errors. -/
theorem complete_primeErrorTail_identity (D : ℕ) {X : ℕ} (hx : 1≤X) :
    primeErrorTail D X 0=(Chebyshev.psi X-X)-stencil (D+1) (fun e => completeDivisorError (X/e)) := by
  let E (t : ℕ) := Chebyshev.psi t-(t : ℝ)
  let z (v : ℕ) := E (X/v)
  let I := Ioc 0 X
  let ind (v e : ℕ) : ℝ := if e∣v then 1 else 0
  have one : (∑ v ∈ I, (if v=1 then (1 : ℝ) else 0)*z v)=E X := by
    rw [sum_eq_single 1]
    · simp [z]
    · intro b _ hb; simp [hb]
    · intro hn; exact (hn (mem_Ioc.mpr ⟨by decide,hx⟩)).elim
  have fibre (e : ℕ) : (∑ v ∈ I, z v*ind v e)=completeDivisorError (X/e) := by
    rcases Nat.eq_zero_or_pos e with rfl | he
    · have hz (v : ℕ) (hv : v ∈ I) : z v*ind v 0=0 := by
        simp [ind,Nat.ne_of_gt (mem_Ioc.mp hv).1]
      simpa only [sum_congr rfl hz,sum_const_zero,Nat.div_zero,completeDivisorError,Icc_eq_empty (by decide : ¬1≤(0 : ℕ)),sum_empty]
    have eq : (∑ v ∈ I, z v*ind v e)=(∑ v ∈ I with e∣v, z v) := by
      rw [sum_filter]; exact sum_congr rfl fun v _ => by by_cases h : e∣v <;> simp [h,ind]
    rw [eq,show I=Ioc 0 X from rfl,sum_divisible_Ioc he,Nat.zero_div]
    simp only [completeDivisorError,z,E,Nat.div_div_eq_div_mul]
    rw [show Ioc 0 (X/e)=Icc 1 (X/e) by ext v; simp only [mem_Icc,mem_Ioc]; omega]
  calc primeErrorTail D X 0 = ∑ v ∈ I, ((if v=1 then 1 else 0)*z v-z v*stencil (D+1) (ind v)) := by
         apply sum_congr rfl; intro v hv
         rw [jump_unit_and_divisors D (mem_Ioc.mp hv).1]; dsimp only [ind,z,E]; ring
       _ = _ := by
         rw [sum_sub_distrib,one,stencil_weighted_sum]
         simp_rw [fibre]

/-- The complete dilation reproduces the actual prime error with a
square-root remainder. The zero reciprocal moment cancels the entire
linear divisor mean. -/
theorem complete_primeErrorTail_bound (D : ℕ) {X : ℕ} (hx : 1≤X) :
    |(Chebyshev.psi X-X)-primeErrorTail D X 0|≤mass (D+1)*(25*Real.sqrt X+2*|Real.eulerMascheroniConstant|) := by
  let γ := Real.eulerMascheroniConstant
  let f (e : ℕ) := completeDivisorError (X/e)
  let main (e : ℕ) := ((-2*γ)*(X : ℝ))/e
  have hz : stencil (D+1) main=0 := stencil_linear_quotient (Nat.succ_pos D) _
  have hh := abs_stencil_le (Nat.succ_pos D) (fun e => f e-main e)
    (M := 25*Real.sqrt X+2*|γ|) (fun e he => by
      let n := X/e
      have hl : Real.sqrt (n : ℝ)≤Real.sqrt X := Real.sqrt_le_sqrt (by exact_mod_cast Nat.div_le_self X e)
      have ha : |((n : ℕ) : ℝ)-(X : ℝ)/e|≤1 := Sieve.abs_natDiv_sub_div_le (mem_Icc.mp he).1
      have eq : f e-main e=(completeDivisorError n+2*γ*n)-(2*γ)*((n : ℝ)-(X : ℝ)/e) := by dsimp [f,main,n]; ring
      rw [eq]
      apply (abs_sub _ _).trans
      rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ)≤2)]
      exact add_le_add ((abs_completeDivisorError_add_le n).trans (mul_le_mul_of_nonneg_left hl (by norm_num)))
        ((mul_le_mul_of_nonneg_left ha (by positivity)).trans_eq (mul_one _)))
  rw [stencil_sub,hz,sub_zero] at hh
  rw [complete_primeErrorTail_identity D hx,sub_sub_cancel]
  exact hh

#print axioms complete_primeErrorTail_identity
#print axioms complete_primeErrorTail_bound
#print axioms completeComplementTail_sub_primeErrorTail
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
