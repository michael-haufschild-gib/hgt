import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimeFloorRowBeyondTheSquareRoot

/-!
# Factorial completion on cofactor multiples

On the cofactor class r ∣ v, the complete Mangoldt price is a factorial ratio
at three divided endpoints. Each removed prime power costs at most its
Mangoldt weight. The bound holds for moving divisors and a sharp prime cut.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Logarithmic center for a complete row of cofactor multiples. -/
def divisibleCofactorFactorial (n r : ℕ) : ℝ :=
  Real.log ((4*n/r).factorial:ℕ)-2*Real.log ((3*n/r).factorial:ℕ)+Real.log ((2*n/r).factorial:ℕ)

/-- Ordinary prime price of all cofactor multiples of r, including v=r.
The primitive restriction on the prime is taken at the original midpoint. -/
def divisibleCofactorPrimePrice (n Q r : ℕ) : ℝ :=
  ∑ p ∈ (Icc 1 (4*n/r)).filter (fun p => Q < p ∧ p.Prime ∧ ¬p ∣ n),
    Real.log p*midpointFloorWeight n (p*r)

private theorem zero_beyond_divided_cut {k n r p : ℕ} (hr : 0 < r) (h : k*n/r < p) :
    k*n/(p*r)=0 :=
  Nat.div_eq_of_lt ((Nat.div_lt_iff_lt_mul hr).mp h)

/-- Full signed price at an arbitrary dividing scale. All three factorials
use the original floor before subtraction. -/
theorem factorial_multiple_cofactor_identity (n : ℕ) {r : ℕ} (hr : 0 < r) :
    (∑ p ∈ Icc 1 (4*n/r), vonMangoldt p*midpointFloorWeight n (p*r)) =
      divisibleCofactorFactorial n r := by
  have row (k : ℕ) (hk : k ≤ 4) :
      (∑ p ∈ Icc 1 (4*n/r), vonMangoldt p*((k*n/(p*r):ℕ):ℝ)) =
        Real.log ((k*n/r).factorial:ℕ) := by
    have h := mangoldt_floor (k*n/r) 1
    simp only [Nat.div_one,Nat.div_div_eq_div_mul,Nat.mul_comm r] at h
    rw [←h]
    symm
    apply sum_subset (Icc_subset_Icc_right (Nat.div_le_div_right (Nat.mul_le_mul_right n hk)))
    intro p hp hnot
    have hl := (mem_Icc.mp hp).1
    have hcut : k*n/r < p := lt_of_not_ge (fun h => hnot (mem_Icc.mpr ⟨hl,h⟩))
    rw [zero_beyond_divided_cut hr hcut,Nat.cast_zero,mul_zero]
  rw [divisibleCofactorFactorial,←row 4 (by decide),←row 3 (by decide),←row 2 (by decide),
    mul_sum,←sum_sub_distrib,←sum_add_distrib]
  exact sum_congr rfl fun p _ => by unfold midpointFloorWeight; ring

#print axioms factorial_multiple_cofactor_identity

private theorem prime_divisors_log_bound {n : ℕ} (hn : 0 < n) :
    (∑ p ∈ n.primeFactors,Real.log p) ≤ Real.log n := by
  have hprod : 0 < ∏ p ∈ n.primeFactors,p := prod_pos fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).pos
  have h := Real.log_le_log (Nat.cast_pos.mpr hprod)
    ((Nat.cast_le (α:=ℝ)).mpr (Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)))
  rwa [Nat.cast_prod,Real.log_prod (fun p hp =>
    Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero)] at h

/-- The complete ordinary row costs the short Mangoldt mass, the proper
powers at the divided scale, and the logarithm of the forbidden prime factors.
The constants and the midpoint are the same for all divisors r. -/
theorem divisible_cofactor_factorial_error {n r : ℕ} (hn : 0 < n) (hr : 0 < r) (Q : ℕ) :
    |divisibleCofactorPrimePrice n Q r-divisibleCofactorFactorial n r| ≤
      Chebyshev.psi Q + (Chebyshev.psi (4*n/r:ℕ)-Chebyshev.theta (4*n/r:ℕ)) + Real.log n := by
  classical
  let T := 4*n/r
  let S := Icc 1 T
  let ok (p : ℕ) := Q < p ∧ p.Prime ∧ ¬p ∣ n
  let f (p : ℕ) := vonMangoldt p*midpointFloorWeight n (p*r)
  have full := factorial_multiple_cofactor_identity n hr
  change (∑ p ∈ S, f p)=_ at full
  have price : divisibleCofactorPrimePrice n Q r=∑ p ∈ S.filter ok,f p := by
    apply sum_congr rfl
    intro p hp
    rw [show f p=vonMangoldt p*midpointFloorWeight n (p*r) from rfl,
      vonMangoldt_apply_prime (mem_filter.mp hp).2.2.1]
  have hsplit := sum_filter_add_sum_filter_not S ok f
  rw [full,←price] at hsplit
  rw [show divisibleCofactorPrimePrice n Q r-divisibleCofactorFactorial n r =
    -(∑ p ∈ S.filter (fun p => ¬ok p),f p) by linarith only [hsplit],abs_neg]
  apply (abs_sum_le_sum_abs _ _).trans
  have drop : (∑ p ∈ S.filter (fun p => ¬ok p),|f p|) ≤
      (∑ p ∈ S.filter (· ≤ Q),vonMangoldt p) +
      (∑ p ∈ S.filter (fun p => ¬p.Prime),vonMangoldt p) +
      ∑ p ∈ S.filter (fun p => p.Prime ∧ p ∣ n), Real.log p := by
    simp only [sum_filter,←sum_add_distrib]
    apply sum_le_sum
    intro p hp
    have hp0 := (mem_Icc.mp hp).1
    have hμ := vonMangoldt_nonneg (n:=p)
    have hb : |f p| ≤ vonMangoldt p := by
      rw [show f p=vonMangoldt p*midpointFloorWeight n (p*r) from rfl,abs_mul,abs_of_nonneg hμ]
      exact mul_le_of_le_one_right hμ (abs_midpoint_division_le_one (Nat.mul_pos hp0 hr) n)
    by_cases hq : p ≤ Q <;> by_cases hpr : p.Prime <;> by_cases hd : p ∣ n <;>
      simp only [ok,hq,hpr,hd,not_lt,lt_iff_not_ge,true_and,and_true,and_false,false_and,
        not_true_eq_false,not_false_eq_true,if_true,if_false,add_zero,zero_add] at * <;>
      first | exact hb | exact le_rfl | linarith only [hb,hμ,Real.log_natCast_nonneg p,
        vonMangoldt_apply_prime (p:=p) (by assumption)] | linarith only [hb,hμ]
  have hi (X : ℕ) : Ioc 0 X=Icc 1 X := by ext p; simp only [mem_Ioc,mem_Icc]; omega
  have low : (∑ p ∈ S.filter (· ≤ Q),vonMangoldt p) ≤ Chebyshev.psi Q := by
    rw [Chebyshev.psi,Nat.floor_natCast,hi]
    apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => vonMangoldt_nonneg)
    exact fun p hp => mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp hp).1).1,(mem_filter.mp hp).2⟩
  have power : (∑ p ∈ S.filter (fun p => ¬p.Prime),vonMangoldt p) =
      Chebyshev.psi T-Chebyshev.theta T := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,Nat.floor_natCast,hi]
  have forb : (∑ p ∈ S.filter (fun p => p.Prime ∧ p ∣ n),Real.log p) ≤ Real.log n := by
    apply le_trans _ (prime_divisors_log_bound hn)
    apply sum_le_sum_of_subset_of_nonneg _ (fun p _ _ => Real.log_natCast_nonneg p)
    exact fun p hp => Nat.mem_primeFactors.mpr ⟨(mem_filter.mp hp).2.1,(mem_filter.mp hp).2.2,hn.ne'⟩
  exact drop.trans (add_le_add (add_le_add low power.le) forb)

#print axioms divisible_cofactor_factorial_error

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
