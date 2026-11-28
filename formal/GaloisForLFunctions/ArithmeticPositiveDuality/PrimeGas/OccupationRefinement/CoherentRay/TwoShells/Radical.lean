import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Carry

/-! # No positive powers of a prime radical differ by one -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay.TwoShells

open Polynomial
open Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity

/-- A trinomial with constant coefficient minus one cannot vanish at a
positive-order radical of a prime when both other powers are nonconstant. -/
theorem prime_radical_gap (p : Nat.Primes) {m j k : ℕ} (hm : 0 < m) (hj : 0 < j) (hk : 0 < k)
    {r : ℝ} (root : r^m=(p.val:ℝ)) : r^k-r^j≠1 := by
  intro gap
  let P : ℤ[X] := X^k-X^j-1
  have van : aeval r P=0 := by simp only [P,map_sub,map_pow,map_one,aeval_X,gap,sub_self]
  obtain ⟨Q,H⟩ := radical_factor p hm root P van
  have atZero := congrArg (Polynomial.eval (0:ℤ)) H
  simp only [P,eval_sub,eval_pow,eval_X,eval_one,eval_C,eval_mul,zero_pow hj.ne',zero_pow hk.ne',
    zero_pow hm.ne',sub_self,zero_sub] at atZero
  have divides : (p.val:ℤ) ∣ 1 := ⟨Q.eval 0,by linear_combination -atZero⟩
  exact (Nat.prime_iff_prime_int.mp p.property).not_unit (isUnit_iff_dvd_one.mpr divides)

private theorem excludes_order (p : Nat.Primes) {r x y : ℝ} {m j k : ℕ} (hm : 0 < m)
    (root : r^m=(p.val:ℝ)) (total : x+y=1) (left : x*r^j=1) (right : y*r^k=1) (lt : j < k) : False := by
  have split : r^k=r^j*r^(k-j) := by rw [←pow_add,show j+(k-j)=k by omega]
  apply prime_radical_gap p hm (by omega : 0 < k-j) (by omega : 0 < k) root
  calc
    r^k-r^(k-j) = (x+y)*r^k-(x*r^j)*r^(k-j) := by rw [total,left,one_mul,one_mul]
    _ = y*r^k := by linear_combination x*split
    _ = 1 := right

/-- Two complementary reciprocal powers of a prime radical have equal
exponents and equal probabilities. -/
theorem complementary_powers (p : Nat.Primes) {r x y : ℝ} {m j k : ℕ} (hm : 0 < m) (hr : 0 < r)
    (root : r^m=(p.val:ℝ)) (total : x+y=1) (left : x*r^j=1) (right : y*r^k=1) : x=y := by
  rcases lt_trichotomy j k with lt|eqn|lt
  · exact False.elim (excludes_order p hm root total left right lt)
  · rw [eqn] at left
    exact mul_right_cancel₀ (pow_ne_zero _ hr.ne') (left.trans right.symm)
  · exact False.elim (excludes_order p hm root ((add_comm y x).trans total) right left lt)

#print axioms prime_radical_gap
#print axioms complementary_powers

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay.TwoShells
