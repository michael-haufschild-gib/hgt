import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Probabilities
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AssociativeComposition

/-! # A prime square distinguishes two exchange-symmetric composition laws -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement

private theorem uniform_count (p : Nat.Primes) (k : ℕ) :
    (singleProfile*singleProfile).val (p.val^k)=k+1 := by
  change (ArithmeticFunction.zeta*ArithmeticFunction.zeta) (p.val^k)=k+1
  rw [ArithmeticFunction.mul_zeta_apply,Nat.sum_divisors_prime_pow p.property]
  simp only [ArithmeticFunction.zeta_apply_ne (pow_ne_zero _ p.property.ne_zero),
    Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one]

/-- Two copies with constant integer multiplicities are uniform on the
ordered factorizations of a prime power. -/
theorem uniform_ray (p : Nat.Primes) (j k : ℕ) :
    share singleProfile singleProfile (p.val^(j+k)) (p.val^j,p.val^k)=1/(j+k+1:ℕ) := by
  have one (m : ℕ) : singleProfile.val (p.val^m)=1 :=
    ArithmeticFunction.zeta_apply_ne (pow_ne_zero _ p.property.ne_zero)
  simp only [share,one,uniform_count,Nat.cast_one,one_mul]

/-- On a balanced channel with two copies of one prime, independent
routing gives twice as much mass to the middle outcome as to either endpoint. -/
theorem balanced_square {u : ℝ} (hu : 0<u) (p : Nat.Primes) :
    probability u u 1 (p.val^2)=1/4 ∧ probability u u p.val p.val=1/2 ∧
    probability u u (p.val^2) 1=1/4 ∧ share singleProfile singleProfile (p.val^2) (p.val,p.val)=1/3 := by
  have half : u/(u+u)=(1:ℝ)/2 := (div_eq_iff (add_pos hu hu).ne').mpr (by ring)
  have left := prime_ray hu hu p 0 2
  have middle := prime_ray hu hu p 1 1
  have right := prime_ray hu hu p 2 0
  have uniform := uniform_ray p 1 1
  norm_num [binomial,half,Nat.choose_succ_succ] at left middle right uniform ⊢
  exact ⟨left,middle,right,uniform⟩

#print axioms uniform_ray
#print axioms balanced_square

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement
