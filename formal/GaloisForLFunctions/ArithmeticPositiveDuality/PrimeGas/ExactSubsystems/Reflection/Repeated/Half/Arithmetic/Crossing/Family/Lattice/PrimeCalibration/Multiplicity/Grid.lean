import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Radix
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Prime

/-! # Unit-damping roots on the integer occupation grid -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity

open Finset Polynomial Real

variable {I : Type*} [Fintype I]

/-- A prime equality fixes the reflection center to an integer or a half-integer. -/
theorem doubled_mean_integral [Nonempty I] (k : I → ℕ) (p : Nat.Primes)
    (hit : accepts k p 1) : Fintype.card I ∣ 2*∑ i, k i := by
  let a (i : I) : ℕ+ := ⟨p.val^k i,pow_pos p.property.pos _⟩
  have h : Coincides a (1 : ℕ) := by
    change agrees (primeModes p k) ((1 : ℕ) : ℝ)
    simpa only [accepts,gibbs_order,one_mul,Nat.cast_one] using hit
  have prod : labelProduct a=p.val^(∑ i, k i) := prod_pow_eq_pow_sum _ k p.val
  have val := dimension_dvd h p.val
  simpa only [prod, Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul,
    p.property.factorization_self,mul_one] using val

/-- On an integral doubled-mean grid, division of all exponents by the
dimension leaves integral coefficients and the physical prime as root. -/
def integerGrid (k : I → ℕ) (c : ℕ) : ℤ[X] :=
  let m := ∑ i, k i
  ∑ i, (X^(m+k i)-X^(m-k i+c))

theorem expand_grid (k : I → ℕ) {c : ℕ} (align : 2*(∑ i, k i)=Fintype.card I*c) :
    expand ℤ (Fintype.card I) (integerGrid k c)=imbalancePolynomial k := by
  simp only [integerGrid,imbalancePolynomial,map_sum,map_sub,map_pow,expand_X,←pow_mul,
    Nat.mul_add (Fintype.card I) _ c,align]

/-- A unit-damping Gibbs equality can be tested by evaluating a single
integer polynomial at the selected elementary prime. -/
theorem grid_root [Nonempty I] (k : I → ℕ) {c : ℕ}
    (align : 2*(∑ i, k i)=Fintype.card I*c) (p : Nat.Primes) :
    (integerGrid k c).eval (p.val : ℤ)=0 ↔ accepts k p 1 := by
  let x := exp (log (p.val : ℝ)/Fintype.card I)
  have npos : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have power : x^Fintype.card I=(p.val : ℝ) := by
    change exp (log (p.val : ℝ)/Fintype.card I)^Fintype.card I=_
    rw [← exp_nat_mul,mul_comm,div_mul_cancel₀ _ npos,exp_log (Nat.cast_pos.mpr p.property.pos)]
  have test := imbalancePolynomial_root k (log (p.val : ℝ))
  rw [← expand_grid k align,expand_eq_comp_X_pow,aeval_comp,map_pow,aeval_X] at test
  change aeval (x^Fintype.card I) (integerGrid k c)=0 ↔ _ at test
  rw [power] at test
  rw [accepts_iff,abs_one,one_mul]
  change _ ↔ agrees (fun i => (k i : ℝ)) (log (p.val : ℝ))
  refine Iff.trans ?_ test
  have castEval := Polynomial.eval₂_at_apply (p := integerGrid k c) (algebraMap ℤ ℝ) (p.val : ℤ)
  calc
    _ ↔ (((integerGrid k c).eval (p.val : ℤ) : ℤ) : ℝ)=0 := Int.cast_eq_zero.symm
    _ ↔ _ := Iff.of_eq (congrArg (· = (0 : ℝ)) castEval.symm)

/-- For a packet supported between zero and its doubled mean, the two
partition sums are ordinary reflected power sums. -/
theorem reflected_powers [Nonempty I] (k : I → ℕ) {c : ℕ}
    (align : 2*(∑ i, k i)=Fintype.card I*c) (bounded : ∀ i, k i≤c) (p : Nat.Primes) :
    accepts k p 1 ↔ (∑ i, (p.val : ℤ)^k i)=∑ i, (p.val : ℤ)^(c-k i) := by
  let m := ∑ i, k i
  have shift (i : I) : m-k i+c=m+(c-k i) := by
    have h : k i ≤ m := single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (mem_univ i)
    have := bounded i
    omega
  rw [←grid_root k align p]
  change (∑ i, ((X : ℤ[X])^(m+k i)-X^(m-k i+c))).eval (p.val : ℤ)=0 ↔ _
  simp only [shift,pow_add,←mul_sub,←mul_sum]
  simp only [eval_mul,eval_finsetSum,eval_sub,eval_pow,eval_X]
  rw [mul_eq_zero,or_iff_right (pow_ne_zero _ (Int.natCast_ne_zero.mpr p.property.ne_zero)),
    sum_sub_distrib,sub_eq_zero]

#print axioms expand_grid
#print axioms reflected_powers
#print axioms doubled_mean_integral
#print axioms grid_root

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity
