import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Spectrum

/-! # Integer polynomial of a centered occupation list -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice

open Finset Real Polynomial

variable {I : Type*} [Fintype I]

/-- Clear the common denominator of centered occupations and shift the smallest
exponent into the ordinary integer polynomial ring. -/
def imbalancePolynomial (k : I → ℕ) : ℤ[X] :=
  let n := Fintype.card I
  let m := ∑ i, k i
  ∑ i, (X^(n*(m+k i)) - X^(n*(m-k i)+2*m))

theorem imbalancePolynomial_eval [Nonempty I] (k : I → ℕ) (t : ℝ) :
    let n := (Fintype.card I : ℝ)
    let m := ((∑ i, k i : ℕ) : ℝ)
    aeval (exp (t/n)) (imbalancePolynomial k) =
      exp ((t/n)*(n*m+m))*oddTrace (centered (fun i => (k i : ℝ))) t := by
  dsimp only
  let m := ∑ i, k i
  let n := Fintype.card I
  have nz : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have center (i : I) : centered (fun i => (k i : ℝ)) i=(k i : ℝ)-(m : ℝ)/n := by
    simp only [centered,meanEnergy,m,n,Nat.cast_sum]
  simp only [imbalancePolynomial,map_sum,map_sub,map_pow,aeval_X,oddTrace,oddTerm]
  conv_rhs => rw [mul_sum]
  apply sum_congr rfl
  intro i _
  have le : k i ≤ m := single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (mem_univ i)
  rw [← exp_nat_mul,← exp_nat_mul,center,mul_sub,← exp_add,← exp_add]
  change exp (((n*(m+k i) : ℕ) : ℝ)*(t/n)) - exp (((n*(m-k i)+2*m : ℕ) : ℝ)*(t/n)) =
    exp ((t/n)*((n : ℝ)*m+m)+t*((k i : ℝ)-m/n)) - exp ((t/n)*((n : ℝ)*m+m)+(-t)*((k i : ℝ)-m/n))
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_sub le,Nat.cast_ofNat]
  congr 1 <;> congr 1 <;> field_simp <;> ring

/-- The positive exponential factor never vanishes, so asymmetry is equivalent
to a nonzero polynomial. -/
theorem imbalancePolynomial_ne_zero {k : I → ℕ}
    (asym : ¬Reflects (fun i => (k i : ℝ))) : imbalancePolynomial k ≠ 0 := by
  rcases isEmpty_or_nonempty I with he | hn
  · exact (asym ⟨0,Equiv.refl _,fun i => (he.false i).elim⟩).elim
  · letI := hn
    intro zero
    apply asym
    apply (centered_heat_iff_reflects _).mp
    intro j _ _
    apply (agrees_odd _ _).mpr
    have h := imbalancePolynomial_eval k (j : ℝ)
    dsimp only at h
    rw [zero,map_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (exp_ne_zero _)

/-- Opposite heat traces agree exactly at positive exponential roots. -/
theorem imbalancePolynomial_root [Nonempty I] (k : I → ℕ) (t : ℝ) :
    aeval (exp (t/Fintype.card I)) (imbalancePolynomial k)=0 ↔
      agrees (fun i => (k i : ℝ)) t := by
  rw [imbalancePolynomial_eval,agrees_odd,mul_eq_zero,or_iff_right (exp_ne_zero _)]

#print axioms imbalancePolynomial_ne_zero
#print axioms imbalancePolynomial_root

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice
