import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Bound
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Carry
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Arithmetic

/-! # Joint multiplicity obstruction at algebraic Gibbs damping -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity

open Polynomial Finset Real

variable {I : Type*} [Fintype I]

/-- Clearing the numerator inserts zero coefficients, so the coefficient
height obstruction at a prime radical is uniform in the rational damping. -/
theorem rational_radical [Nonempty I] (k : I → ℕ) (p : Nat.Primes) {d : ℚ} (hd : 0<d)
    (pass : accepts k p d) : ∃ x : ℝ, x^(d.den*Fintype.card I)=(p.val : ℝ) ∧
      aeval x (expand ℤ d.num.toNat (imbalancePolynomial k))=0 := by
  let n := Fintype.card I
  let A := d.num.toNat
  let K := d.den*n
  let Q := expand ℤ A (imbalancePolynomial k)
  let x := exp (log (p.val : ℝ)/K)
  have kpos : 0<K := Nat.mul_pos d.den_pos Fintype.card_pos
  have npos : (n : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have bpos : (d.den : ℝ)≠0 := Nat.cast_ne_zero.mpr d.den_ne_zero
  have frac : (d.den : ℝ)*(d : ℝ)=(A : ℝ) := by
    have num : (A : ℝ)=(d.num : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (Rat.num_pos.mpr hd).le
    rw [num]
    exact_mod_cast d.den_mul_eq_num
  have xK : x^K=(p.val : ℝ) := by
    rw [←exp_nat_mul,mul_comm,div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr kpos.ne'),
      exp_log (Nat.cast_pos.mpr p.property.pos)]
  have xA : x^A=exp ((d : ℝ)*log (p.val : ℝ)/n) := by
    rw [←exp_nat_mul]
    congr 1
    change (A : ℝ)*(log (p.val : ℝ)/((d.den*n : ℕ) : ℝ))=_
    rw [←frac,Nat.cast_mul]
    field_simp [npos,bpos]
  have reading := (accepts_iff k p d).mp pass
  rw [abs_of_pos (Rat.cast_pos.mpr hd)] at reading
  have root : aeval x Q=0 := by
    dsimp only [Q]
    rw [expand_eq_comp_X_pow,aeval_comp,map_pow,aeval_X,xA]
    exact (imbalancePolynomial_root k _).mpr reading
  exact ⟨x,xK,root⟩

theorem rational_height [Nonempty I] (k : I → ℕ) (p : Nat.Primes) {d : ℚ} (hd : 0<d)
    (asym : ¬Reflects (levels k)) (pass : accepts k p d) {H : ℕ}
    (cap : ∀ m, Sparse.multiplicity k m≤H) :
    (p.val-1)*(imbalancePolynomial k).leadingCoeff.natAbs < H := by
  let A := d.num.toNat
  let Q := expand ℤ A (imbalancePolynomial k)
  have apos : 0<A := by have := Rat.num_pos.mpr hd; dsimp only [A]; omega
  have kpos := Nat.mul_pos d.den_pos (Fintype.card_pos (α := I))
  obtain ⟨x,xK,root⟩ := rational_radical k p hd pass
  have lead : Q.leadingCoeff=(imbalancePolynomial k).leadingCoeff := leadingCoeff_expand apos
  have nz : Q≠0 := by
    apply leadingCoeff_ne_zero.mp
    rw [lead]
    exact leadingCoeff_ne_zero.mpr (imbalancePolynomial_ne_zero asym)
  have digits (j : ℕ) : (Q.coeff j).natAbs ≤ H := by
    rw [show Q.coeff j=_ from coeff_expand apos (imbalancePolynomial k) j]
    split
    · exact Sparse.coefficient_bound k cap _
    · exact Nat.zero_le _
  rw [←lead]
  exact stride_height nz p.property.one_lt kpos (radical_factor p kpos xK Q root) digits

/-- For every accepted prime, the peak multiplicity exceeds its predecessor
times the product of all tested primes. This holds at every positive algebraic damping. -/
theorem joint_algebraic_bound (k : I → ℕ) (S : Finset Nat.Primes) (p : Nat.Primes) (hp : p∈S)
    {d : ℝ} (hd : 0<d) (alg : IsAlgebraic ℚ d) (asym : ¬Reflects (levels k))
    (pass : ∀ q∈S, accepts k q d) {H : ℕ} (cap : ∀ m, Sparse.multiplicity k m≤H) :
    (p.val-1)*(∏ q ∈ S, q.val)<H := by
  classical
  rcases isEmpty_or_nonempty I with he | hn
  · exact (asym ⟨0,Equiv.refl _,fun i => (he.false i).elim⟩).elim
  letI := hn
  have rational : ¬ Irrational d := fun irr =>
    asym ((algebraic_irrational_detected p k hd alg irr).mp (pass p hp))
  obtain ⟨r,rfl⟩ := Classical.not_not.mp rational
  have pos := Rat.cast_pos.mp hd
  have div := prime_product_dvd k S pos pass
  have nz := leadingCoeff_ne_zero.mpr (imbalancePolynomial_ne_zero asym)
  exact (Nat.mul_le_mul_left _ (Nat.le_of_dvd (Int.natAbs_pos.mpr nz) div)).trans_lt
    (rational_height k p pos asym (pass p hp) cap)

#print axioms rational_radical
#print axioms rational_height
#print axioms joint_algebraic_bound

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity
