import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Grid

/-! # Joint divisibility and multiplicity cost of invisible elementary primes -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity

open Finset Polynomial

variable {I : Type*} [Fintype I]

/-- Every accepted prime at the same positive rational damping divides
the same leading coefficient. Distinct prime factors therefore multiply. -/
theorem prime_product_dvd [Nonempty I] (k : I → ℕ) (S : Finset Nat.Primes)
    {d : ℚ} (hd : 0<d) (hit : ∀ p∈S, accepts k p d) :
    (∏ p ∈ S, p.val) ∣ (imbalancePolynomial k).leadingCoeff.natAbs := by
  let a := (imbalancePolynomial k).leadingCoeff
  have single (p : Nat.Primes) (hp : p∈S) : (p.val : ℤ) ∣ a := by
    have eq := (accepts_iff k p d).mp (hit p hp)
    rw [abs_of_pos (Rat.cast_pos.mpr hd)] at eq
    have powDiv := Sparse.rational_divisibility p k hd eq
    have num := Rat.num_pos.mpr hd
    have base : (p.val : ℤ) ∣ (p.val : ℤ)^d.num.toNat := dvd_pow_self _ (by omega)
    exact (Nat.prime_iff_prime_int.mp p.property).dvd_of_dvd_pow (base.trans powDiv)
  have joint : (∏ p ∈ S, (p.val : ℤ)) ∣ a := by
    apply prod_dvd_of_coprime _ single
    intro p _ q _ diff
    exact Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes p.property q.property).mpr
      (fun eq => diff (Subtype.ext eq)))
  apply Int.natCast_dvd.mp
  simpa only [Nat.cast_prod] using joint

/-- If an asymmetric packet accepts a set S at unit damping, its peak
exceeds (p-1) times the product of S for each tested p in S. -/
theorem joint_unit_bound (k : I → ℕ) (S : Finset Nat.Primes) (p : Nat.Primes) (hp : p∈S)
    (asym : ¬Reflects (levels k)) (hit : ∀ q∈S, accepts k q 1)
    {H : ℕ} (cap : ∀ m, Sparse.multiplicity k m≤H) :
    (p.val-1)*(∏ q ∈ S, q.val)<H := by
  classical
  rcases isEmpty_or_nonempty I with he | hn
  · exact (asym ⟨0,Equiv.refl _,fun i => (he.false i).elim⟩).elim
  letI := hn
  obtain ⟨c,align⟩ := doubled_mean_integral k p (hit p hp)
  let P := integerGrid k c
  have expandP : expand ℤ (Fintype.card I) P=imbalancePolynomial k := expand_grid k align
  have nz := imbalancePolynomial_ne_zero asym
  have lead : (imbalancePolynomial k).leadingCoeff=P.leadingCoeff := by
    rw [←expandP,leadingCoeff_expand Fintype.card_pos]
  have Pnz : P≠0 := by
    intro z
    exact nz (by rw [←expandP,z,map_zero])
  have digits (j : ℕ) : (P.coeff j).natAbs≤H := by
    have bound := Sparse.coefficient_bound k cap (j*Fintype.card I)
    rwa [←expandP,coeff_expand_mul Fintype.card_pos] at bound
  have div := prime_product_dvd k S (d := 1) zero_lt_one (by simpa only [Rat.cast_one] using hit)
  rw [lead] at div
  exact (Nat.mul_le_mul_left _ (Nat.le_of_dvd (Int.natAbs_pos.mpr (leadingCoeff_ne_zero.mpr Pnz)) div)).trans_lt
    (root_height P Pnz p.val H p.property.one_lt ((grid_root k align p).mpr (hit p hp)) digits)

#print axioms prime_product_dvd
#print axioms joint_unit_bound

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity
