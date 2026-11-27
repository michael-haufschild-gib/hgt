import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Radix
import GaloisForLFunctions.HTGeometry.EisensteinRadical

/-! # Coefficient bounds at prime radicals of arbitrary order -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity

open Finset Polynomial

/-- The first quotient coefficient reaching a given magnitude cannot be
canceled by the preceding coefficient in the same residue class. -/
theorem stride_digit (Q : ℤ[X]) {b K H j : ℕ} (hb : 1<b) (hK : 0<K)
    (cap : ∀ i, (((X^K-C (b : ℤ))*Q).coeff i).natAbs≤H) (nz : Q.coeff j≠0) :
    (b-1)*(Q.coeff j).natAbs < H := by
  classical
  let P := (X^K-C (b : ℤ))*Q
  let a := |Q.coeff j|
  have pos : 0<a := abs_pos.mpr nz
  have attained : ∃ k, a ≤ |Q.coeff k| := ⟨j,le_rfl⟩
  let i := Nat.find attained
  have atIndex : a ≤ |Q.coeff i| := Nat.find_spec attained
  have below : |(Q*X^K).coeff i| < a := by
    rw [coeff_mul_X_pow']
    split
    · rename_i h
      have earlier : i-K < i := by omega
      exact lt_of_not_ge (Nat.find_min attained earlier)
    · simpa only [abs_zero] using pos
  have coeff : (b : ℤ)*Q.coeff i=(Q*X^K).coeff i-P.coeff i := by
    change (b : ℤ)*Q.coeff i=(Q*X^K).coeff i-((X^K-C (b : ℤ))*Q).coeff i
    rw [sub_mul,coeff_sub,mul_comm (X^K) Q,coeff_C_mul]
    abel
  have bpos : (0 : ℤ)≤b := Int.natCast_nonneg _
  have limit : (b : ℤ)*a<a+H := calc
    _ ≤ (b : ℤ)*|Q.coeff i| := mul_le_mul_of_nonneg_left atIndex bpos
    _ = |(b : ℤ)*Q.coeff i| := by rw [abs_mul,abs_of_nonneg bpos]
    _ ≤ |(Q*X^K).coeff i| + |P.coeff i| := by rw [coeff]; exact abs_sub _ _
    _ < _ := add_lt_add_of_lt_of_le below (by simpa only [Int.natCast_natAbs] using Int.ofNat_le.mpr (cap i))
  have result : ((b-1 : ℕ) : ℤ)*((Q.coeff j).natAbs : ℤ)<H := by
    rw [Nat.cast_sub hb.le,Nat.cast_one,Int.natCast_natAbs]
    change ((b : ℤ)-1)*a<H
    linarith only [limit]
  exact_mod_cast result

/-- A binomial divisor of any stride forces the same strict leading
coefficient bound as an integer root. -/
theorem stride_height {P : ℤ[X]} (nz : P≠0) {b K H : ℕ} (hb : 1<b) (hK : 0<K)
    (factor : (X^K-C (b : ℤ)) ∣ P) (cap : ∀ j, (P.coeff j).natAbs≤H) :
    (b-1)*P.leadingCoeff.natAbs < H := by
  obtain ⟨Q,eq⟩ := factor
  have lead : P.leadingCoeff=Q.leadingCoeff := by
    rw [eq,leadingCoeff_mul,(monic_X_pow_sub_C (b : ℤ) hK.ne').leadingCoeff,one_mul]
  have digit : Q.coeff Q.natDegree≠0 := by
    rw [coeff_natDegree,←lead]
    exact leadingCoeff_ne_zero.mpr nz
  simpa only [coeff_natDegree,←lead] using stride_digit Q hb hK (eq ▸ cap) digit

/-- Eisenstein's criterion turns a positive prime radical root into a
binomial divisor over the integers. -/
theorem radical_factor (p : Nat.Primes) {K : ℕ} (hK : 0<K) {x : ℝ}
    (power : x^K=(p.val : ℝ)) (P : ℤ[X]) (root : aeval x P=0) :
    (X^K-C (p.val : ℤ)) ∣ P := by
  let F : ℤ[X] := X^K-C (p.val : ℤ)
  have pp : Prime (p.val : ℤ) := Nat.prime_iff_prime_int.mp p.property
  have mon : F.Monic := monic_X_pow_sub_C _ hK.ne'
  have irr : Irreducible F :=
    (GaloisForLFunctions.HTGeometry.isEisensteinAt_X_pow_sub_C pp hK).irreducible
      ((Ideal.span_singleton_prime pp.ne_zero).mpr pp) mon.isPrimitive
      (by rw [natDegree_X_pow_sub_C]; omega)
  have van : aeval x F=0 := by simp only [F,map_sub,map_pow,aeval_X,aeval_C,power]; simp
  have integ : IsIntegral ℤ x := ⟨F,mon,van⟩
  have dm := minpoly.isIntegrallyClosed_dvd integ van
  have back := ((irr.dvd_iff.mp dm).resolve_left (minpoly.not_isUnit ℤ x)).dvd
  exact back.trans (minpoly.isIntegrallyClosed_dvd integ root)

#print axioms stride_digit
#print axioms stride_height
#print axioms radical_factor

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity
