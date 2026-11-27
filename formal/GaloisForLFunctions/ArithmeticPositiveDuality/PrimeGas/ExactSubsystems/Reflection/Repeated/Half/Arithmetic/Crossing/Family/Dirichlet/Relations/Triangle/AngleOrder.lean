import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.Triangle.PhaseRatios
import GaloisForLFunctions.HTGeometry.PrimeCyclotomicFieldEscape

/-! # Uniform order of torsion directions over a finite field of lengths -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations

open IntermediateField Polynomial
open scoped IntermediateField Polynomial

/-- Every prime power dividing n is at most twice φ(n), so the factorial
contains n with all its prime multiplicities. -/
theorem dvd_factorial_of_totient_le {n D : ℕ} (hn : 0<n) (h : n.totient ≤ D) :
    n ∣ (2*D).factorial := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p k hp dvd
  cases k with
  | zero => simp
  | succ k =>
    have lower := Nat.le_of_dvd (Nat.totient_pos.mpr hn) (Nat.totient_dvd_of_dvd dvd)
    rw [Nat.totient_prime_pow_succ hp] at lower
    have two : p ≤ 2*(p-1) := by have := hp.two_le; omega
    have bound : p^(k+1) ≤ 2*D := by
      rw [pow_succ]
      calc p^k*p ≤ p^k*(2*(p-1)) := Nat.mul_le_mul_left _ two
           _ = 2*(p^k*(p-1)) := by ring
           _ ≤ 2*D := Nat.mul_le_mul_left _ (lower.trans h)
    exact Nat.dvd_factorial (pow_pos hp.pos _) bound

/-- A bounded-degree equation for a torsion phase over K bounds its order
uniformly in terms of the rational degree of K. -/
theorem angle_order (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] {U : ℂ} {m : ℕ}
    (hm : 0 < m) (unit : U^m=1) (traceSq : (U+U⁻¹)^2 ∈ K) :
    U^((2*(4*Module.finrank ℚ K)).factorial)=1 := by
  let c : K := ⟨(U+U⁻¹)^2,traceSq⟩
  let P : K[X] := X^4+(C (2-c))*X^2+1
  have nz : U ≠ 0 := norm_pos_iff.mp (by rw [phase_norm hm unit]; exact zero_lt_one)
  have root : Polynomial.aeval U P=0 := by
    simp only [P, map_add,map_pow,aeval_X,map_mul,aeval_C,map_sub,map_ofNat,map_one]
    change U^4+(2-(U+U⁻¹)^2)*U^2+1=0
    field_simp
    ring
  have ne : P ≠ 0 := by
    intro eq
    have ev := congrArg (Polynomial.eval (0 : K)) eq
    simp [P] at ev
  have deg : P.natDegree ≤ 4 := by dsimp only [P]; compute_degree
  let L := K⟮U⟯
  have integral := (torsion_algebraic K hm unit).isIntegral
  letI : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional integral
  letI : FiniteDimensional ℚ L := Module.Finite.trans K L
  let w : L := ⟨U,IntermediateField.mem_adjoin_simple_self K U⟩
  have hp : IsPrimitiveRoot w (orderOf U) := (IsPrimitiveRoot.orderOf U).of_map_of_injective L.val.injective
  have ord : 0<orderOf U := Nat.pos_of_dvd_of_pos (orderOf_dvd_of_pow_eq_one unit) hm
  have dim : Module.finrank K L ≤ 4 :=
    (IntermediateField.adjoin.finrank integral).le.trans ((natDegree_le_of_dvd (minpoly.dvd K U root) ne).trans deg)
  have bound : (orderOf U).totient ≤ 4*Module.finrank ℚ K := by
    rw [← GaloisForLFunctions.HTGeometry.minpoly_natDegree_of_isPrimitiveRoot ord hp,mul_comm 4]
    exact (minpoly.natDegree_le w).trans
      ((Module.finrank_mul_finrank ℚ K L).symm.le.trans (Nat.mul_le_mul_left _ dim))
  exact orderOf_dvd_iff_pow_eq_one.mp (dvd_factorial_of_totient_le ord bound)

#print axioms dvd_factorial_of_totient_le
#print axioms angle_order

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations
