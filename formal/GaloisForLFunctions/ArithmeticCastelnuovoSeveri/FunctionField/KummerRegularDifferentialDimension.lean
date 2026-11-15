import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRegularDifferentialEquiv
import GaloisForLFunctions.HTGeometry.PureFibreTangentIso
import Mathlib.LinearAlgebra.Dimension.Constructions


/-!
# Dimension of the actual regular differential space

The polynomial coordinate equivalence makes global regular differentials
finite-dimensional. Summing the dimensions of the bounded polynomial
spaces and evaluating the residue floor sum gives `(q-1)(N-gcd(N,R))/2`.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)

/-- The actual global regular differential space of the prime-power Kummer field is finite-dimensional. -/
instance squareKummer_regularDifferentials_finiteDimensional :
    FiniteDimensional (SquareConstantField p s)
      (globalRegularDifferentials (SquareConstantField p s)
        (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r))) :=
  (squareKummerRegularDifferentialEquiv p s c d r).finiteDimensional

/-- The dimension of actual regular differentials is the sum of the character degree cutoffs. -/
theorem squareKummer_regularDifferential_finrank_sum :
    Module.finrank (SquareConstantField p s)
      (globalRegularDifferentials (SquareConstantField p s)
        (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r))) =
      ∑ i : Fin (p ^ (s + 1) + 1), kummerDifferentialCutoff p s d r i.val := by
  rw [← (squareKummerRegularDifferentialEquiv p s c d r).finrank_eq]
  change Module.finrank (SquareConstantField p s)
    ((i : Fin (p ^ (s + 1) + 1)) →
      degreeLT (SquareConstantField p s) (kummerDifferentialCutoff p s d r i.val)) = _
  rw [Module.finrank_pi_fintype]
  simp only [GaloisForLFunctions.HTGeometry.finrank_degreeLT]

/-- Twice the dimension of actual regular differentials is the explicit ramification defect. -/
theorem squareKummer_regularDifferential_finrank_twice :
    2 * Module.finrank (SquareConstantField p s)
      (globalRegularDifferentials (SquareConstantField p s)
        (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r))) =
      (p ^ (d + 1) - 1) *
        (p ^ (s + 1) + 1 - Nat.gcd (p ^ (s + 1) + 1) (kummerExponent (p ^ (d + 1)) r)) := by
  rw [squareKummer_regularDifferential_finrank_sum, Fin.sum_univ_eq_sum_range]
  exact kummerDifferentialCutoff_sum_twice p s d r

/-- The genus, measured by the actual global regular differential dimension, has the Kummer formula. -/
theorem squareKummer_regularDifferential_finrank :
    Module.finrank (SquareConstantField p s)
      (globalRegularDifferentials (SquareConstantField p s)
        (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r))) =
      ((p ^ (d + 1) - 1) *
        (p ^ (s + 1) + 1 - Nat.gcd (p ^ (s + 1) + 1) (kummerExponent (p ^ (d + 1)) r))) / 2 := by
  have h := squareKummer_regularDifferential_finrank_twice p s c d r
  omega

/-- The regular differential space vanishes exactly when the covering degree divides the branch exponent. -/
theorem squareKummer_regularDifferential_finrank_eq_zero_iff :
    Module.finrank (SquareConstantField p s)
      (globalRegularDifferentials (SquareConstantField p s)
        (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r))) = 0 ↔
      p ^ (s + 1) + 1 ∣ kummerExponent (p ^ (d + 1)) r := by
  have h := squareKummer_regularDifferential_finrank_twice p s c d r
  have hq : 2 ≤ p ^ (d + 1) :=
    Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  have hm : p ^ (d + 1) - 1 ≠ 0 := by omega
  constructor
  · intro hz
    rw [hz, mul_zero] at h
    have hsub := (mul_eq_zero.mp h.symm).resolve_left hm
    have hg : Nat.gcd (p ^ (s + 1) + 1) (kummerExponent (p ^ (d + 1)) r) =
        p ^ (s + 1) + 1 :=
      le_antisymm (Nat.le_of_dvd (Nat.succ_pos _) (Nat.gcd_dvd_left _ _))
        (Nat.sub_eq_zero_iff_le.mp hsub)
    have hd := Nat.gcd_dvd_right (p ^ (s + 1) + 1) (kummerExponent (p ^ (d + 1)) r)
    rwa [hg] at hd
  · intro hd
    rw [Nat.gcd_eq_left hd, Nat.sub_self, mul_zero] at h
    omega

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
