import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerAffineNormalizationDefect
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRegularDifferentialDimension
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.KummerExponentParity

/-!
# Normalization defect and intrinsic genus

For geometric-sum branch exponents, the affine normalization defect and the
actual regular-differential dimension satisfy an exact conservation identity.
Its genus bound is sharp precisely for normal affine orders. When the branch
prime power equals the covering degree minus one, exponent parity gives genus
zero or the constant value `Q*(Q-1)/2`.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s d : ℕ) (c : (SquareConstantField p s)ˣ) (r : ℕ)

private abbrev affineDefectModule (t : ℕ) :
    Module (SquareConstantField p s) (SquareKummerAffineDefect p s d c t) := inferInstance

attribute [local instance] affineDefectModule

/-- Genus as the dimension of differentials regular at every constant-field place. -/
abbrev squareKummerGeometricGenus : ℕ :=
  Module.finrank (SquareConstantField p s)
    (globalRegularDifferentials (SquareConstantField p s)
      (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)))

/-- Twice the affine defect plus twice the intrinsic genus equals the pole-degree expression. -/
theorem squareKummerAffineDefect_add_genus_twice :
    2 * (Module.finrank (SquareConstantField p s)
      (SquareKummerAffineDefect p s d c (kummerExponent (p ^ (d + 1)) r)) +
      squareKummerGeometricGenus p s d c r) =
        p ^ (s + 1) * ((p ^ (d + 1)) ^ r - 1) := by
  rw [squareKummerGeometricGenus, Nat.mul_add,
    squareKummer_regularDifferential_finrank_sum, Fin.sum_univ_eq_sum_range]
  exact squareKummerAffineDefect_add_cutoffs p s d c r

theorem squareKummerAffineDefect_add_genus :
    Module.finrank (SquareConstantField p s)
      (SquareKummerAffineDefect p s d c (kummerExponent (p ^ (d + 1)) r)) +
      squareKummerGeometricGenus p s d c r =
        (p ^ (s + 1) * ((p ^ (d + 1)) ^ r - 1)) / 2 := by
  have h := squareKummerAffineDefect_add_genus_twice p s d c r
  omega

theorem squareKummer_genus_twice_le_pole_degree :
    2 * squareKummerGeometricGenus p s d c r ≤
      p ^ (s + 1) * ((p ^ (d + 1)) ^ r - 1) := by
  have h := squareKummerAffineDefect_add_genus_twice p s d c r
  rw [Nat.mul_add] at h
  omega

/-- Equality in the pole-degree genus bound characterizes a normal affine order. -/
theorem squareKummer_genus_bound_eq_iff_normal :
    2 * squareKummerGeometricGenus p s d c r =
      p ^ (s + 1) * ((p ^ (d + 1)) ^ r - 1) ↔
    squareKummerAffineOrder p s d c (kummerExponent (p ^ (d + 1)) r) = ⊤ := by
  rw [squareKummerAffineOrder_eq_top_iff,
    ← squareKummerAffineDefect_finrank_eq_zero_iff p s d c]
  have h := squareKummerAffineDefect_add_genus_twice p s d c r
  rw [Nat.mul_add] at h
  omega

theorem squareKummer_zero_genus_defect_exact :
    squareKummerGeometricGenus p s d c r = 0 ↔
      2 * Module.finrank (SquareConstantField p s)
        (SquareKummerAffineDefect p s d c (kummerExponent (p ^ (d + 1)) r)) =
        p ^ (s + 1) * ((p ^ (d + 1)) ^ r - 1) := by
  have h := squareKummerAffineDefect_add_genus_twice p s d c r
  rw [Nat.mul_add] at h
  omega

#print axioms squareKummerAffineDefect_add_genus_twice
#print axioms squareKummer_genus_bound_eq_iff_normal

/-- Even geometric-sum length gives genus zero when the two prime powers agree. -/
theorem squareKummerGeometricGenus_even (n : ℕ) :
    squareKummerGeometricGenus p s s c (2 * n) = 0 := by
  rw [squareKummerGeometricGenus, squareKummer_regularDifferential_finrank,
    kummerExponent_even_gcd, Nat.sub_self, mul_zero, Nat.zero_div]

/-- Odd geometric-sum length gives a genus independent of that length. -/
theorem squareKummerGeometricGenus_odd (n : ℕ) :
    squareKummerGeometricGenus p s s c (2 * n + 1) =
      p ^ (s + 1) * (p ^ (s + 1) - 1) / 2 := by
  rw [squareKummerGeometricGenus, squareKummer_regularDifferential_finrank,
    kummerExponent_odd_gcd, Nat.add_sub_cancel, Nat.mul_comm]

#print axioms squareKummerGeometricGenus_even
#print axioms squareKummerGeometricGenus_odd
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
