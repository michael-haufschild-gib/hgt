import GaloisForLFunctions.RepresentationLifting.Differential.MonogenicDerivations
import GaloisForLFunctions.RepresentationLifting.Differential.TruncatedVectorFields
import GaloisForLFunctions.RepresentationLifting.TruncatedPolynomialAlgebra
import GaloisForLFunctions.RHTower.Deninger.DeningerPositiveCellDegreeZero

/-!
# Actual derivations of truncated polynomial algebras

The conormal classification gives exact root values and characteristic-sensitive descent of polynomial vector fields.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.RepresentationLifting.Differential
open _root_.HTGeometry.ConstraintRelativity
variable {K : Type*} [Field K]

/-- The different acts by multiplicity times the top root power, in every characteristic. -/
theorem truncated_different_mul (m : ℕ) (u : TruncatedPolynomialAlgebra K m) :
    rootDifferent (X ^ m : K[X]) * u =
      (m : K) • (truncatedRoot K m ^ (m - 1) * u) := by
  rw [rootDifferent, derivative_X_pow, map_mul, map_pow, AdjoinRoot.mk_X]
  change algebraMap K (TruncatedPolynomialAlgebra K m) (m : K) *
    truncatedRoot K m ^ (m - 1) * u = _
  rw [Algebra.smul_def, mul_assoc]

/-- An actual derivation has arbitrary root value in divisible characteristic; otherwise its root value lies in the root ideal. -/
theorem exists_truncated_derivation_root_iff (m : ℕ) (u : TruncatedPolynomialAlgebra K m) :
    (∃ D : Derivation K (TruncatedPolynomialAlgebra K m) (TruncatedPolynomialAlgebra K m),
      D (truncatedRoot K m) = u) ↔
      (m : K) = 0 ∨ ∃ w, truncatedRoot K m * w = u := by
  rw [show truncatedRoot K m = AdjoinRoot.root (X ^ m : K[X]) from rfl,
    exists_derivation_root_iff, truncated_different_mul]
  cases m with
  | zero => simp
  | succ n =>
    rw [smul_eq_zero]
    apply or_congr Iff.rfl
    have h := truncatedRoot_annihilator K 1 n
    rw [Nat.add_comm 1 n] at h
    simpa only [Nat.add_sub_cancel, pow_one, truncatedRoot] using h u

/-- The actual finite local algebra has its expected dimension over every field. -/
theorem finrank_truncatedPolynomialAlgebra (m : ℕ) :
    Module.finrank K (TruncatedPolynomialAlgebra K m) = m := by
  rw [(_root_.RHTower.deningerMonicQuotient_powerBasis (Polynomial.monic_X_pow m :
    (X ^ m : K[X]).Monic)).finrank]
  exact Polynomial.natDegree_X_pow (R := K) m

private theorem generator_divisibility_iff_preserves (m : ℕ) (g : K[X]) :
    X ^ m ∣ g * derivative (X ^ m) ↔ PreservesPowerIdeal m g := by
  constructor
  · rintro ⟨h, hh⟩ P ⟨q, rfl⟩
    refine ⟨h * q + g * derivative q, ?_⟩
    rw [derivative_mul, mul_add, ← mul_assoc, hh]
    ring
  · intro h
    exact h _ (dvd_refl _)

/-- Every ideal-preserving polynomial vector field gives an actual derivation of the fat point, and only those do. -/
theorem exists_truncated_vectorfield_derivation_iff (m : ℕ) (g : K[X]) :
    (∃ D : Derivation K (TruncatedPolynomialAlgebra K m) (TruncatedPolynomialAlgebra K m),
      D (truncatedRoot K m) = AdjoinRoot.mk (X ^ m) g) ↔
      (m : K) = 0 ∨ g.coeff 0 = 0 := by
  rw [show truncatedRoot K m = AdjoinRoot.root (X ^ m : K[X]) from rfl,
    exists_derivation_root_iff]
  change AdjoinRoot.mk (X ^ m) (derivative (X ^ m)) * AdjoinRoot.mk (X ^ m) g = 0 ↔ _
  rw [← map_mul, AdjoinRoot.mk_eq_zero, mul_comm (derivative _),
    generator_divisibility_iff_preserves, preservesPowerIdeal_iff]

/-- Ordinary differentiation exists on the actual quotient exactly at characteristic-divisible multiplicity. -/
theorem exists_truncated_derivation_root_one_iff (m : ℕ) :
    (∃ D : Derivation K (TruncatedPolynomialAlgebra K m) (TruncatedPolynomialAlgebra K m),
      D (truncatedRoot K m) = 1) ↔ (m : K) = 0 := by
  simpa using exists_truncated_vectorfield_derivation_iff m (1 : K[X])

/-- The Euler root value always extends to an actual derivation of the quotient algebra. -/
theorem exists_truncated_euler_derivation (m : ℕ) :
    ∃ D : Derivation K (TruncatedPolynomialAlgebra K m) (TruncatedPolynomialAlgebra K m),
      D (truncatedRoot K m) = truncatedRoot K m := by
  apply (exists_truncated_derivation_root_iff m _).mpr
  exact Or.inr ⟨1, mul_one _⟩

#print axioms exists_truncated_derivation_root_iff
#print axioms exists_truncated_vectorfield_derivation_iff
#print axioms exists_truncated_derivation_root_one_iff
#print axioms exists_truncated_euler_derivation
#print axioms finrank_truncatedPolynomialAlgebra
end GaloisForLFunctions.RepresentationLifting.Differential
