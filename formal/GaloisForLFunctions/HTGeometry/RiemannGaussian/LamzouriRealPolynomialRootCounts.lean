import GaloisForLFunctions.HilbertMetric.LamzouriFiniteMultiplicity
import GaloisForLFunctions.HTGeometry.RiemannGaussian.FiniteRealRootDecomposition

/-!
# Lamzouri bounds for real-polynomial root divisors

The complete complex root multiset of a real polynomial is already proved
conjugation-invariant in the corpus.  Its diagonal count-square energy detects
algebraic root collisions, so Lamzouri's finite multiplicity inequalities give
unconditional simple-root and distinct-root bounds without separability.
-/

open Finset Polynomial
open scoped BigOperators

namespace RiemannGaussian

open GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Distinct complex roots of a real polynomial. -/
def realPolynomialRootSupport (A : ℝ[X]) : Finset ℂ :=
  (A.map Complex.ofRealHom).roots.toFinset

/-- Algebraic multiplicity in the complete complex root divisor. -/
def realPolynomialRootMultiplicity (A : ℝ[X]) (z : ℂ) : ℕ :=
  (A.map Complex.ofRealHom).roots.count z

/-- Diagonal collision energy of the complete complex root divisor. -/
def realPolynomialRootCollisionMass (A : ℝ[X]) : ℝ :=
  finiteMultiplicityCollisionMass (realPolynomialRootSupport A)
    (realPolynomialRootMultiplicity A)

/-- Distinct roots having algebraic multiplicity one. -/
def realPolynomialSimpleRootSupport (A : ℝ[X]) : Finset ℂ :=
  finiteSimpleMultiplicitySupport (realPolynomialRootSupport A)
    (realPolynomialRootMultiplicity A)

/-- Total root multiplicity is the polynomial degree. -/
theorem realPolynomialRootMultiplicityMass_eq (A : ℝ[X]) :
    finiteMultiplicityMass (realPolynomialRootSupport A)
        (realPolynomialRootMultiplicity A) = A.natDegree := by
  have hnat :
      (∑ z ∈ realPolynomialRootSupport A, realPolynomialRootMultiplicity A z) =
        (A.map Complex.ofRealHom).roots.card := by
    apply Multiset.sum_count_eq_card
    intro z hz
    exact Multiset.mem_toFinset.mpr hz
  unfold finiteMultiplicityMass
  rw [← Nat.cast_sum, hnat, IsAlgClosed.card_roots_eq_natDegree,
    Polynomial.natDegree_map_eq_of_injective Complex.ofRealHom.injective]

/-- Montgomery--Lamzouri simple-point inequality for a real polynomial. -/
theorem realPolynomialSimpleRootSupport_lower (A : ℝ[X]) :
    2 * (A.natDegree : ℝ) - realPolynomialRootCollisionMass A ≤
      ((realPolynomialSimpleRootSupport A).card : ℝ) := by
  have h := finiteSimpleMultiplicitySupport_lower
    (realPolynomialRootSupport A) (realPolynomialRootMultiplicity A)
  rw [realPolynomialRootMultiplicityMass_eq] at h
  exact h

/-- Lamzouri's distinct-point inequality for a real polynomial. -/
theorem realPolynomialDistinctRootSupport_lower (A : ℝ[X]) :
    (3 / 2 : ℝ) * (A.natDegree : ℝ) -
        (1 / 2 : ℝ) * realPolynomialRootCollisionMass A ≤
      ((realPolynomialRootSupport A).card : ℝ) := by
  have h := finitePositiveMultiplicitySupport_lower
    (realPolynomialRootSupport A) (realPolynomialRootMultiplicity A)
  have hs : finitePositiveMultiplicitySupport
      (realPolynomialRootSupport A) (realPolynomialRootMultiplicity A) =
      realPolynomialRootSupport A := by
    unfold finitePositiveMultiplicitySupport
    rw [Finset.filter_eq_self]
    intro z hz
    apply Multiset.count_pos.mpr
    exact Multiset.mem_toFinset.mp hz
  rw [hs, realPolynomialRootMultiplicityMass_eq] at h
  exact h

/-- Root-collision energy is always at least the polynomial degree. -/
theorem realPolynomialRootDegree_le_collisionMass (A : ℝ[X]) :
    (A.natDegree : ℝ) ≤ realPolynomialRootCollisionMass A := by
  rw [← realPolynomialRootMultiplicityMass_eq A]
  exact finiteMultiplicityMass_le_collisionMass
    (realPolynomialRootSupport A) (realPolynomialRootMultiplicity A)

end

end RiemannGaussian
