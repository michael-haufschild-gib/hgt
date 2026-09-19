import GaloisForLFunctions.HilbertMetric.LamzouriFiniteMultiplicity
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Roots

/-!
# Lamzouri collision bounds for split polynomial divisors

Over an algebraically closed field, the complete root multiset has total
multiplicity equal to degree.  Its squared multiplicity mass therefore gives
the same finite collision statistic as a zero divisor.
-/

open Finset Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions.HilbertMetric

noncomputable section

variable {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]

/-- Distinct roots of a polynomial over an algebraically closed field. -/
def algebraicallyClosedPolynomialRootSupport (p : K[X]) : Finset K :=
  p.roots.toFinset

/-- Root multiplicity read from the complete root multiset. -/
def algebraicallyClosedPolynomialRootMultiplicity (p : K[X]) (z : K) : ℕ :=
  p.roots.count z

/-- Squared-multiplicity collision mass of a split polynomial divisor. -/
def algebraicallyClosedPolynomialRootCollisionMass (p : K[X]) : ℝ :=
  finiteMultiplicityCollisionMass
    (algebraicallyClosedPolynomialRootSupport p)
    (algebraicallyClosedPolynomialRootMultiplicity p)

/-- Distinct roots occurring with multiplicity one. -/
def algebraicallyClosedPolynomialSimpleRootSupport (p : K[X]) : Finset K :=
  finiteSimpleMultiplicitySupport
    (algebraicallyClosedPolynomialRootSupport p)
    (algebraicallyClosedPolynomialRootMultiplicity p)

/-- Total root multiplicity equals polynomial degree. -/
theorem algebraicallyClosedPolynomialRootMultiplicityMass_eq (p : K[X]) :
    finiteMultiplicityMass (algebraicallyClosedPolynomialRootSupport p)
        (algebraicallyClosedPolynomialRootMultiplicity p) = p.natDegree := by
  have hnat :
      (∑ z ∈ algebraicallyClosedPolynomialRootSupport p,
          algebraicallyClosedPolynomialRootMultiplicity p z) = p.roots.card := by
    apply Multiset.sum_count_eq_card
    intro z hz
    exact Multiset.mem_toFinset.mpr hz
  unfold finiteMultiplicityMass
  rw [← Nat.cast_sum, hnat, IsAlgClosed.card_roots_eq_natDegree]

/-- Simple roots dominate twice degree minus root-collision energy. -/
theorem algebraicallyClosedPolynomialSimpleRootSupport_lower (p : K[X]) :
    2 * (p.natDegree : ℝ) -
        algebraicallyClosedPolynomialRootCollisionMass p ≤
      (algebraicallyClosedPolynomialSimpleRootSupport p).card := by
  have h := finiteSimpleMultiplicitySupport_lower
    (algebraicallyClosedPolynomialRootSupport p)
    (algebraicallyClosedPolynomialRootMultiplicity p)
  rw [algebraicallyClosedPolynomialRootMultiplicityMass_eq] at h
  exact h

/-- Distinct roots dominate the Lamzouri rank--trace expression. -/
theorem algebraicallyClosedPolynomialDistinctRootSupport_lower (p : K[X]) :
    (3 / 2 : ℝ) * (p.natDegree : ℝ) -
        (1 / 2 : ℝ) * algebraicallyClosedPolynomialRootCollisionMass p ≤
      (algebraicallyClosedPolynomialRootSupport p).card := by
  have h := finitePositiveMultiplicitySupport_lower
    (algebraicallyClosedPolynomialRootSupport p)
    (algebraicallyClosedPolynomialRootMultiplicity p)
  have hs : finitePositiveMultiplicitySupport
      (algebraicallyClosedPolynomialRootSupport p)
      (algebraicallyClosedPolynomialRootMultiplicity p) =
      algebraicallyClosedPolynomialRootSupport p := by
    unfold finitePositiveMultiplicitySupport
    rw [Finset.filter_eq_self]
    intro z hz
    exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hz)
  rw [hs, algebraicallyClosedPolynomialRootMultiplicityMass_eq] at h
  exact h

/-- Root-collision energy is bounded below by degree. -/
theorem algebraicallyClosedPolynomialRootDegree_le_collisionMass (p : K[X]) :
    (p.natDegree : ℝ) ≤ algebraicallyClosedPolynomialRootCollisionMass p := by
  rw [← algebraicallyClosedPolynomialRootMultiplicityMass_eq p]
  exact finiteMultiplicityMass_le_collisionMass
    (algebraicallyClosedPolynomialRootSupport p)
    (algebraicallyClosedPolynomialRootMultiplicity p)

end

end GaloisForLFunctions.HTGeometry
