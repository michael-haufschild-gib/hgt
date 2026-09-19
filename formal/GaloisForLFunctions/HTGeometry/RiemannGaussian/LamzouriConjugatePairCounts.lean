import GaloisForLFunctions.HilbertMetric.LamzouriFiniteMultiplicity
import GaloisForLFunctions.HTGeometry.RiemannGaussian.SymmetricQuartetFiniteRoots

/-!
# Lamzouri bounds for finite conjugate-pair root packets

The finite-polynomial infrastructure represents off-axis roots by a multiset
of chosen upper roots together with their complex conjugates.  This module
proves that the resulting packet is conjugation-closed and applies the finite
multiplicity inequalities to its exact support and count function.

Repeated roots from the upper packet or collisions with conjugate roots are
retained by `Multiset.count`; the resulting collision mass therefore detects
both ordinary repeated roots and conjugation-axis collisions.
-/

open Finset
open scoped BigOperators ComplexConjugate

namespace RiemannGaussian

open GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Distinct support of a conjugate-pair root multiset. -/
def conjugatePairRootSupport (upper : Multiset ℂ) : Finset ℂ :=
  (conjugatePairRootMultiset upper).toFinset

/-- Exact multiplicity of a point in a conjugate-pair root multiset. -/
def conjugatePairRootMultiplicity (upper : Multiset ℂ) (z : ℂ) : ℕ :=
  (conjugatePairRootMultiset upper).count z

/-- Diagonal collision energy of a conjugate-pair root multiset. -/
def conjugatePairRootCollisionMass (upper : Multiset ℂ) : ℝ :=
  finiteMultiplicityCollisionMass (conjugatePairRootSupport upper)
    (conjugatePairRootMultiplicity upper)

/-- Distinct points occurring exactly once in a conjugate-pair packet. -/
def conjugatePairSimpleRootSupport (upper : Multiset ℂ) : Finset ℂ :=
  finiteSimpleMultiplicitySupport (conjugatePairRootSupport upper)
    (conjugatePairRootMultiplicity upper)

/-- Adding all complex conjugates makes the packet invariant under complex
conjugation, including multiplicities. -/
theorem conjugatePairRootMultiset_conj_closed (upper : Multiset ℂ) :
    (conjugatePairRootMultiset upper).map (starRingEnd ℂ) =
      conjugatePairRootMultiset upper := by
  simp [conjugatePairRootMultiset, Multiset.map_add, Multiset.map_map,
    add_comm]

/-- The exact multiplicity mass of the conjugate-pair packet is twice the
size of the chosen upper multiset. -/
theorem conjugatePairRootMultiplicityMass_eq (upper : Multiset ℂ) :
    finiteMultiplicityMass (conjugatePairRootSupport upper)
        (conjugatePairRootMultiplicity upper) =
      (2 * upper.card : ℕ) := by
  have hnat :
      (∑ z ∈ conjugatePairRootSupport upper,
          conjugatePairRootMultiplicity upper z) =
        (conjugatePairRootMultiset upper).card := by
    apply Multiset.sum_count_eq_card
    intro z hz
    exact Multiset.mem_toFinset.mpr hz
  unfold finiteMultiplicityMass
  rw [← Nat.cast_sum, hnat]
  simp [conjugatePairRootMultiset]
  ring

/-- Montgomery's simple-point inequality for the exact conjugate-pair root
packet. -/
theorem conjugatePairSimpleRootSupport_lower (upper : Multiset ℂ) :
    2 * (2 * upper.card : ℕ) - conjugatePairRootCollisionMass upper ≤
      ((conjugatePairSimpleRootSupport upper).card : ℝ) := by
  have h := finiteSimpleMultiplicitySupport_lower
    (conjugatePairRootSupport upper) (conjugatePairRootMultiplicity upper)
  rw [conjugatePairRootMultiplicityMass_eq] at h
  exact h

/-- Lamzouri's distinct-point expression for the exact conjugate-pair root
packet. -/
theorem conjugatePairDistinctRootSupport_lower (upper : Multiset ℂ) :
    (3 / 2 : ℝ) * (2 * upper.card : ℕ) -
        (1 / 2 : ℝ) * conjugatePairRootCollisionMass upper ≤
      ((conjugatePairRootSupport upper).card : ℝ) := by
  have h := finitePositiveMultiplicitySupport_lower
    (conjugatePairRootSupport upper) (conjugatePairRootMultiplicity upper)
  have hs : finitePositiveMultiplicitySupport
      (conjugatePairRootSupport upper) (conjugatePairRootMultiplicity upper) =
      conjugatePairRootSupport upper := by
    unfold finitePositiveMultiplicitySupport
    rw [Finset.filter_eq_self]
    intro z hz
    apply Multiset.count_pos.mpr
    exact Multiset.mem_toFinset.mp hz
  rw [hs, conjugatePairRootMultiplicityMass_eq] at h
  exact h

end

end RiemannGaussian
