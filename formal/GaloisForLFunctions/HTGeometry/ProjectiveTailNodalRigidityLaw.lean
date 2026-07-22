import GaloisForLFunctions.HTGeometry.OrientationNodalCollapse
import GaloisForLFunctions.HTGeometry.PrimeDirichletTailGroupoid

/-!
# Projective-tail nodal rigidity

A continuous deformation of signed real residue coordinates can change Boolean orientation only
by crossing coordinate zero walls.  Finite nodal support forces ordinary eventual equality, which
is stronger than equality modulo finite changes and global complement.  Consequently distinct
projective tail classes can be connected only through infinitely many nodal coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Topology

noncomputable section

/-- **Projective-tail nodal rigidity law.**  A continuous residue deformation between distinct
projective Boolean tail classes must cross infinitely many coordinate zero walls. -/
theorem residuePathNodalSupport_infinite_of_projectiveTailClass_ne
    (epsilon delta : ℕ → Bool) (w : ℕ → ℝ) (r : ℝ → ℕ → ℝ)
    (hw : ∀ p, 0 < w p)
    (hr0 : ∀ p, r 0 p = primeDirichletRealSign (epsilon p) * w p)
    (hr1 : ∀ p, r 1 p = primeDirichletRealSign (delta p) * w p)
    (hcontinuous : ∀ p, ContinuousOn (fun t => r t p) (Set.Icc (0 : ℝ) 1))
    (hclass : booleanProjectiveTailClass epsilon ≠ booleanProjectiveTailClass delta) :
    (residuePathNodalSupport r).Infinite := by
  intro hfinite
  have heventual : PrimeOrientationsEventuallyEqual epsilon delta :=
    primeOrientationsEventuallyEqual_of_finite_residuePathNodalSupport
      epsilon delta w r hw hr0 hr1 hcontinuous hfinite
  have htail : BooleanTailEquivalent epsilon delta :=
    (booleanTailEquivalent_iff_primeOrientationsEventuallyEqual epsilon delta).2 heventual
  apply hclass
  exact (booleanProjectiveTailClass_eq_iff epsilon delta).2 (Or.inl htail)

end

end GaloisForLFunctions.HTGeometry
