import GaloisForLFunctions.HTGeometry.HolonomyCorankDichotomy
import GaloisForLFunctions.HTGeometry.ConstitutiveDoctrineMemoryWitnesses

/-!
# The boundary between analytic D-finiteness and finite difference-orbit corank

The exact algebraic G3 theorem identifies finite relation-lattice corank with finite shift-orbit
rank and constant-coefficient recurrence.  Standard analytic `D`-finiteness permits polynomial
coefficients, so it is strictly weaker.  The Gaussian germ `exp (z²)` supplies a closed witness: it
is `D`-finite of order one, but its response sequence has unbounded Hankel rank and hence infinite
relation-lattice corank.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open GaloisForLFunctions

/-- The Gaussian germ is analytically `D`-finite but has infinite response-orbit corank. -/
theorem dFinite_expSq_infinite_sequenceRelationCorank :
    DFiniteOn expSq (Set.univ : Set ℂ) ∧
      ¬ FiniteDimensional ℂ
        ((ℕ →₀ ℂ) ⧸ sequenceRelationLattice (respSeq expSq)) := by
  refine ⟨dFiniteOn_expSq, ?_⟩
  intro hfinite
  exact not_bddHankelRank_expSq
    ((seqConstantRecurrence_iff_bddHankelRank (respSeq expSq)).mp
      ((sequence_holonomy_corank_dichotomy (respSeq expSq)).mpr hfinite))

/-- Standard analytic `D`-finiteness does not imply finite difference-orbit corank. -/
theorem dFinite_does_not_imply_finite_sequenceRelationCorank :
    ¬ ∀ f : ℂ → ℂ, DFiniteOn f (Set.univ : Set ℂ) →
      FiniteDimensional ℂ ((ℕ →₀ ℂ) ⧸ sequenceRelationLattice (respSeq f)) := by
  intro h
  exact dFinite_expSq_infinite_sequenceRelationCorank.2
    (h expSq dFinite_expSq_infinite_sequenceRelationCorank.1)

end

end GaloisForLFunctions.HTGeometry
