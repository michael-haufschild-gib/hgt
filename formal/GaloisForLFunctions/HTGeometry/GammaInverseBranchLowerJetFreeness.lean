import GaloisForLFunctions.HTGeometry.GammaInversePoleBranchCoefficientFreeness
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Inverse-Gamma pole branches are free from every finite lower-jet frame

The normalized inverse branches at the negative Gamma poles carry a countably algebraically
independent coefficient family in the pole-index germ ring.  In a composition-depth descent, the
other coordinates are the jets of the lower Gamma iterates; crucially, those coordinates do not
depend on the pole label.

This file proves the exact disjointness statement.  Adjoin an arbitrary type `κ` of formal
lower-jet coordinates to the pole-index germ ring.  The polynomial coordinates and every
inverse-branch coefficient remain one algebraically independent family over `ℂ`.  Thus no finite
polynomial cancellation can exchange a lower-depth jet for pole-label data.

The proof is scalar extension over a field: polynomial coordinates are algebraically independent
over the entire pole-index germ ring, and `AlgebraicIndependent.sumElim_comp` combines them with
the already-free inverse-branch coefficients.
-/

open MvPolynomial

namespace GaloisForLFunctions

noncomputable section

local instance gammaInverseBranchLowerJetNatGermAlgebra : Algebra ℂ NatGerm :=
  complexNatGerm.toAlgebra

/-- The coefficient ring obtained by adjoining a formal family of lower-iterate jets to the
pole-index germ ring. -/
abbrev GammaInverseBranchLowerJetRing (κ : Type*) := MvPolynomial κ NatGerm

/-- The combined coordinate family: formal lower jets followed by the normalized inverse-Gamma
pole-branch coefficients, embedded into one polynomial coefficient ring. -/
def lowerJetAndGammaInverseBranchCoefficientFamily (κ : Type*) :
    Sum κ ℕ → GammaInverseBranchLowerJetRing κ :=
  Sum.elim (fun k : κ => MvPolynomial.X k)
    (algebraMap NatGerm (GammaInverseBranchLowerJetRing κ) ∘
      gammaInversePoleBranchCoefficientGerm)

/-- **Pole/lower-depth disjointness.**  For every formal lower-jet frame, its coordinates together
with all normalized inverse-Gamma pole-branch coefficients are algebraically independent over
`ℂ`.  In particular, pole-index data cannot be absorbed by coefficients which are constant in the
pole label. -/
theorem algebraicIndependent_lowerJetAndGammaInverseBranchCoefficientFamily
    (κ : Type*) :
    AlgebraicIndependent ℂ
      (lowerJetAndGammaInverseBranchCoefficientFamily κ) := by
  exact algebraicIndependent_gammaInversePoleBranchCoefficientGerm.sumElim_comp
    (MvPolynomial.algebraicIndependent_X κ NatGerm)

/-- Every finite mixed polynomial in lower-jet variables and inverse-branch coefficients survives
the joint substitution.  This is the evaluation form consumed by a finite composition-depth
descent. -/
theorem aeval_lowerJetAndGammaInverseBranchCoefficientFamily_ne_zero
    {κ : Type*} {P : MvPolynomial (Sum κ ℕ) ℂ} (hP : P ≠ 0) :
    MvPolynomial.aeval
      (lowerJetAndGammaInverseBranchCoefficientFamily κ) P ≠ 0 := by
  exact (algebraicIndependent_iff_injective_aeval.mp
    (algebraicIndependent_lowerJetAndGammaInverseBranchCoefficientFamily κ))
      (by simpa using hP)

end

end GaloisForLFunctions
