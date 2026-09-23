import GaloisForLFunctions.HilbertMetric.LamzouriFiniteMultiplicity
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianXiDivisorContour

/-!
# Lamzouri diagonal bounds on genuine finite zeta-zero windows

The corpus already constructs a finite support of distinct nontrivial zeta
zeros and assigns each point its genuine analytic multiplicity.  Applying the
finite multiplicity inequalities to that support gives unconditional finite
versions of Montgomery's simple-zero bound and Lamzouri's distinct-point
bound.  No pair-correlation asymptotic is used here: the energy is exactly the
diagonal collision term `sum m(rho)^(2 : ℕ)`.
-/

open Finset
open scoped BigOperators

namespace RiemannGaussian

open GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Total analytic multiplicity in the symmetric finite zeta-zero window. -/
def zetaWindowMultiplicityMass (T : ℝ) : ℝ :=
  finiteMultiplicityMass
    (spectralZetaZeroWindow T) analyticZetaZeroMultiplicity

/-- Diagonal collision energy `sum m(rho)^(2 : ℕ)` in the finite zeta-zero window. -/
def zetaWindowDiagonalCollisionMass (T : ℝ) : ℝ :=
  finiteMultiplicityCollisionMass
    (spectralZetaZeroWindow T) analyticZetaZeroMultiplicity

/-- Distinct zeta zeros in the window whose analytic multiplicity is one. -/
def zetaWindowSimpleSupport (T : ℝ) : Finset NontrivialZetaZero :=
  finiteSimpleMultiplicitySupport
    (spectralZetaZeroWindow T) analyticZetaZeroMultiplicity

/-- Montgomery's diagonal simple-zero inequality on the corpus's genuine
finite zeta divisor. -/
theorem zetaWindowSimpleSupport_lower (T : ℝ) :
    2 * zetaWindowMultiplicityMass T - zetaWindowDiagonalCollisionMass T ≤
      ((zetaWindowSimpleSupport T).card : ℝ) := by
  exact finiteSimpleMultiplicitySupport_lower
    (spectralZetaZeroWindow T) analyticZetaZeroMultiplicity

/-- Lamzouri's distinct-point expression is bounded by the number of distinct
zeta zeros in every finite window.  Positivity of analytic order discharges
the positive-support condition internally. -/
theorem zetaWindowDistinctSupport_lower (T : ℝ) :
    (3 / 2 : ℝ) * zetaWindowMultiplicityMass T -
        (1 / 2 : ℝ) * zetaWindowDiagonalCollisionMass T ≤
      ((spectralZetaZeroWindow T).card : ℝ) := by
  have h := finitePositiveMultiplicitySupport_lower
    (spectralZetaZeroWindow T) analyticZetaZeroMultiplicity
  have hs : finitePositiveMultiplicitySupport
      (spectralZetaZeroWindow T) analyticZetaZeroMultiplicity =
      spectralZetaZeroWindow T := by
    unfold finitePositiveMultiplicitySupport
    rw [Finset.filter_eq_self]
    intro rho _
    exact analyticZetaZeroMultiplicity_positive rho
  simpa only [zetaWindowMultiplicityMass,
    zetaWindowDiagonalCollisionMass, hs] using h

/-- Diagonal collision energy always dominates multiplicity mass in a genuine
finite zeta-zero window. -/
theorem zetaWindowMass_le_diagonalCollisionMass (T : ℝ) :
    zetaWindowMultiplicityMass T ≤ zetaWindowDiagonalCollisionMass T := by
  exact finiteMultiplicityMass_le_collisionMass
    (spectralZetaZeroWindow T) analyticZetaZeroMultiplicity

/-- All-real specialization of Lamzouri's simple-plus-real inequality, stated
for the finite zeta divisor with the real contribution replaced by total
multiplicity mass. -/
theorem zetaWindowSimpleSupport_add_mass_lower (T : ℝ) :
    3 * zetaWindowMultiplicityMass T - zetaWindowDiagonalCollisionMass T ≤
      ((zetaWindowSimpleSupport T).card : ℝ) +
        zetaWindowMultiplicityMass T := by
  exact finiteSimpleMultiplicitySupport_add_mass_lower
    (spectralZetaZeroWindow T) analyticZetaZeroMultiplicity

end

end RiemannGaussian
