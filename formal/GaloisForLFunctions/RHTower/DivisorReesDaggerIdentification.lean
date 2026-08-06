import GaloisForLFunctions.RHTower.DivisorReesGradedMetric
import GaloisForLFunctions.RHTower.BurnolCoPoissonConormalReflectionCover
import GaloisForLFunctions.RHTower.CanonicalBranch
import GaloisForLFunctions.RHTower.Reflection

/-!
# The reflected dagger acts trivially on the graded symbol

The co-Poisson conormal reflection is the functional-equation involution `rho ↦ 1 - conj rho`, which
is exactly reflection across the critical line.  The analytic order of the completed zeta function
is invariant under it, because the functional equation and the Schwarz reality pairing compose.

The graded Rees symbol at a divisor point depends on that point only through its multiplicity.  So
the reflection leaves the graded symbol, its Kraus vector, its metric constant and its contraction
defect all unchanged: the graded correspondence carries the reflected dagger for free.
-/

open Complex

namespace RHTower

noncomputable section

/-! ### The co-Poisson reflection is the critical-line reflection -/

theorem burnolCoPoissonConormalReflection_eq_lineReflection (rho : ℂ) :
    burnolCoPoissonConormalReflection rho = lineReflection (1 / 2) rho := by
  rw [burnolCoPoissonConormalReflection, lineReflection_half]

/-! ### The divisor multiplicity is reflection-invariant -/

/-- **The completed-Xi order is invariant under the co-Poisson conormal reflection.** -/
theorem xi_analyticOrderAt_burnolCoPoissonConormalReflection (rho : ℂ) :
    analyticOrderAt xi (burnolCoPoissonConormalReflection rho) = analyticOrderAt xi rho := by
  rw [burnolCoPoissonConormalReflection, xi_orderAt_one_sub, xi_orderAt_conj]

/-- The multiplicity used by the graded Rees symbol is reflection-invariant. -/
theorem xi_multiplicity_burnolCoPoissonConormalReflection (rho : ℂ) :
    (analyticOrderAt xi (burnolCoPoissonConormalReflection rho)).toNat
      = (analyticOrderAt xi rho).toNat := by
  rw [xi_analyticOrderAt_burnolCoPoissonConormalReflection]

/-! ### The graded symbol carries the reflected dagger -/

/-- The graded Rees symbol attached to a spectral point: the graded Gram of its own
multiplicity. -/
def xiGradedSymbol (rho : ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  divisorReesGram (gradedDivisorOverlap (analyticOrderAt xi rho).toNat t)
    (gradedDivisorFisherNumerator (analyticOrderAt xi rho).toNat t)
    (((analyticOrderAt xi rho).toNat : ℝ) ^ 2)

/-- **The reflected dagger acts trivially on the graded symbol.**  Reflecting the spectral point
across the critical line leaves the graded Rees symbol unchanged, because the symbol sees the point
only through a multiplicity and that multiplicity is reflection-invariant. -/
theorem xiGradedSymbol_burnolCoPoissonConormalReflection (rho : ℂ) (t : ℝ) :
    xiGradedSymbol (burnolCoPoissonConormalReflection rho) t = xiGradedSymbol rho t := by
  rw [xiGradedSymbol, xiGradedSymbol, xi_multiplicity_burnolCoPoissonConormalReflection]

/-- The graded symbol at a spectral point is the outer square of its own Kraus vector. -/
theorem xiGradedSymbol_eq_vecMulVec (rho : ℂ) {t : ℝ} (ht : t ≠ 0) :
    xiGradedSymbol rho t
      = Matrix.vecMulVec ![1, ((analyticOrderAt xi rho).toNat : ℝ)]
          ![1, ((analyticOrderAt xi rho).toNat : ℝ)] :=
  gradedDivisorReesGram_eq_vecMulVec _ ht

/-- The graded symbol at a spectral point is positive semidefinite. -/
theorem xiGradedSymbol_posSemidef (rho : ℂ) {t : ℝ} (ht : t ≠ 0) :
    (xiGradedSymbol rho t).PosSemidef :=
  gradedDivisorReesGram_posSemidef _ ht

/-- **The reflected dagger preserves the contraction.**  The energy-normalized graded symbol is a
complete contraction at the reflected point with the very same energy constant. -/
theorem xiGradedSymbol_contraction_reflection (rho : ℂ) {t : ℝ} (ht : t ≠ 0) :
    (1 - (gradedDivisorEnergy (analyticOrderAt xi rho).toNat)⁻¹ •
      xiGradedSymbol (burnolCoPoissonConormalReflection rho) t).PosSemidef := by
  rw [xiGradedSymbol_burnolCoPoissonConormalReflection, xiGradedSymbol]
  exact gradedDivisorReesGram_contraction _ ht

end

end RHTower
