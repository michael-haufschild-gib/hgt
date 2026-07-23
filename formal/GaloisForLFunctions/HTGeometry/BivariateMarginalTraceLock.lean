import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Bivariate marginal trace lock

A finite kernel on a product carrier has two canonical coordinate marginals, obtained by tracing
over either factor. Both marginals have exactly the same total trace. The law uses no positivity,
Hermitian symmetry, nondegeneracy, or index bound, so off-diagonal coupling cannot alter it.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- Jet-coordinate marginal of a finite bivariate kernel. -/
def bivariateJetMarginal
    {P J R : Type*} [Fintype P] [Fintype J] [AddCommMonoid R]
    (C : Matrix (P × J) (P × J) R) : Matrix J J R :=
  fun i j => ∑ p, C (p, i) (p, j)

/-- Source-coordinate marginal of a finite bivariate kernel. -/
def bivariateSourceMarginal
    {P J R : Type*} [Fintype P] [Fintype J] [AddCommMonoid R]
    (C : Matrix (P × J) (P × J) R) : Matrix P P R :=
  fun p q => ∑ i, C (p, i) (q, i)

/-- **Universal bivariate marginal trace lock.** Both coordinate marginals of every finite
bivariate kernel have the same total trace. -/
theorem trace_bivariateJetMarginal_eq_trace_bivariateSourceMarginal
    {P J R : Type*} [Fintype P] [Fintype J] [AddCommMonoid R]
    (C : Matrix (P × J) (P × J) R) :
    Matrix.trace (bivariateJetMarginal C) =
      Matrix.trace (bivariateSourceMarginal C) := by
  change (∑ i : J, ∑ p : P, C (p, i) (p, i)) =
    ∑ p : P, ∑ i : J, C (p, i) (p, i)
  rw [Finset.sum_comm]

end GaloisForLFunctions.HTGeometry
