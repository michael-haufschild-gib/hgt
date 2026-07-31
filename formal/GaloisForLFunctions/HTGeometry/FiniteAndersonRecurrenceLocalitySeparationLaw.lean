import GaloisForLFunctions.HTGeometry.FiniteAndersonProjectiveGenericityLaw
import GaloisForLFunctions.HTGeometry.FiniteAndersonObservationHorizonLocalityLaw

/-!
# Finite Anderson recurrence–locality separation

This file composes two independent properties of a finite tight-binding
Hamiltonian.  Every fixed Hermitian hopping matrix has a dense set of onsite
potentials with maximal projective rational rank.  Near the atomic limit,
every off-diagonal transition amplitude is uniformly small throughout any
prescribed finite observation horizon.  Density lets both properties hold
for the same nonzero-hopping Hamiltonian.

The conclusion is an exact separation theorem: finite-horizon spatial
transition suppression does not force arithmetic compression of the full
spectrum.  It is not an infinite-time dynamical-localization theorem and
does not assert that full spectral rank is visible to a local observer.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Onsite potentials giving maximal projective spectral rank after scaling
the fixed hopping matrix by `g`. -/
def scaledFiniteAndersonProjectiveMaximalSet
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.IsHermitian) (g : ℝ) :
    Set (Fin n → ℝ) :=
  finiteAndersonProjectiveMaximalSet ((g : ℂ) • T)
    (hT.smul (by rw [isSelfAdjoint_iff]; simp))

/-- Maximal projective onsite potentials remain dense at every hopping
strength, including arbitrarily small positive strengths. -/
theorem scaledFiniteAndersonProjectiveMaximalSet_dense
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.IsHermitian) (g : ℝ) :
    Dense (scaledFiniteAndersonProjectiveMaximalSet T hT g) := by
  exact
    (finiteAndersonProjectiveMaximalSet_dense_residual_fullMeasure
      ((g : ℂ) • T)
      (hT.smul (by rw [isSelfAdjoint_iff]; simp))).1

/-- The scaled-hopping convention used for finite-horizon evolution is
definitionally the fixed-hopping Anderson family evaluated at `gT`. -/
theorem scaledFiniteAndersonHamiltonian_eq
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (g : ℝ) (p : Fin n → ℝ) :
    scaledFiniteAndersonHamiltonian T g p =
      finiteAndersonHamiltonian ((g : ℂ) • T) p := rfl

/-- **Finite Anderson recurrence–locality separation law.** For every finite
Hermitian hopping matrix, reference onsite potential, finite observation
horizon, and positive transition tolerance, there is a positive hopping
strength and onsite potential such that:

1. the canonical spectrum has maximal projective rational rank; and
2. every off-diagonal site transition amplitude stays below the tolerance
   throughout the whole observation horizon.
-/
theorem exists_finiteAnderson_maximalProjective_finiteHorizonLocalized
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.IsHermitian) (p₀ : Fin n → ℝ) (H : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ, ∃ p : Fin n → ℝ,
      0 < g ∧
      p ∈ scaledFiniteAndersonProjectiveMaximalSet T hT g ∧
      FiniteHorizonOffDiagonalSmall T g p H ε := by
  exact exists_positive_dense_good_uniform_all_offDiagonal_small
    T p₀ H hε
    (scaledFiniteAndersonProjectiveMaximalSet T hT)
    (fun g _hg => scaledFiniteAndersonProjectiveMaximalSet_dense T hT g)

end

end GaloisForLFunctions.HTGeometry
