/-
# The Kapustin Hilbert--Pólya endpoint

Kapustin's Krein-self-adjoint carrier contains the spectral point
`1 / (rho * (1-rho))` for every nontrivial xi zero `rho`.  A symmetric operator
on a genuine complex Hilbert space can have only conjugation-fixed eigenvalues.
The reciprocal Berry--Keating coordinate is conjugation-fixed, away from the
real-axis degeneracy, exactly on the critical line.  Consequently, any one
Hilbert-symmetric operator carrying all of Kapustin's xi-divisor eigenvalues
already implies RH.

This is an endpoint theorem, not a construction of the operator or its metric.
It formalizes why Hilbertizing the exact Kapustin point spectrum is the RH step
itself unless a separate source theorem produces the Hilbert structure.
-/

import GaloisForLFunctions.BerryKeating
import GaloisForLFunctions.RHTower.CentralReciprocalMoments
import Mathlib.Analysis.InnerProductSpace.Spectrum

open Module.End

namespace RHTower

noncomputable section

/-- A Hilbert-symmetric realization of one Kapustin spectral point forces its
non-real source point onto the critical line. -/
theorem critical_of_kapustinEigenvalue_of_symmetric
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (s : ℂ) (him : s.im ≠ 0)
    (heig : HasEigenvalue T (GaloisForLFunctions.kapustinEigenvalue s)) :
    s.re = 1 / 2 := by
  exact (GaloisForLFunctions.conj_kapustinEigenvalue_eq_iff s him).mp
    (hT.conj_eigenvalue_eq_self heig)

/-- If one Hilbert-symmetric operator contains the Kapustin spectral point of
every actual xi-divisor zero, then RH follows.  The hypothesis is exactly the
missing Hilbert--Pólya realization, not a weaker positivity premise. -/
theorem riemannHypothesis_of_kapustin_symmetric_pointSpectrum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hspec : ∀ ρ : ↥(MeromorphicOn.divisor xi Set.univ).support,
      HasEigenvalue T (GaloisForLFunctions.kapustinEigenvalue (ρ : ℂ))) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro s hs hzero
  let ρ : ↥(MeromorphicOn.divisor xi Set.univ).support :=
    ⟨s, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hline : s.re = 1 / 2 :=
    critical_of_kapustinEigenvalue_of_symmetric T hT s
      (xi_divisor_support_im_ne_zero ρ) (hspec ρ)
  exact (ne_of_gt hs) hline

end

end RHTower
