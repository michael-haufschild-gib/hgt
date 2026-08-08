import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryQuadrature
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundarySourceJet
import GaloisForLFunctions.RHTower.XiShiftedReciprocalHankelTailCriterion

/-!
# Source realization of the shifted Xi boundary quadrature remainder

The first moment not fixed by a singular positive Hankel face is its degree-`2n+1`
positive-flat-quadrature remainder.  This file transports that remainder, without introducing any
zero-location hypothesis, to the completed prime--Gamma source.  On the Euler ray its positivity
is exactly one archimedean-versus-Chebyshev-discrepancy inequality.  In the endpoint convergence
window it also has a zero-free negative-binomial source formula.
-/

open scoped BigOperators
open Matrix Polynomial

namespace RHTower

noncomputable section

/-- Source-only version of the boundary jet, obtained from the convergent negative-binomial
transform of the fixed prime--Gamma moment tower. -/
def xiShiftedHankelBoundaryPrimeArchJet
    (y : ℝ) (n : ℕ) (c : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, c j * (primeArchShiftedReciprocalMoment y (n + (j : ℕ))).re

/-- **Quadrature/source identity.** The first positive-flat-quadrature remainder is exactly the
normalized completed-source boundary jet. -/
theorem xiShiftedHankelBoundaryQuadratureError_eq_sourceJet
    {w : ℝ} (hw : 0 < w) (n : ℕ) (c : Fin (n + 1) → ℝ) :
    xiShiftedHankelBoundaryQuadratureError (w ^ 2) c
        (X ^ (n + 1) * xiShiftedHankelNullPolynomial c) =
      xiShiftedHankelBoundarySourceJet w (n + 1) c := by
  rw [← xiShiftedHankelFirstOmittedCoupling_eq_boundaryQuadratureError]
  exact (xiShiftedHankelBoundarySourceJet_eq hw (n + 1) c).symm

/-- On the Euler ray, the first boundary quadrature remainder splits exactly into its
archimedean and cancellation-preserving prime-discrepancy parts. -/
theorem xiShiftedHankelBoundaryQuadratureError_eq_archimedean_add_discrepancy
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) (c : Fin (n + 1) → ℝ) :
    xiShiftedHankelBoundaryQuadratureError (w ^ 2) c
        (X ^ (n + 1) * xiShiftedHankelNullPolynomial c) =
      xiShiftedHankelBoundaryArchimedeanJet w (n + 1) c +
        xiShiftedHankelBoundaryDiscrepancyJet w (n + 1) c := by
  rw [xiShiftedHankelBoundaryQuadratureError_eq_sourceJet (by linarith : 0 < w),
    xiShiftedHankelBoundarySourceJet_eq_archimedean_add_discrepancy hw]

/-- **Exact source-side open core.** Positivity of the first extension coordinate is equivalent to
the archimedean boundary jet strictly dominating the negative prime-discrepancy jet. -/
theorem xiShiftedHankelBoundaryQuadratureError_pos_iff_sourceDominance
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) (c : Fin (n + 1) → ℝ) :
    0 < xiShiftedHankelBoundaryQuadratureError (w ^ 2) c
        (X ^ (n + 1) * xiShiftedHankelNullPolynomial c) ↔
      -xiShiftedHankelBoundaryDiscrepancyJet w (n + 1) c <
        xiShiftedHankelBoundaryArchimedeanJet w (n + 1) c := by
  rw [xiShiftedHankelBoundaryQuadratureError_eq_archimedean_add_discrepancy hw]
  constructor <;> intro h <;> linarith

/-- In the endpoint convergence window, the first boundary quadrature remainder is the source-only
negative-binomial prime--Gamma boundary jet. -/
theorem xiShiftedHankelBoundaryQuadratureError_eq_primeArchJet
    {y : ℝ} (hy : 0 ≤ y) (hymax : y < 41 / 2)
    (n : ℕ) (c : Fin (n + 1) → ℝ) :
    xiShiftedHankelBoundaryQuadratureError y c
        (X ^ (n + 1) * xiShiftedHankelNullPolynomial c) =
      xiShiftedHankelBoundaryPrimeArchJet y (n + 1) c := by
  rw [← xiShiftedHankelFirstOmittedCoupling_eq_boundaryQuadratureError]
  simp only [xiShiftedHankelFirstOmittedCoupling,
    GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling,
    xiShiftedHankelBoundaryPrimeArchJet]
  apply Finset.sum_congr rfl
  intro j hj
  rw [xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment hy hymax]

end

end RHTower
