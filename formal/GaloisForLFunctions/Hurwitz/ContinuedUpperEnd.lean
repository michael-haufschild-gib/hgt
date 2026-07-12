import GaloisForLFunctions.Hurwitz.AnalyticContinuation
import GaloisForLFunctions.Hurwitz.JointUpperEndDifferentialIndependence

/-!
# Analytically continued Hurwitz elements in the upper-end differential field

This file packages the Taylor-regularized continuation as a concrete analytic germ and then as an
element of the upper-end meromorphic differential field.  No restriction on the exponent is used.
-/

open Complex Polynomial

namespace HurwitzJointLadder

open HurwitzLadder HurwitzZetaContinuation GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open Filter Set Topology
open scoped Differential

noncomputable section

/-- The analytically continued Hurwitz function as an upper-end analytic germ. -/
def continuedHzetaUpperEndAnalytic (s : ℂ) : upperEndAnalyticSubring :=
  ⟨Germ.coeRingHom upperEndFilter (continuedHzeta s), continuedHzeta s, 0,
    by
      simpa [UHP, upperTail] using continuedHzeta_analyticOnNhd s,
    rfl⟩

/-- The genuine `n`th derivative of the continued Hurwitz function as an analytic germ. -/
def continuedHzetaUpperEndAnalyticJet (s : ℂ) (n : ℕ) : upperEndAnalyticSubring :=
  ⟨Germ.coeRingHom upperEndFilter (iteratedDeriv n (continuedHzeta s)),
    iteratedDeriv n (continuedHzeta s), 0,
    by
      simpa [UHP, upperTail] using
        analyticOnNhd_iteratedDeriv (continuedHzeta_analyticOnNhd s) n,
    rfl⟩

@[simp]
theorem continuedHzetaUpperEndAnalyticJet_zero (s : ℂ) :
    continuedHzetaUpperEndAnalyticJet s 0 = continuedHzetaUpperEndAnalytic s := by
  rfl

/-- Analytic-germ differentiation advances the continued Hurwitz jet. -/
theorem upperEndAnalyticDeriv_continuedHzetaJet (s : ℂ) (n : ℕ) :
    upperEndAnalyticDeriv (continuedHzetaUpperEndAnalyticJet s n) =
      continuedHzetaUpperEndAnalyticJet s (n + 1) := by
  apply Subtype.ext
  change (deriv (iteratedDeriv n (continuedHzeta s)) : Germ upperEndFilter ℂ) =
    (iteratedDeriv (n + 1) (continuedHzeta s) : Germ upperEndFilter ℂ)
  rw [iteratedDeriv_succ]

/-- The analytically continued Hurwitz function as an upper-end meromorphic-field element. -/
def continuedHzetaUpperEndMero (s : ℂ) : upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  exact algebraMap upperEndAnalyticSubring upperEndMeroField
    (continuedHzetaUpperEndAnalytic s)

/-- Differential-field jets of the continued element are its genuine analytic derivative germs. -/
theorem differentialJet_continuedHzetaUpperEndMero (s : ℂ) (n : ℕ) :
    letI := isDomain_upperEndAnalyticSubring
    letI := upperEndMeroFieldDifferential
    differentialJet n (continuedHzetaUpperEndMero s) =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (continuedHzetaUpperEndAnalyticJet s n) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI := upperEndMeroFieldDifferential
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show n + 1 = n + 1 by rfl, differentialJet_succ, ih,
        upperEndMeroFieldDifferential_algebraMap,
        upperEndAnalyticDeriv_continuedHzetaJet]

/-- In the convergence chamber, the continued analytic germ is the original series germ. -/
theorem continuedHzetaUpperEndAnalytic_eq_hzetaUpperEndAnalytic
    (s : ℂ) (hs : 1 < s.re) :
    continuedHzetaUpperEndAnalytic s = hzetaUpperEndAnalytic s hs := by
  apply Subtype.ext
  apply Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun a => continuedHzeta_eq_hzeta hs

/-- In the convergence chamber, the continued meromorphic element is the original Hurwitz
element. -/
theorem continuedHzetaUpperEndMero_eq_hzetaUpperEndMero
    (s : ℂ) (hs : 1 < s.re) :
    continuedHzetaUpperEndMero s = hzetaUpperEndMero s hs := by
  letI := isDomain_upperEndAnalyticSubring
  rw [continuedHzetaUpperEndMero, hzetaUpperEndMero,
    continuedHzetaUpperEndAnalytic_eq_hzetaUpperEndAnalytic s hs]

end

end HurwitzJointLadder
