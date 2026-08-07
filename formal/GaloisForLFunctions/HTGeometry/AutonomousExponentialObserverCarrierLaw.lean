import GaloisForLFunctions.HTGeometry.ObserverCriticalCarrierConfinementLaw
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Autonomous exponential observer-carrier law

This module specializes observer critical-carrier confinement to autonomous
evolutions.  A coefficient vector is sent linearly into a real Banach algebra,
exponentiated once, and read by a linear reporter.  This includes ordinary
time-independent finite-dimensional Hamiltonian evolution after incorporating
the fixed time and the factor `-i` into the generator map.

The derivative at the zero Hamiltonian is exactly the reported generator map.
Thus one finite determinant at time zero controls all nonlinear exponential
fibres globally: the common critical locus is Gaussian-null, and every exact
adaptive target carrier off it has Hausdorff dimension at most parameter
dimension minus visible observer dimension.
-/

open MeasureTheory ProbabilityTheory Metric Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- An autonomous exponential endpoint: linear generator assembly, one
exponential, then a linear observer report. -/
def autonomousExponentialEndpoint
    {m v : ℕ} {A : Type*}
    [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (L : EuclideanSpace ℝ (Fin m) →L[ℝ] A)
    (R : A →L[ℝ] EuclideanSpace ℝ (Fin v))
    (x : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin v) :=
  ((R : A → EuclideanSpace ℝ (Fin v)) ∘ NormedSpace.exp ∘
    (L : EuclideanSpace ℝ (Fin m) → A)) x

/-- Autonomous exponential endpoints are globally real analytic. -/
theorem autonomousExponentialEndpoint_analyticOnNhd
    {m v : ℕ} {A : Type*}
    [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (L : EuclideanSpace ℝ (Fin m) →L[ℝ] A)
    (R : A →L[ℝ] EuclideanSpace ℝ (Fin v)) :
    AnalyticOnNhd ℝ (autonomousExponentialEndpoint L R) univ := by
  have hexp : AnalyticOnNhd ℝ (NormedSpace.exp : A → A) univ :=
    fun x _ => NormedSpace.exp_analytic x
  have hcomp := hexp.comp (L.analyticOnNhd univ) (mapsTo_univ _ _)
  change AnalyticOnNhd ℝ (fun x => R (NormedSpace.exp (L x))) univ
  simpa [Function.comp_def] using R.comp_analyticOnNhd hcomp

/-- The Fréchet derivative of the autonomous endpoint at zero is the reported
generator map, written first with the identity derivative of the exponential. -/
theorem autonomousExponentialEndpoint_hasFDerivAt_zero
    {m v : ℕ} {A : Type*}
    [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (L : EuclideanSpace ℝ (Fin m) →L[ℝ] A)
    (R : A →L[ℝ] EuclideanSpace ℝ (Fin v)) :
    HasFDerivAt (autonomousExponentialEndpoint L R)
      (R.comp ((1 : A →L[ℝ] A).comp L)) 0 := by
  have hExpL : HasFDerivAt
      ((NormedSpace.exp : A → A) ∘ (L : EuclideanSpace ℝ (Fin m) → A))
      ((1 : A →L[ℝ] A).comp L) 0 := by
    have hexp0 : HasFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) (L 0) := by
      simpa using (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A))
    exact hexp0.comp 0 L.hasFDerivAt
  exact R.hasFDerivAt.comp 0 hExpL

/-- The derivative at zero, simplified to composition of reporter and
generator maps. -/
theorem autonomousExponentialEndpoint_fderiv_zero
    {m v : ℕ} {A : Type*}
    [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (L : EuclideanSpace ℝ (Fin m) →L[ℝ] A)
    (R : A →L[ℝ] EuclideanSpace ℝ (Fin v)) :
    fderiv ℝ (autonomousExponentialEndpoint L R) 0 = R.comp L := by
  rw [(autonomousExponentialEndpoint_hasFDerivAt_zero L R).fderiv]
  ext x
  simp

/-- The finite visible-generator minor tested at zero. -/
def autonomousGeneratorMinor
    {m v : ℕ} {A : Type*}
    [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (L : EuclideanSpace ℝ (Fin m) →L[ℝ] A)
    (R : A →L[ℝ] EuclideanSpace ℝ (Fin v))
    (u : Fin v → EuclideanSpace ℝ (Fin m)) : Matrix (Fin v) (Fin v) ℝ :=
  fun i j => R (L (u j)) i

/-- **Autonomous universal exact-carrier law.**  If selected generator
directions span the reporter, then one target-independent Gaussian-null set
contains every critical coefficient.  For every target and every exact
adaptive carrier outside that set, Hausdorff dimension is at most `m - v`. -/
theorem autonomousExponential_universal_exactCarrierLaw
    {m v : ℕ} {A : Type*}
    [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (L : EuclideanSpace ℝ (Fin m) →L[ℝ] A)
    (R : A →L[ℝ] EuclideanSpace ℝ (Fin v))
    (u : Fin v → EuclideanSpace ℝ (Fin m))
    (hdet : (autonomousGeneratorMinor L R u).det ≠ 0) :
    stdGaussian (EuclideanSpace ℝ (Fin m))
        {x | ¬Function.Surjective
          (fderiv ℝ (autonomousExponentialEndpoint L R) x)} = 0 ∧
      ∀ (y : EuclideanSpace ℝ (Fin v))
        (M : Set (EuclideanSpace ℝ (Fin m))),
        M ⊆ {x | autonomousExponentialEndpoint L R x = y} ∩
          {x | Function.Surjective
            (fderiv ℝ (autonomousExponentialEndpoint L R) x)} →
        dimH M ≤ (m - v : ℕ) := by
  have hdet0 :
      (observerMinor
        (fun z => fderiv ℝ (autonomousExponentialEndpoint L R) z) u 0).det ≠ 0 := by
    have hminorEq :
        observerMinor
            (fun z => fderiv ℝ (autonomousExponentialEndpoint L R) z) u 0 =
          autonomousGeneratorMinor L R u := by
      ext i j
      simp only [observerMinor, autonomousGeneratorMinor]
      rw [autonomousExponentialEndpoint_fderiv_zero L R]
      rfl
    rw [hminorEq]
    exact hdet
  exact analytic_observer_universal_exactCarrierLaw
    (autonomousExponentialEndpoint_analyticOnNhd L R) u hdet0

end

end GaloisForLFunctions.HTGeometry
