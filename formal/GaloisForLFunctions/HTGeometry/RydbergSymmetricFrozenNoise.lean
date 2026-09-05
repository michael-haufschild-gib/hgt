import Mathlib

/-!
# Symmetry-forced cancellation of frozen-noise response

The symmetric static-disorder mechanism used in arXiv:2608.29858 is isolated
from any particular Hamiltonian.  Pairing offsets `ε` and `-ε` projects an
arbitrary response onto its even part.  Consequently its linear response at the
origin vanishes, while its quadratic curvature survives unchanged.
-/

namespace HTGeometry

/-- Response averaged over an equally weighted frozen pair `ε, -ε`. -/
noncomputable def symmetricFrozenAverage (f : ℝ → ℝ) (ε : ℝ) : ℝ :=
  (f ε + f (-ε)) / 2

/-- Antisymmetric component removed by the frozen-pair average. -/
noncomputable def antisymmetricFrozenResponse (f : ℝ → ℝ) (ε : ℝ) : ℝ :=
  (f ε - f (-ε)) / 2

theorem response_eq_symmetric_add_antisymmetric (f : ℝ → ℝ) (ε : ℝ) :
    f ε = symmetricFrozenAverage f ε + antisymmetricFrozenResponse f ε := by
  unfold symmetricFrozenAverage antisymmetricFrozenResponse
  ring

theorem symmetricFrozenAverage_neg (f : ℝ → ℝ) (ε : ℝ) :
    symmetricFrozenAverage f (-ε) = symmetricFrozenAverage f ε := by
  unfold symmetricFrozenAverage
  rw [neg_neg]
  ring

theorem antisymmetricFrozenResponse_neg (f : ℝ → ℝ) (ε : ℝ) :
    antisymmetricFrozenResponse f (-ε) = -antisymmetricFrozenResponse f ε := by
  unfold antisymmetricFrozenResponse
  rw [neg_neg]
  ring

theorem symmetricFrozenAverage_antisymmetric_eq_zero (f : ℝ → ℝ) (ε : ℝ) :
    symmetricFrozenAverage (antisymmetricFrozenResponse f) ε = 0 := by
  rw [symmetricFrozenAverage, antisymmetricFrozenResponse_neg]
  ring

theorem antisymmetricFrozenResponse_symmetric_eq_zero (f : ℝ → ℝ) (ε : ℝ) :
    antisymmetricFrozenResponse (symmetricFrozenAverage f) ε = 0 := by
  rw [antisymmetricFrozenResponse, symmetricFrozenAverage_neg]
  ring

/-- Symmetric frozen disorder kills linear response at the symmetry point. -/
theorem symmetricFrozenAverage_deriv_zero (f : ℝ → ℝ) :
    deriv (symmetricFrozenAverage f) 0 = 0 := by
  let g := symmetricFrozenAverage f
  have heven : (fun ε : ℝ => g (-ε)) = g := by
    funext ε
    exact symmetricFrozenAverage_neg f ε
  have hcomp := deriv_comp_neg g 0
  rw [heven] at hcomp
  simp only [neg_zero] at hcomp
  linarith

/-- Even response packaged with its symmetry certificate. -/
structure RydbergEvenResponse where
  response : ℝ → ℝ
  reflection : ∀ ε, response (-ε) = response ε

namespace RydbergEvenResponse

theorem symmetricFrozenAverage_eq (R : RydbergEvenResponse) (ε : ℝ) :
    symmetricFrozenAverage R.response ε = R.response ε := by
  rw [symmetricFrozenAverage, R.reflection]
  ring

/-- Every certified even response has zero first-order susceptibility at the
symmetry point. -/
theorem deriv_zero (R : RydbergEvenResponse) : deriv R.response 0 = 0 := by
  have heq : symmetricFrozenAverage R.response = R.response := by
    funext ε
    exact R.symmetricFrozenAverage_eq ε
  have havg := symmetricFrozenAverage_deriv_zero R.response
  rwa [heq] at havg

end RydbergEvenResponse

/-- A globally differentiated response with certified curvature at zero. -/
structure RydbergTwiceDifferentiableResponse where
  response : ℝ → ℝ
  responseDerivative : ℝ → ℝ
  curvature : ℝ
  hasFirstDerivative : ∀ ε, HasDerivAt response (responseDerivative ε) ε
  hasCurvature : HasDerivAt responseDerivative curvature 0

namespace RydbergTwiceDifferentiableResponse

/-- Derivative of the symmetric frozen-pair response. -/
noncomputable def symmetricFrozenDerivative
    (R : RydbergTwiceDifferentiableResponse) (ε : ℝ) : ℝ :=
  (R.responseDerivative ε - R.responseDerivative (-ε)) / 2

theorem symmetricFrozenAverage_hasDerivAt
    (R : RydbergTwiceDifferentiableResponse) (ε : ℝ) :
    deriv (symmetricFrozenAverage R.response) ε = R.symmetricFrozenDerivative ε := by
  have hneg : HasDerivAt (fun x : ℝ => R.response (-x))
      (-R.responseDerivative (-ε)) ε := by
    simpa [Function.comp_def] using
      HasDerivAt.scomp (𝕜 := ℝ) ε (R.hasFirstDerivative (-ε)) (hasDerivAt_neg ε)
  unfold symmetricFrozenAverage symmetricFrozenDerivative
  exact ((R.hasFirstDerivative ε).add hneg).div_const (2 : ℝ) |>.deriv

theorem symmetricFrozenDerivative_zero (R : RydbergTwiceDifferentiableResponse) :
    R.symmetricFrozenDerivative 0 = 0 := by
  simp [symmetricFrozenDerivative]

/-- Symmetrization preserves second-order curvature exactly. -/
theorem symmetricFrozenDerivative_hasDerivAt_curvature
    (R : RydbergTwiceDifferentiableResponse) :
    deriv R.symmetricFrozenDerivative 0 = R.curvature := by
  have hout : HasDerivAt R.responseDerivative R.curvature (-(0 : ℝ)) := by
    simpa using R.hasCurvature
  have hneg : HasDerivAt (fun ε : ℝ => R.responseDerivative (-ε)) (-R.curvature) 0 := by
    simpa [Function.comp_def] using
      HasDerivAt.scomp (𝕜 := ℝ) (0 : ℝ) hout (hasDerivAt_neg (0 : ℝ))
  unfold symmetricFrozenDerivative
  calc
    deriv (fun ε : ℝ =>
        (R.responseDerivative ε - R.responseDerivative (-ε)) / 2) 0 =
        (R.curvature - -R.curvature) / 2 :=
      (R.hasCurvature.sub hneg).div_const (2 : ℝ) |>.deriv
    _ = R.curvature := by ring

theorem symmetricFrozenAverage_deriv_zero (R : RydbergTwiceDifferentiableResponse) :
    deriv (symmetricFrozenAverage R.response) 0 = 0 := by
  rw [R.symmetricFrozenAverage_hasDerivAt 0,
    R.symmetricFrozenDerivative_zero]

theorem symmetricFrozenAverage_secondDeriv_zero (R : RydbergTwiceDifferentiableResponse) :
    deriv R.symmetricFrozenDerivative 0 = R.curvature :=
  R.symmetricFrozenDerivative_hasDerivAt_curvature

end RydbergTwiceDifferentiableResponse

end HTGeometry
