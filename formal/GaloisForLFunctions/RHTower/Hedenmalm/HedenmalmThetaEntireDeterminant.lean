/-
# The entire regularized determinant of the theta source pencil

The corpus determinant `thetaFredholmDet` is the disc-local exponential representative
`exp(−∑_{n≥2} zⁿ/n·tr(Bⁿ))`, nowhere zero by construction.  Its analytic continuation to the whole
plane is the Hilbert–Carleman determinant, and *that* is the object whose divisor the card's
determinant clause is about.

Here the general construction is instantiated at the actual arithmetic source: `thetaEntireDet2`
is entire, equals `thetaFredholmDet` near the origin, takes the value one there, is the unique such
function, and each of its nonzero zeros is a reciprocal eigenvalue of the source inverse itself.

Main results:
* `thetaEntireDet2`, `differentiable_thetaEntireDet2`, `isRegularizedDet_thetaEntireDet2`.
* `thetaEntireDet2_eq_thetaFredholmDet` — the agreement near the origin.
* `exists_eigenvector_of_thetaEntireDet2_eq_zero` — its zeros are reciprocal eigenvalues.
-/
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaTrace
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantEigenvalueLimit

namespace RHTower

namespace HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry HilbertSchmidt MeasureTheory

/-- **The entire regularized determinant of the source pencil.** -/
noncomputable def thetaEntireDet2 : ℂ → ℂ := entireDet2 thetaKernelMatrix

theorem differentiable_thetaEntireDet2 : Differentiable ℂ thetaEntireDet2 :=
  differentiable_entireDet2 isHS_thetaKernelMatrix

theorem isRegularizedDet_thetaEntireDet2 :
    IsRegularizedDet thetaKernelMatrix thetaEntireDet2 :=
  isRegularizedDet_entireDet2 isHS_thetaKernelMatrix

theorem thetaEntireDet2_zero : thetaEntireDet2 0 = 1 :=
  isRegularizedDet_thetaEntireDet2.eq_one_at_zero

/-- **Uniqueness.**  Any entire function agreeing with the local determinant near the origin is
`thetaEntireDet2`. -/
theorem eq_thetaEntireDet2_of_isRegularizedDet {D : ℂ → ℂ}
    (hD : IsRegularizedDet thetaKernelMatrix D) : D = thetaEntireDet2 :=
  hD.unique isRegularizedDet_thetaEntireDet2

/-- The entire determinant agrees with the corpus disc-local determinant near the origin. -/
theorem thetaEntireDet2_eq_thetaFredholmDet :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ Metric.ball (0 : ℂ) r, thetaEntireDet2 z = thetaFredholmDet z := by
  obtain ⟨-, r, hr, -, he⟩ := isRegularizedDet_thetaEntireDet2
  exact ⟨r, hr, he⟩

/-- The represented operator of the kernel matrix is the coordinate model of the source
inverse. -/
theorem toOperator_thetaKernelMatrix :
    toOperator isHS_thetaKernelMatrix = thetaKernelMatrixOperator :=
  toOperator_matrixOf isHilbertSchmidt_thetaKernelMatrixOperator

/-- **A zero of the entire theta determinant is a reciprocal eigenvalue of the source inverse.**
The transport is through the coordinate isometry of the quantile space onto `ℓ²`. -/
theorem exists_eigenvector_of_thetaEntireDet2_eq_zero {z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (h : thetaEntireDet2 z₀ = 0) :
    ∃ f : Lp ℂ 2 unitIntervalMeasure, f ≠ 0 ∧ thetaKernelOperator f = z₀⁻¹ • f := by
  obtain ⟨w, hw0, hw⟩ :=
    exists_eigenvector_of_entireDet2_eq_zero isHS_thetaKernelMatrix hz₀ h
  rw [toOperator_thetaKernelMatrix] at hw
  refine ⟨thetaCoord.symm w, ?_, ?_⟩
  · intro hzero
    exact hw0 (by simpa using congrArg thetaCoord hzero)
  · have hcoord : thetaCoord (thetaKernelOperator (thetaCoord.symm w)) = z₀⁻¹ • w := by
      simpa [thetaKernelMatrixOperator] using hw
    have := congrArg thetaCoord.symm hcoord
    simpa [map_smul] using this

end HedenmalmThetaSource

end RHTower
