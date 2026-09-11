import GaloisForLFunctions.HTGeometry.KukolGlobalOrbitSlice
import GaloisForLFunctions.HTGeometry.KukolTubeSaturationCoordinates
import GaloisForLFunctions.HTGeometry.KukolNilpotentExponential

/-!
# Native analytic matrix orbits and future-tube saturation

The arbitrary-dimensional complex orbit theory specializes exactly to the
existing nilpotent three-by-three matrix exponential. Its complete invariants
classify simultaneous analytic matrix orbits on the whole nonzero-minus locus.
The two upper-half-plane inequalities characterize precisely which native
matrix orbits meet the future tube.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped BigOperators Matrix

/-- The regular coordinate chart maps to the corpus's existing three-component Lorentz matrices. -/
def kukolRegularMatrixVector (x : KukolRegularPoint Unit) : Fin 3 → ℂ :=
  ![(x.minus : ℂ),x.plus,x.transverse ()]

theorem kukolRegularMatrixVector_injective : Function.Injective kukolRegularMatrixVector := by
  intro x y h
  apply KukolRegularPoint.ext
  · apply Units.ext
    exact congrArg (fun v => v 0) h
  · exact congrArg (fun v => v 1) h
  · funext k
    cases k
    exact congrArg (fun v => v 2) h

/-- The chart covers precisely the complete nonzero-minus matrix locus. -/
theorem kukolRegularMatrixVector_range :
    Set.range kukolRegularMatrixVector = {v : Fin 3 → ℂ | v 0≠0} := by
  ext v
  constructor
  · rintro ⟨x,rfl⟩
    exact x.minus.ne_zero
  · intro hv
    refine ⟨⟨Units.mk0 (v 0) hv,v 1,fun _ => v 2⟩,?_⟩
    funext j
    fin_cases j <;> rfl

/-- The new arbitrary-dimensional action is exactly the old matrix action on this native chart. -/
theorem kukolRegularMatrixVector_action (u : ℂ) (x : KukolRegularPoint Unit) :
    kukolRegularMatrixVector (kukolRegularAction (fun _ => u) x) =
      (kukolUnipotentMatrix u).mulVec (kukolRegularMatrixVector x) := by
  ext j
  fin_cases j <;>
    simp [kukolRegularMatrixVector,kukolRegularAction,kukolUnipotentMatrix,
      Matrix.mulVec]
  all_goals ring

/-- The exact action is the analytic exponential already formalized in the corpus. -/
theorem kukolRegularMatrixVector_exp_action (u : ℂ) (x : KukolRegularPoint Unit) :
    kukolRegularMatrixVector (kukolRegularAction (fun _ => u) x) =
      (NormedSpace.exp (kukolNilpotentMatrix u)).mulVec (kukolRegularMatrixVector x) := by
  rw [kukolNilpotentMatrix_analytic_exp]
  exact kukolRegularMatrixVector_action u x

/-- The complete invariant tuple classifies simultaneous native analytic matrix-exponential orbits. -/
theorem kukolAnalyticDiagonal_orbit_iff {ι : Type*} (anchor : ι)
    (x y : ι → KukolRegularPoint Unit) :
    (∃ u : ℂ,∀ j,(NormedSpace.exp (kukolNilpotentMatrix u)).mulVec
      (kukolRegularMatrixVector (x j))=kukolRegularMatrixVector (y j)) ↔
      kukolDiagonalInvariants anchor x=kukolDiagonalInvariants anchor y := by
  constructor
  · rintro ⟨u,hu⟩
    apply (kukolDiagonal_orbit_iff anchor x y).mp
    refine ⟨fun _ => u,fun j => kukolRegularMatrixVector_injective ?_⟩
    rw [kukolRegularMatrixVector_exp_action]
    exact hu j
  · intro h
    obtain ⟨u,hu⟩ := (kukolDiagonal_orbit_iff anchor x y).mpr h
    refine ⟨u (),fun j => ?_⟩
    have he : (fun _ : Unit => u ())=u := by funext k; cases k; rfl
    rw [← kukolRegularMatrixVector_exp_action,he,hu j]

/-- Native imaginary coordinates and the arbitrary-dimensional future-tube definition agree exactly. -/
theorem kukolRegularMatrixVector_future_iff (x : KukolRegularPoint Unit) :
    kukolImaginaryCoordinates (kukolRegularMatrixVector x) ∈ kukolFuture ↔
      x ∈ kukolRegularFutureTube := by
  simp [kukolImaginaryCoordinates,kukolRegularMatrixVector,kukolFuture,kukolQuadratic,
    kukolRegularFutureTube,kukolRegularImaginaryMargin,Real.norm_eq_abs]

/-- Exact criterion for a native analytic matrix orbit to meet the future tube. -/
theorem kukolAnalyticMatrix_future_saturation_iff (x : KukolRegularPoint Unit) :
    (∃ u : ℂ,kukolImaginaryCoordinates
      ((NormedSpace.exp (kukolNilpotentMatrix u)).mulVec (kukolRegularMatrixVector x)) ∈ kukolFuture) ↔
      0 < (x.minus : ℂ).im ∧ 0 < (kukolRegularQuotientCoordinate x).im := by
  rw [← kukolRegularTubeSaturation_iff]
  constructor
  · rintro ⟨u,hu⟩
    refine ⟨fun _ => u,?_⟩
    rw [← kukolRegularMatrixVector_future_iff,kukolRegularMatrixVector_exp_action]
    exact hu
  · rintro ⟨u,hu⟩
    refine ⟨u (),?_⟩
    have he : (fun _ : Unit => u ())=u := by funext k; cases k; rfl
    rw [← kukolRegularMatrixVector_exp_action,he,kukolRegularMatrixVector_future_iff]
    exact hu

end GaloisForLFunctions.HTGeometry
