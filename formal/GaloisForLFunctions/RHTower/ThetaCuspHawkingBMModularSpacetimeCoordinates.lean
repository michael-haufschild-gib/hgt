import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModularCoexact

/-! The original four-dimensional modular coordinate action and its complete differential. -/

open Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse D4BMMetricReconstruction
noncomputable section

/-- The angular complex coordinate of the actual four-dimensional chart. -/
def spacetimeAngular : (Fin 4 → ℝ) →L[ℝ] ℂ :=
  angularCoordinates.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![ContinuousLinearMap.proj 2,ContinuousLinearMap.proj 3])

private theorem spacetimeAngular_apply (x : Fin 4 → ℝ) :
    spacetimeAngular x = (x 2 : ℂ)+(x 3 : ℂ)*Complex.I := rfl

/-- A spacetime point with its original upper-half-plane angular coordinate. -/
def spacetimePoint (t r : ℝ) (z : UpperHalfPlane) : Fin 4 → ℝ := ![t,r,z.re,z.im]

private theorem spacetimeAngular_point (t r : ℝ) (z : UpperHalfPlane) :
    spacetimeAngular (spacetimePoint t r z) = (z:ℂ) := by
  change ((z:ℂ).re:ℂ)+((z:ℂ).im:ℂ)*Complex.I = (z:ℂ)
  exact (z:ℂ).re_add_im

/-- The original modular coordinate action, leaving time and radius fixed. -/
def modularSpacetimePoint (A : SL(2,ℤ)) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  let z := A • ofComplex (spacetimeAngular x)
  ![x 0,x 1,z.re,z.im]

/-- The full real differential of the original modular coordinate action. -/
def modularSpacetimeDifferential (A : SL(2,ℤ)) (z : UpperHalfPlane) :
    (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
  let D := (UpperHalfPlane.smulFDeriv (A : GL (Fin 2) ℝ) (z:ℂ)).comp spacetimeAngular
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0,ContinuousLinearMap.proj 1,
    Complex.reCLM.comp D,Complex.imCLM.comp D]

/-- The complexified Jacobian retains both real angular entries of the actual Mobius derivative. -/
def modularJacobian (A : SL(2,ℤ)) (z : UpperHalfPlane) : Matrix (Fin 4) (Fin 4) ℂ :=
  let c := 1/(denom A z)^(2 : ℕ)
  !![1,0,0,0; 0,1,0,0; 0,0,c.re,-c.im; 0,0,c.im,c.re]

/-- The actual modular action has exactly the displayed full coordinate differential. -/
theorem modularSpacetimePoint_hasFDerivAt (A : SL(2,ℤ)) (t r : ℝ) (z : UpperHalfPlane) :
    HasFDerivAt (modularSpacetimePoint A) (modularSpacetimeDifferential A z) (spacetimePoint t r z) := by
  have hz := spacetimeAngular_point t r z
  have hd := ((UpperHalfPlane.hasStrictFDerivAt_smul (A : GL (Fin 2) ℝ) z).hasFDerivAt)
  rw [← hz] at hd
  have hc := hd.comp (spacetimePoint t r z) spacetimeAngular.hasFDerivAt
  rw [hz] at hc
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasFDerivAt_apply 0 _
  · exact hasFDerivAt_apply 1 _
  · exact Complex.reCLM.hasFDerivAt.comp _ hc
  · exact Complex.imCLM.hasFDerivAt.comp _ hc

/-- Every complexified Jacobian entry is an actual differentiated coordinate entry. -/
theorem modularSpacetimeDifferential_matrix (A : SL(2,ℤ)) (z : UpperHalfPlane) (i j : Fin 4) :
    ((modularSpacetimeDifferential A z (Pi.single j 1) i : ℝ) : ℂ) = modularJacobian A z i j := by
  fin_cases i <;> fin_cases j <;>
    simp [modularSpacetimeDifferential,modularJacobian,spacetimeAngular_apply,
      modular_chart_jacobian]

/-- The full original coordinate map realizes the modular action on the angular point. -/
theorem modularSpacetimePoint_coordinates (A : SL(2,ℤ)) (t r : ℝ) (z : UpperHalfPlane) :
    modularSpacetimePoint A (spacetimePoint t r z) = spacetimePoint t r (A • z) := by
  unfold modularSpacetimePoint
  rw [spacetimeAngular_point,ofComplex_apply]
  rfl

/-- Both actual coordinate differential factors are retained in tensor pullback. -/
def modularTensorPullback (A : SL(2,ℤ)) (z : UpperHalfPlane) (M : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ := (modularJacobian A z).transpose*M*modularJacobian A z

end
end RHTower.D4BMModularCore
