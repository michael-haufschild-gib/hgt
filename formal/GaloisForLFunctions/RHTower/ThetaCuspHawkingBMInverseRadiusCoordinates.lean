import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMIngoingCoordinates

/-! The actual inverse-radius coordinate differential and tensor pullback. -/

open GaloisForLFunctions.HTGeometry Filter Topology
namespace RHTower.D4BMModularCore
noncomputable section

/-- The actual inverse-radius coordinate change in the ingoing chart. -/
def inverseRadiusPoint (x : Fin 4 → ℝ) : Fin 4 → ℝ := ![x 0,(x 1)⁻¹,x 2,x 3]

/-- Its complete real differential. -/
def inverseRadiusDifferential (u : ℝ) : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0,
    (-u⁻¹^(2 : ℕ)) • ContinuousLinearMap.proj 1,ContinuousLinearMap.proj 2,ContinuousLinearMap.proj 3]

/-- The inverse-radius differential follows from the actual coordinate map. -/
theorem inverseRadiusPoint_hasFDerivAt (x : Fin 4 → ℝ) (hu : x 1 ≠ 0) :
    HasFDerivAt inverseRadiusPoint (inverseRadiusDifferential (x 1)) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasFDerivAt_apply 0 x
  · have h := HasDerivAt.comp_hasFDerivAt (𝕜 := ℝ) (𝕜' := ℝ)
      (f := fun z : Fin 4 → ℝ => z 1) x (hasDerivAt_inv hu) (hasFDerivAt_apply 1 x)
    convert! h using 1
    all_goals ext v
    all_goals simp
  · exact hasFDerivAt_apply 2 x
  · exact hasFDerivAt_apply 3 x

/-- Complexification of the full inverse-radius coordinate differential. -/
def inverseRadiusJacobian (u : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![1,-u⁻¹^(2 : ℕ),1,1]

/-- Every displayed matrix entry is the actual differentiated coordinate entry. -/
theorem inverseRadiusDifferential_matrix (u : ℝ) (i j : Fin 4) :
    ((inverseRadiusDifferential u (Pi.single j 1) i : ℝ) : ℂ) = inverseRadiusJacobian u i j := by
  fin_cases i <;> fin_cases j <;> simp [inverseRadiusDifferential,inverseRadiusJacobian]

/-- Tensor pullback retaining both inverse-radius differential factors. -/
def inverseRadiusPullback (u : ℂ) (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (inverseRadiusJacobian u).transpose*M*inverseRadiusJacobian u

end
end RHTower.D4BMModularCore
