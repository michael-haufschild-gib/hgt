import GaloisForLFunctions.HTGeometry.HaferkampBlockFlattenedRank
import GaloisForLFunctions.HTGeometry.HaferkampFlattenedTerminalPhaseCurves

/-!
# Independent physical tangents of flattened terminal phase curves

The recursive BLC construction now supplies literal real `SU(4)` curves for
all retained terminal coordinates.  Their entrywise tangents are the algebraic
coordinate outputs used in Appendix B, multiplied by the common nonzero
complex scalar `i`; they therefore remain linearly independent.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace BackwardsLightCone

/-- The complex-linear map determined by the explicitly realized terminal
curve tangents.  Once the simultaneous real chart is differentiated, this is
the corresponding selected-coordinate restriction of its Jacobian. -/
def TerminalBlockPrefixAssembly.terminalCoordinateTangentMap
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) :
    (Fin labels.length → ℂ) →ₗ[ℂ]
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ where
  toFun := fun x => ∑ i, x i • (Complex.I •
    haferkampUnitaryListCoordinateOutput assembly.liftedWord
      (assembly.terminalIndices i)
      (finitePauliMatrix (Function.update (fun _ => none) root (some 2))))
  map_add' := by
    intro x y
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change (c * x i) • (Complex.I •
      haferkampUnitaryListCoordinateOutput assembly.liftedWord
        (assembly.terminalIndices i)
        (finitePauliMatrix (Function.update (fun _ => none) root (some 2)))) =
      c • (x i • (Complex.I •
        haferkampUnitaryListCoordinateOutput assembly.liftedWord
          (assembly.terminalIndices i)
          (finitePauliMatrix (Function.update (fun _ => none) root (some 2)))))
    rw [mul_smul]

/-- The explicitly physical flattened terminal phase curves have linearly
independent entrywise tangents at the assembled circuit point. -/
theorem TerminalBlockPrefixAssembly.linearIndependent_terminalCoordinateCurveTangents
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone 1 labels)
    (hlabels : LinearIndependent ℂ (fun i : Fin labels.length =>
      finitePauliMatrix (labels.get i))) :
    LinearIndependent ℂ (fun i =>
      Complex.I • haferkampUnitaryListCoordinateOutput assembly.liftedWord
        (assembly.terminalIndices i)
        (finitePauliMatrix (Function.update (fun _ => none) root (some 2)))) ∧
    ∀ i, EntrywiseMatrixHasDerivAt (assembly.terminalCoordinateCurve i)
      (Complex.I • haferkampUnitaryListCoordinateOutput assembly.liftedWord
        (assembly.terminalIndices i)
        (finitePauliMatrix (Function.update (fun _ => none) root (some 2)))) 0 := by
  refine ⟨?_, fun i => assembly.entrywiseHasDerivAt_terminalCoordinateCurve i⟩
  exact linearIndependent_smul_of_ne_zero _
    (assembly.linearIndependent_terminalCoordinateOutputs hlabels)
    (fun _ => Complex.I) (fun _ => Complex.I_ne_zero)

/-- The selected tangent map has complex range dimension at least the number
of fresh terminal directions. -/
theorem TerminalBlockPrefixAssembly.finrank_range_ge_terminalCoordinateTangents
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone 1 labels)
    (hlabels : LinearIndependent ℂ (fun i : Fin labels.length =>
      finitePauliMatrix (labels.get i))) :
    labels.length ≤ Module.finrank ℂ assembly.terminalCoordinateTangentMap.range := by
  apply finrank_range_ge_of_linearIndependent_images
    assembly.terminalCoordinateTangentMap (fun i => Pi.single i 1)
  have htangents := (assembly.linearIndependent_terminalCoordinateCurveTangents hlabels).1
  have hsingle (i : Fin labels.length) :
      assembly.terminalCoordinateTangentMap (Pi.single i 1) =
        Complex.I • haferkampUnitaryListCoordinateOutput assembly.liftedWord
          (assembly.terminalIndices i)
          (finitePauliMatrix (Function.update (fun _ => none) root (some 2))) := by
    simp [terminalCoordinateTangentMap]
  simpa only [hsingle] using htangents

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
