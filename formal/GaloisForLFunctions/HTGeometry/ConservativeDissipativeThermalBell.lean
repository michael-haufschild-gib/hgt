import GaloisForLFunctions.HTGeometry.ConservativeDissipativeThermalTensorRelaxation
import GaloisForLFunctions.HTGeometry.BellEndpointCompleteBasis

/-!
# Thermal dynamics of the corpus's existing Bell basis

The composite conservative–dissipative channel motivated by arXiv:2609.04530 is
applied to the already formalized Bell endpoint-complete basis. Index transport
preserves the exact Bell amplitudes. Diagonal matrix units are proved positive,
normalized pure projectors; all Bell transition matrices have exact thermal
limits. Populations reach the product bath and off-diagonal coherences vanish.
Existing finite Bures data processing applies throughout this physical evolution.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder Kronecker
open Matrix Filter
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Transport the corpus's Boolean Bell coordinates to the four-dimensional quantum carrier. -/
def spinBellIndex : Bool × Bool ≃ Fin 4 :=
  (Equiv.prodCongr finTwoEquiv.symm finTwoEquiv.symm).trans finProdFinEquiv

/-- The existing Bell basis, transported without changing its amplitudes. -/
def spinBellMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ spinBellIndex bellMatrix

/-- Orthonormality is inherited from the corpus's proved Bell basis. -/
theorem spinBellMatrix_unitary : spinBellMatrixᴴ * spinBellMatrix = 1 := by
  unfold spinBellMatrix
  simp only [Matrix.coe_reindexAlgEquiv, Matrix.conjTranspose_reindex]
  change (Matrix.reindexAlgEquiv ℂ ℂ spinBellIndex) bellMatrixᴴ *
    (Matrix.reindexAlgEquiv ℂ ℂ spinBellIndex) bellMatrix = 1
  rw [← map_mul, bellMatrix_conjTranspose_mul, map_one]

/-- Bell-basis matrix units, including both pure densities and off-diagonal coherences. -/
def spinBellTransition (α β : Bool × Bool) : Matrix (Fin 4) (Fin 4) ℂ :=
  spinBellMatrix * Matrix.single (spinBellIndex α) (spinBellIndex β) 1 * spinBellMatrixᴴ

/-- Exact entrywise identification with the existing Bell vectors. -/
theorem spinBellTransition_entries (α β : Bool × Bool) (i j : Fin 4) :
    spinBellTransition α β i j =
      bellVector α (spinBellIndex.symm i) * conj (bellVector β (spinBellIndex.symm j)) := by
  simp [spinBellTransition, Matrix.mul_apply, Matrix.single, Matrix.conjTranspose_apply,
    spinBellMatrix, Matrix.reindex_apply, Matrix.submatrix_apply, bellMatrix, ite_and]

/-- Trace distinguishes diagonal Bell populations from off-diagonal Bell coherences. -/
theorem spinBellTransition_trace (α β : Bool × Bool) :
    Matrix.trace (spinBellTransition α β) = if α = β then 1 else 0 := by
  rw [spinBellTransition, Matrix.trace_mul_cycle, spinBellMatrix_unitary, Matrix.one_mul]
  by_cases h : α = β
  · subst β
    simp
  · have hne : spinBellIndex α ≠ spinBellIndex β := fun he => h (spinBellIndex.injective he)
    rw [Matrix.trace_single_eq_of_ne _ _ _ hne, if_neg h]

/-- Every diagonal Bell matrix unit is a constructed positive state. -/
theorem spinBellTransition_posSemidef (α : Bool × Bool) : (spinBellTransition α α).PosSemidef := by
  have hd := Matrix.posSemidef_conjTranspose_mul_self (Matrix.single (spinBellIndex α) (spinBellIndex α) (1 : ℂ))
  simp only [Matrix.conjTranspose_single, star_one, Matrix.single_mul_single_same, one_mul] at hd
  exact hd.mul_mul_conjTranspose_same spinBellMatrix

/-- The diagonal Bell carriers remain exact pure projectors before thermal evolution. -/
theorem spinBellTransition_sq (α : Bool × Bool) :
    spinBellTransition α α * spinBellTransition α α = spinBellTransition α α := by
  let D : Matrix (Fin 4) (Fin 4) ℂ := Matrix.single (spinBellIndex α) (spinBellIndex α) 1
  change (spinBellMatrix * D * spinBellMatrixᴴ) * (spinBellMatrix * D * spinBellMatrixᴴ) = spinBellMatrix * D * spinBellMatrixᴴ
  calc
    _ = spinBellMatrix * (D * (spinBellMatrixᴴ * spinBellMatrix) * D) * spinBellMatrixᴴ := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [spinBellMatrix_unitary, Matrix.mul_one]
      have hd : D * D = D := by simp [D]
      rw [hd]

/-- Every evolved Bell input is positive and normalized at every physical time. -/
theorem spinThermalTensorBell_state (a u b v : ℝ) (t : NNReal) (α : Bool × Bool) :
    ((spinThermalTensorChannel a u b v t).map (spinBellTransition α α)).PosSemidef ∧
      Matrix.trace ((spinThermalTensorChannel a u b v t).map (spinBellTransition α α)) = 1 := by
  constructor
  · exact (spinThermalTensorChannel a u b v t).positive (spinBellTransition_posSemidef α)
  · rw [(spinThermalTensorChannel a u b v t).tracePreserving, spinBellTransition_trace, if_pos rfl]

/-- All Bell-basis transition matrices have exact thermal limits: populations reach the bath, coherences vanish. -/
theorem spinThermalTensorBell_transition_tendsto (s u r v : ℝ) (α β : Bool × Bool) :
    Tendsto (fun t : NNReal => (spinThermalTensorChannel (Real.exp s) u (Real.exp r) v t).map (spinBellTransition α β))
      atTop (nhds (if α = β then spinThermalTensorBath u v else 0)) := by
  have h := spinThermalTensorChannel_tendsto_trace_bath s u r v (spinBellTransition α β)
  simpa only [spinBellTransition_trace, ite_smul, one_smul, zero_smul] using h

/-- Existing finite Bures data processing applies to the entire thermally evolved Bell family. -/
theorem spinThermalTensorBell_bures_progress (a u b v : ℝ) (s t : NNReal) (α β : Bool × Bool) :
    finiteBuresRootFidelity ((spinThermalTensorChannel a u b v t).map (spinBellTransition α α))
        ((spinThermalTensorChannel a u b v t).map (spinBellTransition β β)) ≤
      finiteBuresRootFidelity ((spinThermalTensorChannel a u b v (s + t)).map (spinBellTransition α α))
        ((spinThermalTensorChannel a u b v (s + t)).map (spinBellTransition β β)) := by
  have h := (spinThermalTensorKraus a u b v s).finiteBuresRootFidelity_le_evolve
    (spinThermalTensorBell_state a u b v t α).1 (spinThermalTensorBell_state a u b v t β).1
  rw [spinThermalTensorChannel_add]
  exact h

end
end GaloisForLFunctions.HTGeometry.SchafferExl
