import GaloisForLFunctions.HTGeometry.ConservativeDissipativeThermalTensor

/-!
# Thermalization of arbitrary composite quantum inputs

This application of the conservative–dissipative mechanism from arXiv:2609.04530
combines the closed local thermal limits with a complete tensor matrix-unit
expansion. Every raw composite matrix converges to its conserved trace times the
constructed product bath. Thus entangled initial inputs are included directly.
The same limit classifies all-time stationary matrices as exactly that trace ray.
Positive local rates are constructed exponentially from unrestricted coordinates.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder Kronecker
open Matrix Filter
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Every raw product input converges under constructed positive local rates. -/
theorem spinThermalTensorChannel_product_tendsto (s u r v : ℝ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    Tendsto (fun t : NNReal => (spinThermalTensorChannel (Real.exp s) u (Real.exp r) v t).map (finiteSpinTensorMatrix A B))
      atTop (nhds ((Matrix.trace A * Matrix.trace B) • spinThermalTensorBath u v)) := by
  have hA := spinThermalChannel_tendsto_trace_bath s u A
  have hB := spinThermalChannel_tendsto_trace_bath r v B
  have hh : finiteSpinTensorMatrix (Matrix.trace A • spinBathDensity u) (Matrix.trace B • spinBathDensity v) =
      (Matrix.trace A * Matrix.trace B) • spinThermalTensorBath u v := by
    rw [finiteSpinTensorMatrix_smul_left, finiteSpinTensorMatrix_smul_right, smul_smul]
    rfl
  rw [← hh]
  simp only [spinThermalTensorChannel_product]
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  let i' : Fin 2 × Fin 2 := finProdFinEquiv.symm i
  let j' : Fin 2 × Fin 2 := finProdFinEquiv.symm j
  change Tendsto (fun t : NNReal =>
      (spinThermalChannel (Real.exp s) u t).map A i'.1 j'.1 *
        (spinThermalChannel (Real.exp r) v t).map B i'.2 j'.2) atTop
      (nhds (((Matrix.trace A • spinBathDensity u) i'.1 j'.1) *
        ((Matrix.trace B • spinBathDensity v) i'.2 j'.2)))
  exact (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hA i'.1) j'.1).mul
    (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hB i'.2) j'.2)

set_option maxHeartbeats 1200000 in
/-- Matrix-unit expansion extends thermalization to every composite input, including entangled matrices. -/
theorem spinThermalTensorChannel_tendsto_trace_bath (s u r v : ℝ) (ρ : Matrix (Fin 4) (Fin 4) ℂ) :
    Tendsto (fun t : NNReal => (spinThermalTensorChannel (Real.exp s) u (Real.exp r) v t).map ρ)
      atTop (nhds (Matrix.trace ρ • spinThermalTensorBath u v)) := by
  let A (i j : Fin 2 × Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
    Matrix.single i.1 j.1 (ρ (finProdFinEquiv i) (finProdFinEquiv j))
  let B (i j : Fin 2 × Fin 2) : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single i.2 j.2 1
  have hexpand : ρ = ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2, finiteSpinTensorMatrix (A i j) (B i j) :=
    finiteSpinTensorMatrix_expansion (m := 2) (n := 2) ρ
  have htrace : (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2, Matrix.trace (A i j) * Matrix.trace (B i j)) = Matrix.trace ρ := by
    calc
      _ = Matrix.trace (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2, finiteSpinTensorMatrix (A i j) (B i j)) := by
        simp only [Matrix.trace_sum, finiteSpinTensorMatrix_trace]
      _ = Matrix.trace ρ := congrArg Matrix.trace hexpand.symm
  have hsum := tendsto_finsetSum (s := Finset.univ) (fun (i : Fin 2 × Fin 2) _ =>
    tendsto_finsetSum (s := Finset.univ) (fun (j : Fin 2 × Fin 2) _ =>
      spinThermalTensorChannel_product_tendsto s u r v (A i j) (B i j)))
  simp only [← Finset.sum_smul, htrace] at hsum
  have hmap (t : NNReal) : (spinThermalTensorChannel (Real.exp s) u (Real.exp r) v t).map ρ =
      ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        (spinThermalTensorChannel (Real.exp s) u (Real.exp r) v t).map (finiteSpinTensorMatrix (A i j) (B i j)) := by
    change spinThermalTensorLinear (Real.exp s) u (Real.exp r) v t ρ =
      ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        spinThermalTensorLinear (Real.exp s) u (Real.exp r) v t (finiteSpinTensorMatrix (A i j) (B i j))
    rw [hexpand]
    simp only [map_sum]
  apply hsum.congr'
  exact Filter.Eventually.of_forall (fun t => (hmap t).symm)

/-- Every constructed normalized product state reaches the actual product bath. -/
theorem spinThermalTensorChannel_pure_tendsto_bath (s u r v : ℝ) (z w : ℂ) :
    Tendsto (fun t : NNReal => (spinThermalTensorChannel (Real.exp s) u (Real.exp r) v t).map
      (finiteSpinTensorMatrix (spinChartDensity z) (spinChartDensity w)))
      atTop (nhds (spinThermalTensorBath u v)) := by
  have h := spinThermalTensorChannel_tendsto_trace_bath s u r v
    (finiteSpinTensorMatrix (spinChartDensity z) (spinChartDensity w))
  rw [(spinThermalTensor_pure_state z w).2, one_smul] at h
  exact h

/-- All-time stationarity is exactly the product-bath trace ray; no input-state assumptions are needed. -/
theorem spinThermalTensorChannel_stationary_iff (s u r v : ℝ) (ρ : Matrix (Fin 4) (Fin 4) ℂ) :
    (∀ t : NNReal, (spinThermalTensorChannel (Real.exp s) u (Real.exp r) v t).map ρ = ρ) ↔
      ρ = Matrix.trace ρ • spinThermalTensorBath u v := by
  constructor
  · intro h
    have hlim := spinThermalTensorChannel_tendsto_trace_bath s u r v ρ
    simp only [h] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  · intro h t
    calc
      _ = (spinThermalTensorChannel (Real.exp s) u (Real.exp r) v t).map (Matrix.trace ρ • spinThermalTensorBath u v) :=
        congrArg (spinThermalTensorChannel (Real.exp s) u (Real.exp r) v t).map h
      _ = Matrix.trace ρ • spinThermalTensorBath u v := by
        rw [(spinThermalTensorChannel (Real.exp s) u (Real.exp r) v t).map_smul, spinThermalTensorChannel_bath_fixed]
      _ = ρ := h.symm

end
end GaloisForLFunctions.HTGeometry.SchafferExl
