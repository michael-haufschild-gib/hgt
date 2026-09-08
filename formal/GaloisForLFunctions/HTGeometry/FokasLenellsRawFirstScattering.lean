import GaloisForLFunctions.HTGeometry.FokasLenellsRawFirstCoefficient
import GaloisForLFunctions.HTGeometry.FokasLenellsRawScattering

/-!
# Cancellation of the actual first scattering coefficient

Both Jost endpoint matrices have the same first spectral derivative at
zero. Differentiating their exact determinant-one connection proves that
every entry of the original scattering matrix has zero first derivative.
This is a genuine coefficient of the constructed scattering data.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def rawFirstCoefficientMatrix (q : SchwartzMap ℝ ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0,-I*q 0;-I*q 0,0]

theorem rawAsymptoticMatrix_first_derivative_entry (q : SchwartzMap ℝ ℂ) (left : Bool) (i j : Fin 2) :
    HasDerivAt (fun k : ℝ => rawAsymptoticMatrix q k left i j) (rawFirstCoefficientMatrix q i j) 0 := by
  have h1 := rawAsymptoticVector_first_derivative q (1,0) left
  have h2 := rawAsymptoticVector_first_derivative q (0,1) left
  fin_cases i <;> fin_cases j
  · simpa [rawAsymptoticMatrix,rawFirstCoefficientMatrix,rawFirstCoefficient,Function.comp_def] using
      (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt 0 h1
  · simpa [rawAsymptoticMatrix,rawFirstCoefficientMatrix,rawFirstCoefficient,Function.comp_def] using
      (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt 0 h2
  · simpa [rawAsymptoticMatrix,rawFirstCoefficientMatrix,rawFirstCoefficient,Function.comp_def] using
      (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt 0 h1
  · simpa [rawAsymptoticMatrix,rawFirstCoefficientMatrix,rawFirstCoefficient,Function.comp_def] using
      (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt 0 h2

theorem rawAsymptoticMatrix_inverse_eq (q : SchwartzMap ℝ ℂ) (k : ℝ) (left : Bool) :
    (rawAsymptoticMatrix q k left)⁻¹ =
      !![rawAsymptoticMatrix q k left 1 1,-rawAsymptoticMatrix q k left 0 1;
        -rawAsymptoticMatrix q k left 1 0,rawAsymptoticMatrix q k left 0 0] := by
  rw [Matrix.inv_def,rawAsymptoticMatrix_det]
  simp only [Ring.inverse_one,one_smul,Matrix.adjugate_fin_two]

theorem rawAsymptoticMatrix_inverse_first_derivative_entry (q : SchwartzMap ℝ ℂ) (left : Bool) (i j : Fin 2) :
    HasDerivAt (fun k : ℝ => (rawAsymptoticMatrix q k left)⁻¹ i j) (-rawFirstCoefficientMatrix q i j) 0 := by
  simp only [rawAsymptoticMatrix_inverse_eq]
  fin_cases i <;> fin_cases j
  · simpa [rawFirstCoefficientMatrix] using rawAsymptoticMatrix_first_derivative_entry q left 1 1
  · convert! (rawAsymptoticMatrix_first_derivative_entry q left 0 1).neg using 1
  · convert! (rawAsymptoticMatrix_first_derivative_entry q left 1 0).neg using 1
  · simpa [rawFirstCoefficientMatrix] using rawAsymptoticMatrix_first_derivative_entry q left 0 0

/-- The original scattering matrix has no linear spectral term, for arbitrary Schwartz data. -/
theorem rawScatteringMatrix_first_derivative_entry (q : SchwartzMap ℝ ℂ) (i j : Fin 2) :
    HasDerivAt (fun k : ℝ => rawScatteringMatrix q k i j) 0 0 := by
  have h0 := (rawAsymptoticMatrix_first_derivative_entry q false i 0).mul
    (rawAsymptoticMatrix_inverse_first_derivative_entry q true 0 j)
  have h1 := (rawAsymptoticMatrix_first_derivative_entry q false i 1).mul
    (rawAsymptoticMatrix_inverse_first_derivative_entry q true 1 j)
  convert! h0.add h1 using 1
  · funext k
    simp only [rawScatteringMatrix,Matrix.mul_apply,Fin.sum_univ_two]
    rfl
  · simp only [rawAsymptoticMatrix_zero_frequency,inv_one]
    fin_cases i <;> fin_cases j <;> simp [rawFirstCoefficientMatrix,Matrix.one_apply]

theorem rawScatteringMatrix_hasDerivAt_zero (q : SchwartzMap ℝ ℂ) :
    HasDerivAt (rawScatteringMatrix q) 0 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact rawScatteringMatrix_first_derivative_entry q i j

theorem continuousAt_rawScatteringMatrix_zero (q : SchwartzMap ℝ ℂ) :
    ContinuousAt (rawScatteringMatrix q) 0 := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  exact (rawScatteringMatrix_first_derivative_entry q i j).continuousAt

theorem rawScatteringMatrix_tendsto_zero (q : SchwartzMap ℝ ℂ) :
    Tendsto (rawScatteringMatrix q) (𝓝 0) (𝓝 1) := by
  simpa only [rawScatteringMatrix_zero_frequency] using (continuousAt_rawScatteringMatrix_zero q).tendsto

end
end GaloisForLFunctions.HTGeometry.FokasLenells
