import GaloisForLFunctions.HTGeometry.FokasLenellsLeftJost

/-!
# Fokas–Lenells scattering amplitudes from constructed Jost bases

The two asymptotically normalized bases determine a scattering matrix for
every Schwartz potential and positive real spectral parameter. This file
proves the basis relation (2.59), both connection formulas (2.60), determinant
one (2.62), and the four Wronskian formulas (2.63)–(2.66) of Yan–Zhang–Zhu,
arXiv:2607.19649v1.

The scattering matrix is constructed from the potential. Position
independence, nondegeneracy and all inverses are proved, with no assumed
scattering data or nonvanishing transmission premise.
-/

open Complex Matrix
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The scattering matrix obtained from the two constructed asymptotic bases. -/
def scatteringMatrix (q : SchwartzMap ℝ ℂ) (κ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  rightAsymptoticMatrix q κ*(leftAsymptoticMatrix q κ)⁻¹

/-- Equation (2.62), with no assumed scattering data. -/
theorem scatteringMatrix_det (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    (scatteringMatrix q κ).det = 1 := by
  rw [scatteringMatrix, Matrix.det_mul, rightAsymptoticMatrix_det,
    Matrix.det_nonsing_inv, leftAsymptoticMatrix_det]
  simp

/-- The constant matrix changes the right Jost basis to the left Jost basis. -/
theorem leftJostMatrix_eq_right_mul_scattering (q : SchwartzMap ℝ ℂ) (κ x : ℝ) :
    leftJostMatrix q κ x = rightJostMatrix q κ x*scatteringMatrix q κ := by
  have hi : (rightAsymptoticMatrix q κ)⁻¹*rightAsymptoticMatrix q κ = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [rightAsymptoticMatrix_det]; exact isUnit_one)
  simp only [leftJostMatrix, rightJostMatrix, scatteringMatrix]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((rightAsymptoticMatrix q κ)⁻¹), hi,
    one_mul]

/-- The unnormalized connection matrix is independent of the observation position. -/
theorem scatteringMatrix_eq_connection (q : SchwartzMap ℝ ℂ) (κ x : ℝ) :
    (rightJostMatrix q κ x)⁻¹*leftJostMatrix q κ x = scatteringMatrix q κ := by
  rw [leftJostMatrix_eq_right_mul_scattering, ← Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ (by rw [rightJostMatrix_det]; exact isUnit_one), one_mul]

theorem scattering_connection_position_independent (q : SchwartzMap ℝ ℂ) (κ x y : ℝ) :
    (rightJostMatrix q κ x)⁻¹*leftJostMatrix q κ x =
      (rightJostMatrix q κ y)⁻¹*leftJostMatrix q κ y := by
  rw [scatteringMatrix_eq_connection, scatteringMatrix_eq_connection]

/-- The normalized relation (2.59), with the explicit free-phase conjugation. -/
theorem leftJostFunction_eq_right_scattering (q : SchwartzMap ℝ ℂ) (κ x : ℝ) :
    leftJostFunction q κ x = rightJostFunction q κ x *
      (diagonalFrame (-((Real.exp κ)^(2 : ℕ))) x*scatteringMatrix q κ*
        diagonalFrame ((Real.exp κ)^(2 : ℕ)) x) := by
  have hi : diagonalFrame ((Real.exp κ)^(2 : ℕ)) x*diagonalFrame (-((Real.exp κ)^(2 : ℕ))) x = 1 := by
    simpa only [neg_neg] using diagonalFrame_neg_inverse (-((Real.exp κ)^(2 : ℕ))) x
  simp only [leftJostFunction, rightJostFunction, leftJostMatrix_eq_right_mul_scattering]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc (rightJostMatrix q κ x) _ (diagonalFrame (-((Real.exp κ)^(2 : ℕ))) x),
    hi, mul_one]

/-- Equation (2.60): removing the free conjugation recovers a constant matrix. -/
theorem scatteringMatrix_eq_normalized_connection (q : SchwartzMap ℝ ℂ) (κ x : ℝ) :
    diagonalFrame ((Real.exp κ)^(2 : ℕ)) x *
      ((rightJostFunction q κ x)⁻¹*leftJostFunction q κ x) *
        diagonalFrame (-((Real.exp κ)^(2 : ℕ))) x = scatteringMatrix q κ := by
  have hi : diagonalFrame ((Real.exp κ)^(2 : ℕ)) x*diagonalFrame (-((Real.exp κ)^(2 : ℕ))) x = 1 := by
    simpa only [neg_neg] using diagonalFrame_neg_inverse (-((Real.exp κ)^(2 : ℕ))) x
  rw [leftJostFunction_eq_right_scattering,
    ← Matrix.mul_assoc ((rightJostFunction q κ x)⁻¹),
    Matrix.nonsing_inv_mul _ (by rw [rightJostFunction_det]; exact isUnit_one), one_mul]
  simp only [← Matrix.mul_assoc]
  rw [hi, one_mul, Matrix.mul_assoc, hi, mul_one]

/-- Transmission and reflection amplitudes in the paper's convention. -/
def transmission (q : SchwartzMap ℝ ℂ) (κ : ℝ) : ℂ := scatteringMatrix q κ 0 0
def reverseTransmission (q : SchwartzMap ℝ ℂ) (κ : ℝ) : ℂ := scatteringMatrix q κ 1 1
def reflectionAmplitude (q : SchwartzMap ℝ ℂ) (κ : ℝ) : ℂ := scatteringMatrix q κ 1 0
def reverseReflectionAmplitude (q : SchwartzMap ℝ ℂ) (κ : ℝ) : ℂ := scatteringMatrix q κ 0 1

theorem scattering_amplitude_determinant (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    transmission q κ*reverseTransmission q κ -
      reflectionAmplitude q κ*reverseReflectionAmplitude q κ = 1 := by
  have h := scatteringMatrix_det q κ
  simpa only [Matrix.det_fin_two, transmission, reverseTransmission,
    reflectionAmplitude, reverseReflectionAmplitude, mul_comm] using h

/-- The two transmission/reflection columns cannot both vanish. -/
theorem scattering_amplitudes_nondegenerate (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    (transmission q κ ≠ 0 ∨ reflectionAmplitude q κ ≠ 0) ∧
      (reverseTransmission q κ ≠ 0 ∨ reverseReflectionAmplitude q κ ≠ 0) := by
  have h := scattering_amplitude_determinant q κ
  constructor
  · by_contra hc
    push Not at hc
    simp [hc.1,hc.2] at h
  · by_contra hc
    push Not at hc
    simp [hc.1,hc.2] at h

/-- Spatial derivatives of the reconstructed connection vanish identically. -/
theorem scattering_connection_hasDerivAt_zero (q : SchwartzMap ℝ ℂ) (κ x : ℝ) (i j : Fin 2) :
    HasDerivAt (fun y => ((rightJostMatrix q κ y)⁻¹*leftJostMatrix q κ y) i j) 0 x := by
  simp only [scatteringMatrix_eq_connection]
  exact hasDerivAt_const x _

/-- The four Wronskian identities (2.63)–(2.66), in the original eigenmatrix frame. -/
theorem scattering_amplitudes_wronskians (q : SchwartzMap ℝ ℂ) (κ x : ℝ) :
    transmission q κ = leftJostMatrix q κ x 0 0*rightJostMatrix q κ x 1 1 -
      leftJostMatrix q κ x 1 0*rightJostMatrix q κ x 0 1 ∧
    reverseTransmission q κ = rightJostMatrix q κ x 0 0*leftJostMatrix q κ x 1 1 -
      rightJostMatrix q κ x 1 0*leftJostMatrix q κ x 0 1 ∧
    reflectionAmplitude q κ = rightJostMatrix q κ x 0 0*leftJostMatrix q κ x 1 0 -
      rightJostMatrix q κ x 1 0*leftJostMatrix q κ x 0 0 ∧
    reverseReflectionAmplitude q κ = leftJostMatrix q κ x 0 1*rightJostMatrix q κ x 1 1 -
      leftJostMatrix q κ x 1 1*rightJostMatrix q κ x 0 1 := by
  have hd := rightJostMatrix_det q κ x
  rw [Matrix.det_fin_two] at hd
  simp only [leftJostMatrix_eq_right_mul_scattering, Matrix.mul_apply, Fin.sum_univ_two,
    transmission, reverseTransmission, reflectionAmplitude, reverseReflectionAmplitude]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination -(scatteringMatrix q κ 0 0)*hd
  · linear_combination -(scatteringMatrix q κ 1 1)*hd
  · linear_combination -(scatteringMatrix q κ 1 0)*hd
  · linear_combination -(scatteringMatrix q κ 0 1)*hd

/-- At the origin the same Wronskians use the normalized Jost functions directly. -/
theorem scattering_amplitudes_normalized_wronskians (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    transmission q κ = leftJostFunction q κ 0 0 0*rightJostFunction q κ 0 1 1 -
      leftJostFunction q κ 0 1 0*rightJostFunction q κ 0 0 1 ∧
    reverseTransmission q κ = rightJostFunction q κ 0 0 0*leftJostFunction q κ 0 1 1 -
      rightJostFunction q κ 0 1 0*leftJostFunction q κ 0 0 1 ∧
    reflectionAmplitude q κ = rightJostFunction q κ 0 0 0*leftJostFunction q κ 0 1 0 -
      rightJostFunction q κ 0 1 0*leftJostFunction q κ 0 0 0 ∧
    reverseReflectionAmplitude q κ = leftJostFunction q κ 0 0 1*rightJostFunction q κ 0 1 1 -
      leftJostFunction q κ 0 1 1*rightJostFunction q κ 0 0 1 := by
  have hz : diagonalFrame ((Real.exp κ)^(2 : ℕ)) 0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonalFrame, FDNLS.staggerPhase]
  simpa only [leftJostFunction, rightJostFunction, hz, mul_one] using
    scattering_amplitudes_wronskians q κ 0

end
end GaloisForLFunctions.HTGeometry.FokasLenells
