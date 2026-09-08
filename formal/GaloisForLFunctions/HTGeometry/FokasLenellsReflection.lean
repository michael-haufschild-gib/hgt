import GaloisForLFunctions.HTGeometry.FokasLenellsScattering
import GaloisForLFunctions.HTGeometry.FokasLenellsSpatialUniqueness

/-!
# Reverse-space scattering symmetry and its involution

At initial time, the nonlocal reduction in Yan–Zhang–Zhu,
arXiv:2607.19649v1, exchanges the two spatial components under `x ↦ -x`.
Uniqueness of the constructed spatial ODE proves the Jost symmetry (2.68),
the inverse-conjugation identity (2.69), and opposite reflection amplitudes
(2.71). All statements hold for every complex Schwartz potential and every
positive real spectral parameter, without a scattering-data hypothesis.

The positive algebraic consequence is that scattering followed by the
component swap is a traceless determinant-minus-one involution. This exposes
a bridge to the corpus's involution decompositions and matrix exponentials.
-/

open Complex Matrix Filter
open scoped Topology Matrix.Norms.Elementwise
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section


def swapOperator : SpectralVector →L[ℝ] SpectralVector :=
  (ContinuousLinearMap.snd ℝ ℂ ℂ).prod (ContinuousLinearMap.fst ℝ ℂ ℂ)

@[simp] theorem swapOperator_apply (v : SpectralVector) : swapOperator v = (v.2,v.1) := rfl
@[simp] theorem swapOperator_involution (v : SpectralVector) : swapOperator (swapOperator v) = v := rfl

def swapMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;1,0]

@[simp] theorem swapMatrix_squared : swapMatrix*swapMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- Reverse space and swap the two spectral components; no complex conjugation occurs. -/
theorem spatialOperator_reflection (q : SchwartzMap ℝ ℂ) (a : ℂ) (x : ℝ)
    (v : SpectralVector) :
    -swapOperator (spatialOperator q a (-x) v) = spatialOperator q a x (swapOperator v) := by
  apply Prod.ext <;>
    simp [spatialOperator, pairOperator, reflectedDerivative, RHTower.negSchwartz'_apply,
      SchwartzMap.derivCLM_apply]

theorem reflected_spatialEigenfunction_isSpatialSolution (q : SchwartzMap ℝ ℂ) (a : ℂ)
    (v : SpectralVector) :
    IsSpatialSolution q a v (fun x => swapOperator (spatialEigenfunction q a (swapOperator v) (-x))) := by
  constructor
  · simp [spatialEigenfunction_initial]
  · intro x
    have h := (spatialEigenfunction_isSpatialSolution q a (swapOperator v)).2 (-x)
    have hn := h.scomp x (hasDerivAt_id x).neg
    have hs := swapOperator.hasFDerivAt.comp_hasDerivAt x hn
    simpa only [Function.comp_def, neg_one_smul, map_neg, spatialOperator_reflection] using hs

/-- Uniqueness forces the reverse-space symmetry of the constructed original eigenfunctions. -/
theorem spatialEigenfunction_reflection (q : SchwartzMap ℝ ℂ) (a : ℂ) (v : SpectralVector) (x : ℝ) :
    spatialEigenfunction q a v (-x) = swapOperator (spatialEigenfunction q a (swapOperator v) x) := by
  have h := (spatialSolution_existsUnique q a v).unique
    (reflected_spatialEigenfunction_isSpatialSolution q a v)
    (spatialEigenfunction_isSpatialSolution q a v)
  simpa only [neg_neg] using (congrFun h (-x)).symm

theorem spatialFundamentalMatrix_reflection (q : SchwartzMap ℝ ℂ) (a : ℂ) (x : ℝ) :
    spatialFundamentalMatrix q a (-x) = swapMatrix*spatialFundamentalMatrix q a x*swapMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spatialFundamentalMatrix, spatialEigenfunction_reflection, swapMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem rotatingFrame_reflection (z x : ℝ) (v : SpectralVector) :
    rotatingFrame z (-x) (swapOperator v) = swapOperator (rotatingFrame z x v) := by
  apply Prod.ext <;> simp [rotatingFrame, FDNLS.staggerPhase]

theorem interactionSolution_reflection (q : SchwartzMap ℝ ℂ) (κ : ℝ)
    (v : SpectralVector) (x : ℝ) :
    interactionSolution q κ v (-x) = swapOperator (interactionSolution q κ (swapOperator v) x) := by
  simp only [interactionSolution, spatialEigenfunction_reflection, rotatingFrame_reflection]

theorem leftAsymptoticVector_reflection (q : SchwartzMap ℝ ℂ) (κ : ℝ) (v : SpectralVector) :
    leftAsymptoticVector q κ v = swapOperator (rightAsymptoticVector q κ (swapOperator v)) := by
  have hl := reversedInteractionSolution_tendsto_right q κ v
  have hr := swapOperator.continuous.continuousAt.tendsto.comp
    (interactionSolution_tendsto_right q κ (swapOperator v))
  apply tendsto_nhds_unique hl
  change Tendsto (fun x => interactionSolution q κ v (-x)) atTop _
  simpa only [interactionSolution_reflection, Function.comp_def] using hr

theorem leftAsymptoticMatrix_reflection (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    leftAsymptoticMatrix q κ = swapMatrix*rightAsymptoticMatrix q κ*swapMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leftAsymptoticMatrix, rightAsymptoticMatrix, leftAsymptoticVector_reflection,
      swapMatrix, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem swapMatrix_inverse : swapMatrix⁻¹ = swapMatrix := by
  simp [Matrix.inv_def, swapMatrix, Matrix.det_fin_two, Matrix.adjugate_fin_two]

/-- The left original Jost basis is the reflected right basis, as in (2.68) at initial time. -/
theorem leftJostMatrix_reflection (q : SchwartzMap ℝ ℂ) (κ x : ℝ) :
    leftJostMatrix q κ (-x) = swapMatrix*rightJostMatrix q κ x*swapMatrix := by
  simp only [leftJostMatrix, spatialFundamentalMatrix_reflection,
    leftAsymptoticMatrix_reflection, Matrix.mul_inv_rev, swapMatrix_inverse,
    rightJostMatrix, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc swapMatrix swapMatrix, swapMatrix_squared, one_mul]

theorem diagonalFrame_reflection (z x : ℝ) :
    diagonalFrame z (-x) = swapMatrix*diagonalFrame z x*swapMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalFrame, swapMatrix, Matrix.mul_apply, Fin.sum_univ_two, FDNLS.staggerPhase]

/-- The reverse-space Jost symmetry survives the paper's phase normalization. -/
theorem leftJostFunction_reflection (q : SchwartzMap ℝ ℂ) (κ x : ℝ) :
    leftJostFunction q κ (-x) = swapMatrix*rightJostFunction q κ x*swapMatrix := by
  simp only [leftJostFunction, leftJostMatrix_reflection, diagonalFrame_reflection,
    rightJostFunction, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc swapMatrix swapMatrix, swapMatrix_squared, one_mul]

/-- The full scattering matrix is determined by the right asymptotic basis alone. -/
theorem scatteringMatrix_reflected_factorization (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    scatteringMatrix q κ = rightAsymptoticMatrix q κ*swapMatrix*
      (rightAsymptoticMatrix q κ)⁻¹*swapMatrix := by
  simp only [scatteringMatrix, leftAsymptoticMatrix_reflection,
    Matrix.mul_inv_rev, swapMatrix_inverse, Matrix.mul_assoc]

/-- The antisymmetry (2.71) is derived from the potential, with no assumption on amplitudes. -/
theorem reverseReflectionAmplitude_eq_neg (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    reverseReflectionAmplitude q κ = -reflectionAmplitude q κ := by
  simp [reverseReflectionAmplitude, reflectionAmplitude,
    scatteringMatrix_reflected_factorization, Matrix.inv_def, rightAsymptoticMatrix_det,
    Matrix.adjugate_fin_two, swapMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The paper's inverse-conjugation symmetry (2.69), at initial time. -/
theorem scatteringMatrix_inverse_reflection (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    scatteringMatrix q κ = swapMatrix*(scatteringMatrix q κ)⁻¹*swapMatrix := by
  have hb := reverseReflectionAmplitude_eq_neg q κ
  change scatteringMatrix q κ 0 1 = -scatteringMatrix q κ 1 0 at hb
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.inv_def, scatteringMatrix_det, Matrix.adjugate_fin_two,
      swapMatrix, Matrix.mul_apply, Fin.sum_univ_two, hb]

/-- A nonlinear constraint on the three independent initial scattering amplitudes. -/
theorem scattering_amplitude_quadric (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    transmission q κ*reverseTransmission q κ + reflectionAmplitude q κ^2 = 1 := by
  have h := scattering_amplitude_determinant q κ
  rw [reverseReflectionAmplitude_eq_neg] at h
  linear_combination h

/-- Multiplication by the component swap turns scattering into an involution. -/
theorem scattering_swap_involution (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    (scatteringMatrix q κ*swapMatrix)^2 = 1 := by
  rw [pow_two]
  conv_lhs => lhs; lhs; rw [scatteringMatrix_inverse_reflection]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc swapMatrix swapMatrix, swapMatrix_squared, one_mul]
  rw [← Matrix.mul_assoc ((scatteringMatrix q κ)⁻¹),
    Matrix.nonsing_inv_mul _ (by rw [scatteringMatrix_det]; exact isUnit_one),
    one_mul, swapMatrix_squared]

theorem scattering_swap_trace (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    (scatteringMatrix q κ*swapMatrix).trace = 0 := by
  have h := reverseReflectionAmplitude_eq_neg q κ
  change scatteringMatrix q κ 0 1 = -scatteringMatrix q κ 1 0 at h
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two, swapMatrix, h]

theorem scattering_swap_det (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    (scatteringMatrix q κ*swapMatrix).det = -1 := by
  rw [Matrix.det_mul, scatteringMatrix_det, one_mul]
  simp [swapMatrix, Matrix.det_fin_two]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
