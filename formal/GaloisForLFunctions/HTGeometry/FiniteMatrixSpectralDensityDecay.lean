import GaloisForLFunctions.HTGeometry.GaussianRadialActionKernel
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Finite matrix spectral-density Fourier decay

Riemann--Lebesgue decay for complex spectral densities is upgraded entrywise to operator-norm
decay for finite matrices. The final theorem is the exact finite-dimensional bridge used after
absolute continuity of a matrix-valued spectral measure has been established.
-/

open Filter Topology MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

noncomputable def matrixVecLinearEquiv
    (I : Type*) [Fintype I] [DecidableEq I] :
    Matrix I I ℂ ≃ₗ[ℂ] ((I × I) → ℂ) :=
  LinearEquiv.ofBijective
    { toFun := Matrix.vec
      map_add' := Matrix.vec_add
      map_smul' := Matrix.vec_smul }
    Matrix.vec_bijective

theorem finiteMatrix_entrywise_tendsto_operatorNorm_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    {α : Type*} {l : Filter α} (U : α → Matrix I I ℂ)
    (hU : ∀ i j, Tendsto (fun t => U t i j) l (𝓝 0)) :
    Tendsto (fun t => ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) (U t)‖) l (𝓝 0) := by
  have hmatrix : Tendsto U l (𝓝 0) := by
    let e := matrixVecLinearEquiv I
    have hvec : Tendsto (fun t => e (U t)) l (𝓝 0) := by
      rw [tendsto_pi_nhds]
      intro ij
      simpa [e, matrixVecLinearEquiv, Matrix.vec] using hU ij.2 ij.1
    have hback0 := e.toContinuousLinearEquiv.symm.continuous.tendsto
      (0 : (I × I) → ℂ)
    have hback : Tendsto e.toContinuousLinearEquiv.symm
        (𝓝 (0 : (I × I) → ℂ)) (𝓝 (0 : Matrix I I ℂ)) := by
      simpa using hback0
    have hback' := hback.comp hvec
    have hfun : (e.toContinuousLinearEquiv.symm ∘ fun t => e (U t)) = U := by
      funext t
      exact e.symm_apply_apply (U t)
    rw [hfun] at hback'
    exact hback'
  simpa only [Matrix.cstar_norm_def, map_zero, norm_zero] using hmatrix.norm

noncomputable def spectralDensityFourierAmplitude
    (density : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-((t * x : ℝ) : ℂ) * Complex.I) * density x

theorem spectralDensityFourierAmplitude_tendsto_zero_cocompact
    (density : ℝ → ℂ) :
    Tendsto (spectralDensityFourierAmplitude density)
      (cocompact ℝ) (𝓝 0) := by
  have hfourier := Real.tendsto_integral_exp_smul_cocompact density
  have hcomp := hfourier.comp (GaloisForLFunctions.HTGeometry.tendsto_div_const_cocompact
    (c := 2 * Real.pi) (by positivity))
  refine hcomp.congr fun t => ?_
  rw [Function.comp_apply, spectralDensityFourierAmplitude]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [Circle.smul_def, Real.fourierChar_apply]
  congr 2
  push_cast
  field_simp

noncomputable def finiteMatrixSpectralDensityAmplitude
    {I : Type*} (density : I → I → ℝ → ℂ) (t : ℝ) : Matrix I I ℂ :=
  fun i j => spectralDensityFourierAmplitude (density i j) t

theorem finiteMatrixSpectralDensityAmplitude_entry_tendsto_zero
    {I : Type*} (density : I → I → ℝ → ℂ) (i j : I) :
    Tendsto (fun t => finiteMatrixSpectralDensityAmplitude density t i j)
      (cocompact ℝ) (𝓝 0) :=
  spectralDensityFourierAmplitude_tendsto_zero_cocompact (density i j)

theorem finiteMatrixSpectralDensityAmplitude_operatorNorm_tendsto_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (density : I → I → ℝ → ℂ) :
    Tendsto (fun t => ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I))
      (finiteMatrixSpectralDensityAmplitude density t)‖)
      (cocompact ℝ) (𝓝 0) := by
  exact finiteMatrix_entrywise_tendsto_operatorNorm_zero
    (finiteMatrixSpectralDensityAmplitude density)
    (finiteMatrixSpectralDensityAmplitude_entry_tendsto_zero density)

end

end GaloisForLFunctions.HTGeometry
