import GaloisForLFunctions.HTGeometry.FokasLenellsInteractionFrame
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix.Normed

/-!
# Right Jost solutions from proved asymptotic transport

The right asymptotic vectors constructed from integrable transport preserve
the determinant pairing. Their matrix therefore has determinant one, so its
inverse normalizes the spatial fundamental matrix at infinity.

For every Schwartz potential and positive real spectral parameter `exp κ`,
the resulting Jost function satisfies the spatial commutator equation (2.2)
of Yan–Zhang–Zhu, arXiv:2607.19649v1, converges to the identity as specified
after (2.3), and has determinant one as in (2.61). Both left and right phase
conventions are related by an isometric diagonal conjugation. All existence,
normalization and invertibility conditions are proved internally.

Only the right endpoint and positive real spectral parameters are treated;
no analytic continuation or nonlinear inverse-scattering theorem is asserted.
-/

open Complex Matrix Filter Topology
open scoped Matrix.Norms.Elementwise
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section


theorem rotatingFrame_wedge (z x : ℝ) (v w : SpectralVector) :
    (rotatingFrame z x v).1*(rotatingFrame z x w).2 -
      (rotatingFrame z x v).2*(rotatingFrame z x w).1 = v.1*w.2-v.2*w.1 := by
  have hp : FDNLS.staggerPhase z x*FDNLS.staggerPhase (-z) x = 1 := by
    simp [FDNLS.staggerPhase, ← Complex.exp_add]
  change (FDNLS.staggerPhase z x*v.1)*(FDNLS.staggerPhase (-z) x*w.2) -
    (FDNLS.staggerPhase (-z) x*v.2)*(FDNLS.staggerPhase z x*w.1) = _
  calc
    _ = (FDNLS.staggerPhase z x*FDNLS.staggerPhase (-z) x)*(v.1*w.2-v.2*w.1) := by ring
    _ = _ := by rw [hp,one_mul]

theorem interactionSolution_wedge (q : SchwartzMap ℝ ℂ) (κ : ℝ)
    (v w : SpectralVector) (x : ℝ) :
    (interactionSolution q κ v x).1*(interactionSolution q κ w x).2 -
      (interactionSolution q κ v x).2*(interactionSolution q κ w x).1 = v.1*w.2-v.2*w.1 := by
  rw [interactionSolution, interactionSolution, rotatingFrame_wedge]
  exact spatialWedge_constant q (κ:ℂ) v w x

/-- Conservation survives the limit to infinity. -/
theorem rightAsymptoticVector_wedge (q : SchwartzMap ℝ ℂ) (κ : ℝ) (v w : SpectralVector) :
    (rightAsymptoticVector q κ v).1*(rightAsymptoticVector q κ w).2 -
      (rightAsymptoticVector q κ v).2*(rightAsymptoticVector q κ w).1 = v.1*w.2-v.2*w.1 := by
  have hv := interactionSolution_tendsto_right q κ v
  have hw := interactionSolution_tendsto_right q κ w
  have h := (hv.fst_nhds.mul hw.snd_nhds).sub (hv.snd_nhds.mul hw.fst_nhds)
  simp only [interactionSolution_wedge] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

def interactionFundamentalMatrix (q : SchwartzMap ℝ ℂ) (κ x : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(interactionSolution q κ (1,0) x).1, (interactionSolution q κ (0,1) x).1;
     (interactionSolution q κ (1,0) x).2, (interactionSolution q κ (0,1) x).2]

def rightAsymptoticMatrix (q : SchwartzMap ℝ ℂ) (κ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(rightAsymptoticVector q κ (1,0)).1, (rightAsymptoticVector q κ (0,1)).1;
     (rightAsymptoticVector q κ (1,0)).2, (rightAsymptoticVector q κ (0,1)).2]

theorem interactionFundamentalMatrix_tendsto (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    Tendsto (interactionFundamentalMatrix q κ) atTop (𝓝 (rightAsymptoticMatrix q κ)) := by
  have hc : Continuous (fun p : SpectralVector × SpectralVector =>
      (!![p.1.1,p.2.1;p.1.2,p.2.2] : Matrix (Fin 2) (Fin 2) ℂ)) := by fun_prop
  exact (hc.tendsto _).comp ((interactionSolution_tendsto_right q κ (1,0)).prodMk_nhds
    (interactionSolution_tendsto_right q κ (0,1)))

theorem rightAsymptoticMatrix_det (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    (rightAsymptoticMatrix q κ).det = 1 := by
  have h := rightAsymptoticVector_wedge q κ (1,0) (0,1)
  simpa [rightAsymptoticMatrix, Matrix.det_fin_two, mul_comm] using h

theorem rightAsymptoticMatrix_mul_inverse (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    rightAsymptoticMatrix q κ * (rightAsymptoticMatrix q κ)⁻¹ = 1 := by
  apply Matrix.mul_nonsing_inv
  rw [rightAsymptoticMatrix_det]
  exact isUnit_one

/-- The fundamental matrix normalized at the right infinite endpoint. -/
def rightJostMatrix (q : SchwartzMap ℝ ℂ) (κ x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  spatialFundamentalMatrix q (κ:ℂ) x * (rightAsymptoticMatrix q κ)⁻¹

/-- Its representation in the rotating frame. -/
def rightJostFrame (q : SchwartzMap ℝ ℂ) (κ x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  interactionFundamentalMatrix q κ x * (rightAsymptoticMatrix q κ)⁻¹

/-- Actual normalization at infinity; no Jost limit is assumed. -/
theorem rightJostFrame_tendsto_one (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    Tendsto (rightJostFrame q κ) atTop (𝓝 1) := by
  have h := (interactionFundamentalMatrix_tendsto q κ).mul_const
    ((rightAsymptoticMatrix q κ)⁻¹)
  rwa [rightAsymptoticMatrix_mul_inverse] at h

/-- The rotating-frame object is the diagonal renormalization of the actual Lax eigenmatrix. -/
theorem rightJostFrame_eq_diagonal_mul (q : SchwartzMap ℝ ℂ) (κ x : ℝ) :
    rightJostFrame q κ x =
      !![FDNLS.staggerPhase ((Real.exp κ)^(2 : ℕ)) x,0;
        0,FDNLS.staggerPhase (-((Real.exp κ)^(2 : ℕ))) x] * rightJostMatrix q κ x := by
  unfold rightJostFrame rightJostMatrix
  rw [← Matrix.mul_assoc]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [interactionFundamentalMatrix, spatialFundamentalMatrix, interactionSolution,
      rotatingFrame, Matrix.mul_apply, Fin.sum_univ_two]

theorem rightJostMatrix_det (q : SchwartzMap ℝ ℂ) (κ x : ℝ) :
    (rightJostMatrix q κ x).det = 1 := by
  rw [rightJostMatrix, Matrix.det_mul, spatialFundamentalMatrix_det,
    Matrix.det_nonsing_inv, rightAsymptoticMatrix_det]
  simp

/-- Entrywise derivative of the previously constructed fundamental matrix. -/
theorem spatialFundamentalMatrix_entry_hasDerivAt (q : SchwartzMap ℝ ℂ) (a : ℂ)
    (x : ℝ) (i j : Fin 2) :
    HasDerivAt (fun y => spatialFundamentalMatrix q a y i j)
      ((spatialLax (deriv q x) (deriv (fun y : ℝ => q (-y)) x) (Complex.exp a) *
        spatialFundamentalMatrix q a x) i j) x := by
  fin_cases i <;> fin_cases j
  · simpa [spatialFundamentalMatrix, spatialLax, Matrix.mul_apply, Fin.sum_univ_two] using
      spatialEigenfunction_first_hasDerivAt q a (1,0) x
  · simpa [spatialFundamentalMatrix, spatialLax, Matrix.mul_apply, Fin.sum_univ_two] using
      spatialEigenfunction_first_hasDerivAt q a (0,1) x
  · simpa [spatialFundamentalMatrix, spatialLax, Matrix.mul_apply, Fin.sum_univ_two,
      sub_eq_add_neg] using spatialEigenfunction_second_hasDerivAt q a (1,0) x
  · simpa [spatialFundamentalMatrix, spatialLax, Matrix.mul_apply, Fin.sum_univ_two,
      sub_eq_add_neg] using spatialEigenfunction_second_hasDerivAt q a (0,1) x

/-- The asymptotically normalized matrix still satisfies the original Lax equation. -/
theorem rightJostMatrix_entry_hasDerivAt (q : SchwartzMap ℝ ℂ) (κ x : ℝ) (i j : Fin 2) :
    HasDerivAt (fun y => rightJostMatrix q κ y i j)
      ((spatialLax (deriv q x) (deriv (fun y : ℝ => q (-y)) x) (Complex.exp (κ:ℂ)) *
        rightJostMatrix q κ x) i j) x := by
  let C := (rightAsymptoticMatrix q κ)⁻¹
  have h := ((spatialFundamentalMatrix_entry_hasDerivAt q (κ:ℂ) x i 0).mul_const (C 0 j)).fun_add
    ((spatialFundamentalMatrix_entry_hasDerivAt q (κ:ℂ) x i 1).mul_const (C 1 j))
  simp only [rightJostMatrix, ← Matrix.mul_assoc]
  simpa only [Matrix.mul_apply, Fin.sum_univ_two, Pi.add_apply, C] using h

/-- A diagonal free-propagation matrix. -/
def diagonalFrame (z x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![FDNLS.staggerPhase z x,0;0,FDNLS.staggerPhase (-z) x]

theorem diagonalFrame_neg_inverse (z x : ℝ) : diagonalFrame (-z) x*diagonalFrame z x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalFrame, Matrix.mul_apply, Fin.sum_univ_two, FDNLS.staggerPhase,
      ← Complex.exp_add]

/-- Real spectral oscillations preserve the matrix sup norm under conjugation. -/
theorem diagonalFrame_conjugation_norm (z x : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖diagonalFrame (-z) x*A*diagonalFrame z x‖ = ‖A‖ := by
  have he (i j : Fin 2) : ‖(diagonalFrame (-z) x*A*diagonalFrame z x) i j‖ = ‖A i j‖ := by
    fin_cases i <;> fin_cases j <;>
      simp [diagonalFrame, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, FDNLS.norm_staggerPhase]
  simp only [Matrix.norm_eq_sup_sup_nnnorm]
  congr 1
  apply Finset.sup_congr rfl
  intro i _
  apply Finset.sup_congr rfl
  intro j _
  exact NNReal.eq (he i j)

/-- The paper's right-normalized Jost function, with free phases removed on the right. -/
def rightJostFunction (q : SchwartzMap ℝ ℂ) (κ x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  rightJostMatrix q κ x*diagonalFrame ((Real.exp κ)^(2 : ℕ)) x

theorem rightJostFunction_norm_sub_one (q : SchwartzMap ℝ ℂ) (κ x : ℝ) :
    ‖rightJostFunction q κ x-1‖ = ‖rightJostFrame q κ x-1‖ := by
  have hleft : diagonalFrame (-((Real.exp κ)^(2 : ℕ))) x*rightJostFrame q κ x =
      rightJostMatrix q κ x := by
    rw [rightJostFrame_eq_diagonal_mul]
    change diagonalFrame (-((Real.exp κ)^(2 : ℕ))) x *
      (diagonalFrame ((Real.exp κ)^(2 : ℕ)) x * rightJostMatrix q κ x) = _
    rw [← Matrix.mul_assoc, diagonalFrame_neg_inverse, one_mul]
  have he : rightJostFunction q κ x-1 =
      diagonalFrame (-((Real.exp κ)^(2 : ℕ))) x*(rightJostFrame q κ x-1)*
        diagonalFrame ((Real.exp κ)^(2 : ℕ)) x := by
    rw [mul_sub, sub_mul, mul_one, hleft, diagonalFrame_neg_inverse]
    rfl
  rw [he, diagonalFrame_conjugation_norm]

/-- The Jost normalization specified after equation (2.3) holds at positive real spectral parameters. -/
theorem rightJostFunction_tendsto_one (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    Tendsto (rightJostFunction q κ) atTop (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h := tendsto_iff_norm_sub_tendsto_zero.mp (rightJostFrame_tendsto_one q κ)
  simpa only [rightJostFunction_norm_sub_one] using h

theorem diagonalFrame_det (z x : ℝ) : (diagonalFrame z x).det = 1 := by
  simp [diagonalFrame, Matrix.det_fin_two, FDNLS.staggerPhase, ← Complex.exp_add]

theorem rightJostFunction_det (q : SchwartzMap ℝ ℂ) (κ x : ℝ) :
    (rightJostFunction q κ x).det = 1 := by
  rw [rightJostFunction, Matrix.det_mul, rightJostMatrix_det, diagonalFrame_det, one_mul]

/-- The normalized Jost function solves the commutator form of the spatial Lax equation. -/
theorem rightJostFunction_entry_hasDerivAt (q : SchwartzMap ℝ ℂ) (κ x : ℝ) (i j : Fin 2) :
    HasDerivAt (fun y => rightJostFunction q κ y i j)
      ((spatialLax (deriv q x) (deriv (fun y : ℝ => q (-y)) x) (Complex.exp (κ:ℂ)) *
          rightJostFunction q κ x -
        rightJostFunction q κ x * spatialLax 0 0 (Complex.exp (κ:ℂ))) i j) x := by
  fin_cases j
  · have he : (fun y => rightJostFunction q κ y i 0) =
        fun y => rightJostMatrix q κ y i 0*FDNLS.staggerPhase ((Real.exp κ)^(2 : ℕ)) y := by
      funext y
      simp [rightJostFunction, diagonalFrame, Matrix.mul_apply, Fin.sum_univ_two]
    refine (((rightJostMatrix_entry_hasDerivAt q κ x i 0).fun_mul
      (FDNLS.hasDerivAt_staggerPhase ((Real.exp κ)^(2 : ℕ)) x)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun y => congrFun he y))).congr_deriv ?_
    fin_cases i <;>
      simp [rightJostFunction, diagonalFrame, spatialLax, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, Fin.sum_univ_two, ← Complex.ofReal_exp] <;> ring
  · have he : (fun y => rightJostFunction q κ y i 1) =
        fun y => rightJostMatrix q κ y i 1*FDNLS.staggerPhase (-((Real.exp κ)^(2 : ℕ))) y := by
      funext y
      simp [rightJostFunction, diagonalFrame, Matrix.mul_apply, Fin.sum_univ_two]
    refine (((rightJostMatrix_entry_hasDerivAt q κ x i 1).fun_mul
      (FDNLS.hasDerivAt_staggerPhase (-((Real.exp κ)^(2 : ℕ))) x)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun y => congrFun he y))).congr_deriv ?_
    fin_cases i <;>
      simp [rightJostFunction, diagonalFrame, spatialLax, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, Fin.sum_univ_two, ← Complex.ofReal_exp] <;> ring

end
end GaloisForLFunctions.HTGeometry.FokasLenells
