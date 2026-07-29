import GaloisForLFunctions.U0.HolomorphicIFT
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Analysis.Analytic.Constructions

/-!
# Holomorphic scalar branches over finite-dimensional parameter spaces

This module extends the existing scalar-parameter holomorphic implicit-function theorem to an
arbitrary complete complex Banach parameter space. The result is the analytic branch engine needed
for eigenvalues of Hamiltonians with one independent coupling per interaction edge.
-/

open Filter Topology Complex ContinuousLinearMap Set
open scoped ContDiff

namespace GaloisForLFunctions.HTGeometry

/-- Holomorphic implicit function theorem with an arbitrary complete complex Banach parameter
space and a scalar root variable. -/
theorem parametric_holo_implicit
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
    {f : P × ℂ → ℂ} {p₀ : P} {w₀ : ℂ}
    (hf : AnalyticAt ℂ f (p₀, w₀)) (h0 : f (p₀, w₀) = 0)
    (hfw : (fderiv ℂ f (p₀, w₀)) (0, 1) ≠ 0) :
    ∃ r : P → ℂ, AnalyticAt ℂ r p₀ ∧ r p₀ = w₀ ∧
      (∀ᶠ p in 𝓝 p₀, f (p, r p) = 0) := by
  have cdf : ContDiffAt ℂ ω f (p₀, w₀) := hf.contDiffAt
  have if₂ : (fderiv ℂ f (p₀, w₀) ∘L (.inr ℂ P ℂ)).IsInvertible :=
    HolomorphicIFT.clm_invertible_of_apply_one_ne (by simpa using hfw)
  have hω : (ω : WithTop ℕ∞) ≠ 0 := by decide
  refine ⟨cdf.implicitFunction hω if₂,
    (cdf.contDiffAt_implicitFunction hω if₂).analyticAt, ?_, ?_⟩
  · exact cdf.implicitFunction_apply_self hω if₂
  · filter_upwards [cdf.eventually_apply_implicitFunction hω if₂] with p hp
    rw [hp, h0]

/-! ## Analytic branches of simple diagonal matrix eigenvalues -/

open Matrix Polynomial

/-- Determinants preserve analyticity of a finite matrix-valued family. -/
theorem analyticAt_matrix_det_parametric
    {P ι : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [Fintype ι] [DecidableEq ι]
    {M : P → Matrix ι ι ℂ} {p₀ : P}
    (hM : ∀ i j, AnalyticAt ℂ (fun p => M p i j) p₀) :
    AnalyticAt ℂ (fun p => (M p).det) p₀ := by
  have heq : (fun p => (M p).det)
      = fun p => ∑ σ : Equiv.Perm ι,
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M p (σ i) i := by
    funext p
    rw [Matrix.det_apply]
    exact Finset.sum_congr rfl
      (fun σ _ => by rw [Units.smul_def, zsmul_eq_mul])
  rw [heq]
  exact Finset.analyticAt_fun_sum _
    (fun σ _ => analyticAt_const.mul
      (Finset.analyticAt_fun_prod _ (fun i _ => hM (σ i) i)))

/-- Characteristic determinant with the matrix and spectral value both treated as parameters. -/
def matrixCharpolyRelation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : Matrix ι ι ℂ × ℂ) : ℂ :=
  (Matrix.scalar ι q.2 - q.1).det

theorem matrixCharpolyRelation_analyticAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q₀ : Matrix ι ι ℂ × ℂ) :
    AnalyticAt ℂ (matrixCharpolyRelation (ι := ι)) q₀ := by
  apply analyticAt_matrix_det_parametric
  intro i j
  have hentry :
      AnalyticAt ℂ (fun q : Matrix ι ι ℂ × ℂ => q.1 i j) q₀ := by
    exact (((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.proj i)).analyticAt q₀.1).comp q₀ analyticAt_fst
  by_cases hij : i = j
  · subst j
    simpa [matrixCharpolyRelation, Matrix.scalar_apply] using
      analyticAt_snd.sub hentry
  · simpa [matrixCharpolyRelation, Matrix.scalar_apply, hij] using
      analyticAt_const.sub hentry

/-- The pure spectral-value derivative of the characteristic determinant is the derivative of the
characteristic polynomial. -/
theorem matrixCharpolyRelation_partial_w
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (w : ℂ) :
    (fderiv ℂ (matrixCharpolyRelation (ι := ι)) (H, w)) (0, 1) =
      (derivative H.charpoly).eval w := by
  let f := matrixCharpolyRelation (ι := ι)
  have hfdiff : HasFDerivAt f (fderiv ℂ f (H, w)) (H, w) :=
    (matrixCharpolyRelation_analyticAt (H, w)).differentiableAt.hasFDerivAt
  have hι : HasFDerivAt (fun z : ℂ => (H, z))
      ((0 : ℂ →L[ℂ] Matrix ι ι ℂ).prod
        (ContinuousLinearMap.id ℂ ℂ)) w :=
    (hasFDerivAt_const H w).prodMk (hasFDerivAt_id w)
  have hcomp : HasFDerivAt (fun z => f (H, z))
      ((fderiv ℂ f (H, w)).comp
        ((0 : ℂ →L[ℂ] Matrix ι ι ℂ).prod
          (ContinuousLinearMap.id ℂ ℂ))) w :=
    hfdiff.comp w hι
  have hpoly :
      HasDerivAt (fun z => f (H, z))
        ((derivative H.charpoly).eval w) w := by
    have heq : (fun z => f (H, z)) =
        fun z => H.charpoly.eval z := by
      funext z
      exact (Matrix.eval_charpoly H z).symm
    rw [heq]
    exact Polynomial.hasDerivAt H.charpoly w
  have huniq := hcomp.unique hpoly.hasFDerivAt
  have hev := ContinuousLinearMap.ext_iff.mp huniq 1
  simpa [f] using hev

/-- Every eigenvalue of a diagonal matrix with pairwise-distinct entries has a locally analytic
branch under arbitrary complex matrix perturbations. -/
theorem simpleDiagonalMatrix_eigenvalueBranch
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (hinj : Function.Injective energy) (x : ι) :
    ∃ branch : Matrix ι ι ℂ → ℂ,
      AnalyticAt ℂ branch (Matrix.diagonal energy) ∧
      branch (Matrix.diagonal energy) = energy x ∧
      (∀ᶠ H in 𝓝 (Matrix.diagonal energy),
        (matrixCharpolyRelation (H, branch H) = 0)) := by
  have hanalytic :
      AnalyticAt ℂ (matrixCharpolyRelation (ι := ι))
        (Matrix.diagonal energy, energy x) :=
    matrixCharpolyRelation_analyticAt _
  have hroot :
      matrixCharpolyRelation
          (Matrix.diagonal energy, energy x) = 0 := by
    rw [← Matrix.eval_charpoly, Matrix.charpoly_diagonal]
    simp
  have hsep :
      (∏ i, (X - C (energy i)) : ℂ[X]).Separable :=
    Polynomial.separable_prod_X_sub_C_iff.mpr hinj
  have heval :
      (∏ i, (X - C (energy i)) : ℂ[X]).eval (energy x) = 0 := by
    simp
  have hderiv :
      (derivative (Matrix.diagonal energy).charpoly).eval (energy x) ≠ 0 := by
    rw [Matrix.charpoly_diagonal]
    have hne := hsep.eval₂_derivative_ne_zero
      (RingHom.id ℂ) (by simpa using heval)
    simpa using hne
  exact parametric_holo_implicit hanalytic hroot
    (by simpa [matrixCharpolyRelation_partial_w] using hderiv)

end GaloisForLFunctions.HTGeometry
