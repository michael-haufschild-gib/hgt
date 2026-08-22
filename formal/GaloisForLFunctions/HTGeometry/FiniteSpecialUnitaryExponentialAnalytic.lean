import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryNormalization
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Real-analytic normalized finite-unitary exponential coordinates

The self-adjoint exponential supplies real-analytic local coordinates on a
finite unitary group.  Composing it with the explicit determinant normalizer
from `FiniteSpecialUnitaryNormalization` gives a real-analytic map into the
special-unitary group, with no choice of a determinant root.
-/

open Matrix
open scoped Real Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The determinant of a finite complex matrix family with real-analytic
entries is real analytic. -/
theorem analyticAt_matrix_det_real
    {P ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [Fintype ι] [DecidableEq ι] {M : P → Matrix ι ι ℂ} {p0 : P}
    (hM : ∀ i j, AnalyticAt ℝ (fun p => M p i j) p0) :
    AnalyticAt ℝ (fun p => (M p).det) p0 := by
  have heq : (fun p => (M p).det) =
      fun p => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ i, M p (σ i) i := by
    funext p
    rw [Matrix.det_apply]
    exact Finset.sum_congr rfl (fun σ _ => by
      rw [Units.smul_def, zsmul_eq_mul])
  rw [heq]
  exact Finset.analyticAt_fun_sum _
    (fun σ _ => analyticAt_const.mul
      (Finset.analyticAt_fun_prod _ (fun i _ => hM (σ i) i)))

/-- The underlying matrix of the self-adjoint unitary exponential is real
analytic. -/
theorem analyticAt_expUnitary_coe_real
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : selfAdjoint (Matrix ι ι ℂ)) :
    AnalyticAt ℝ (fun K : selfAdjoint (Matrix ι ι ℂ) =>
      (selfAdjoint.expUnitary K : Matrix ι ι ℂ)) H := by
  let L : selfAdjoint (Matrix ι ι ℂ) →L[ℝ] Matrix ι ι ℂ :=
    (ContinuousLinearMap.lsmul ℝ ℂ) Complex.I |>.comp
      (selfAdjoint.submodule ℝ (Matrix ι ι ℂ)).subtypeL
  have hL : AnalyticAt ℝ (fun K => L K) H := L.analyticAt H
  have hexp : AnalyticAt ℝ NormedSpace.exp (L H) :=
    NormedSpace.exp_analytic (𝕂 := ℝ) (L H)
  have h := hexp.comp hL
  rw [show (fun K : selfAdjoint (Matrix ι ι ℂ) =>
      (selfAdjoint.expUnitary K : Matrix ι ι ℂ)) =
      (fun K => NormedSpace.exp (L K)) by
        funext K
        rw [selfAdjoint.expUnitary_coe]
        rfl]
  exact h

/-- The determinant of the self-adjoint unitary exponential is real
analytic. -/
theorem analyticAt_expUnitary_det_real
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : selfAdjoint (Matrix ι ι ℂ)) :
    AnalyticAt ℝ (fun K : selfAdjoint (Matrix ι ι ℂ) =>
      (selfAdjoint.expUnitary K : Matrix ι ι ℂ).det) H := by
  apply analyticAt_matrix_det_real
  intro i j
  let L : selfAdjoint (Matrix ι ι ℂ) →L[ℝ] Matrix ι ι ℂ :=
    (ContinuousLinearMap.lsmul ℝ ℂ) Complex.I |>.comp
      (selfAdjoint.submodule ℝ (Matrix ι ι ℂ)).subtypeL
  have hL : AnalyticAt ℝ (fun K => L K) H := L.analyticAt H
  have hexp : AnalyticAt ℝ NormedSpace.exp (L H) :=
    NormedSpace.exp_analytic (𝕂 := ℝ) (L H)
  let eval : Matrix ι ι ℂ →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ι → ℂ) i)
  have hentry := (eval.analyticAt (NormedSpace.exp (L H))).comp hexp
  have h := hentry.comp hL
  change AnalyticAt ℝ (fun K => eval (NormedSpace.exp (L K))) H at h
  have heq : (fun K => eval (NormedSpace.exp (L K))) =
      fun K : selfAdjoint (Matrix ι ι ℂ) =>
        NormedSpace.exp (Complex.I • (K : Matrix ι ι ℂ)) i j := by
    funext K
    simp [eval, L]
    rfl
  rw [heq] at h
  simpa only [selfAdjoint.expUnitary_coe] using h

/-- A diagonal update at one finite coordinate is an affine matrix family. -/
theorem diagonal_update_one_eq_one_add_single
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι) (z : ℂ) :
    Matrix.diagonal (Function.update (fun _ : ι => (1 : ℂ)) i0 z) =
      1 + (z - 1) • Matrix.single i0 i0 1 := by
  ext i j
  by_cases hi : i = i0
  · subst i
    by_cases hj : j = i0
    · subst j
      simp
    · simp [Ne.symm hj]
  · by_cases hij : i = j
    · subst j
      simp [Function.update, hi, Ne.symm hi]
    · simp [hij, Ne.symm hi]

/-- Substituting a real-analytic scalar function into a one-coordinate
diagonal update is real analytic. -/
theorem analyticAt_diagonal_update_one
    {P ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [Fintype ι] [DecidableEq ι] (i0 : ι) {f : P → ℂ} {p0 : P}
    (hf : AnalyticAt ℝ f p0) :
    AnalyticAt ℝ (fun p =>
      Matrix.diagonal (Function.update (fun _ : ι => (1 : ℂ)) i0 (f p))) p0 := by
  rw [show (fun p => Matrix.diagonal
      (Function.update (fun _ : ι => (1 : ℂ)) i0 (f p))) =
      fun p => 1 + (f p - 1) • Matrix.single i0 i0 1 by
    funext p
    exact diagonal_update_one_eq_one_add_single i0 (f p)]
  exact analyticAt_const.add ((hf.sub analyticAt_const).smul analyticAt_const)

/-- The explicit determinant normalization of the self-adjoint unitary
exponential is real analytic after coercion to matrices. -/
theorem analyticAt_specialUnitaryNormalize_expUnitary_coe
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι)
    (H : selfAdjoint (Matrix ι ι ℂ)) :
    AnalyticAt ℝ (fun K : selfAdjoint (Matrix ι ι ℂ) =>
      (specialUnitaryNormalize i0 (selfAdjoint.expUnitary K) : Matrix ι ι ℂ)) H := by
  have hU := analyticAt_expUnitary_coe_real H
  have hdet := analyticAt_expUnitary_det_real H
  let D : selfAdjoint (Matrix ι ι ℂ) → Matrix ι ι ℂ := fun K =>
    Matrix.diagonal (Function.update (fun _ : ι => (1 : ℂ)) i0
      (selfAdjoint.expUnitary K : Matrix ι ι ℂ).det)
  have hD : AnalyticAt ℝ D H := by
    exact analyticAt_diagonal_update_one i0 hdet
  have hstarD : AnalyticAt ℝ (fun K : selfAdjoint (Matrix ι ι ℂ) =>
      star (Matrix.diagonal
        (Function.update (fun _ : ι => (1 : ℂ)) i0
          (selfAdjoint.expUnitary K : Matrix ι ι ℂ).det))) H := by
    let starMap : Matrix ι ι ℂ →L[ℝ] Matrix ι ι ℂ :=
      (starL' ℝ : Matrix ι ι ℂ ≃L[ℝ] Matrix ι ι ℂ).toContinuousLinearMap
    have hstarMap : AnalyticAt ℝ (fun M : Matrix ι ι ℂ => starMap M) (D H) :=
      starMap.analyticAt (D H)
    have hstar := hstarMap.comp hD
    change AnalyticAt ℝ (fun K => starMap (D K)) H at hstar
    rw [show (fun K => starMap (D K)) = fun K => star (D K) by
      funext K
      change (starL' ℝ : Matrix ι ι ℂ ≃L[ℝ] Matrix ι ι ℂ) (D K) = star (D K)
      exact starL'_apply ℝ (D K)] at hstar
    simpa only [D] using hstar
  change AnalyticAt ℝ (fun K : selfAdjoint (Matrix ι ι ℂ) =>
    (selfAdjoint.expUnitary K : Matrix ι ι ℂ) *
      star (Matrix.diagonal (Function.update (fun _ : ι => (1 : ℂ)) i0
        (selfAdjoint.expUnitary K : Matrix ι ι ℂ).det))) H
  exact hU.mul hstarD

end

end GaloisForLFunctions.HTGeometry
