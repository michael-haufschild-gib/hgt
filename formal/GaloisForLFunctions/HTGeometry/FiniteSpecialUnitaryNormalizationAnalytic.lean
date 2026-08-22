import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryExponentialAnalytic

/-!
# Analytic determinant normalization of finite unitary families

The explicit determinant normalizer preserves real analyticity of arbitrary
finite unitary matrix families.  The translated exponential specialization is
the chart-level form needed for Haar-null transport.
-/

open Matrix
open scoped Real Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Determinant normalization preserves real analyticity after coercion to
matrices. -/
theorem analyticAt_specialUnitaryNormalize_coe_of_analyticAt
    {P ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [Fintype ι] [DecidableEq ι] (i0 : ι)
    {F : P → Matrix.unitaryGroup ι ℂ} {p0 : P}
    (hF : AnalyticAt ℝ (fun p => (F p : Matrix ι ι ℂ)) p0) :
    AnalyticAt ℝ (fun p =>
      (specialUnitaryNormalize i0 (F p) : Matrix ι ι ℂ)) p0 := by
  have hdet : AnalyticAt ℝ (fun p => (F p : Matrix ι ι ℂ).det) p0 := by
    apply analyticAt_matrix_det_real
    intro i j
    let eval : Matrix ι ι ℂ →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) j).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ι → ℂ) i)
    have h := AnalyticAt.comp
      (f := fun p => (F p : Matrix ι ι ℂ))
      (g := fun M : Matrix ι ι ℂ => eval M)
      (x := p0) (eval.analyticAt (F p0 : Matrix ι ι ℂ)) hF
    change AnalyticAt ℝ (fun p => eval (F p : Matrix ι ι ℂ)) p0
    exact h
  let D : P → Matrix ι ι ℂ := fun p =>
    Matrix.diagonal (Function.update (fun _ : ι => (1 : ℂ)) i0
      (F p : Matrix ι ι ℂ).det)
  have hD : AnalyticAt ℝ D p0 := by
    exact analyticAt_diagonal_update_one i0 hdet
  have hstarD : AnalyticAt ℝ (fun p => star (D p)) p0 := by
    let starMap : Matrix ι ι ℂ →L[ℝ] Matrix ι ι ℂ :=
      (starL' ℝ : Matrix ι ι ℂ ≃L[ℝ] Matrix ι ι ℂ).toContinuousLinearMap
    have hstarMap : AnalyticAt ℝ (fun M : Matrix ι ι ℂ => starMap M) (D p0) :=
      starMap.analyticAt (D p0)
    have hstar := hstarMap.comp hD
    change AnalyticAt ℝ (fun p => starMap (D p)) p0 at hstar
    rw [show (fun p => starMap (D p)) = fun p => star (D p) by
      funext p
      change (starL' ℝ : Matrix ι ι ℂ ≃L[ℝ] Matrix ι ι ℂ) (D p) = star (D p)
      exact starL'_apply ℝ (D p)] at hstar
    exact hstar
  change AnalyticAt ℝ (fun p =>
    (F p : Matrix ι ι ℂ) * star (D p)) p0
  exact hF.mul hstarD

/-- Determinant normalization of every left-translated finite-unitary
exponential chart is real analytic. -/
theorem analyticAt_specialUnitaryNormalize_mul_expUnitary_coe
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i0 : ι) (U : Matrix.unitaryGroup ι ℂ)
    (H : selfAdjoint (Matrix ι ι ℂ)) :
    AnalyticAt ℝ (fun K : selfAdjoint (Matrix ι ι ℂ) =>
      (specialUnitaryNormalize i0 (U * selfAdjoint.expUnitary K) :
        Matrix ι ι ℂ)) H := by
  apply analyticAt_specialUnitaryNormalize_coe_of_analyticAt i0
  have hprod : AnalyticAt ℝ (fun K : selfAdjoint (Matrix ι ι ℂ) =>
      (U : Matrix ι ι ℂ) * (selfAdjoint.expUnitary K : Matrix ι ι ℂ)) H :=
    analyticAt_const.mul (analyticAt_expUnitary_coe_real H)
  simpa using hprod

end

end GaloisForLFunctions.HTGeometry
