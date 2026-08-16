import GaloisForLFunctions.HTGeometry.SkewConjugatedRiccatiGramian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The derivative of the inverse of a matrix curve

Cramer's rule expresses every entry of `A⁻¹` as a quotient of two determinants, hence as a
rational function of the entries of `A`.  An entrywise differentiable matrix curve with invertible
value therefore has an entrywise differentiable inverse, and differentiating `A⁻¹A = 1` identifies
its derivative as `-A⁻¹A'A⁻¹`.

Everything is entrywise, so no normed structure on the matrix space is used.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {n : ℕ}

/-! ## Differentiability of finite sums and products -/

theorem differentiableAt_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) {y : ℝ}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (f i) y) :
    DifferentiableAt ℝ (fun v => ∑ i ∈ s, f i v) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (h a (by simp)).add (ih fun i hi => h i (by simp [hi]))

theorem differentiableAt_finsetProd {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) {y : ℝ}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (f i) y) :
    DifferentiableAt ℝ (fun v => ∏ i ∈ s, f i v) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (h a (by simp)).mul (ih fun i hi => h i (by simp [hi]))

/-! ## Differentiability of determinant, adjugate and inverse -/

theorem differentiableAt_det_of_entries {M : ℝ → Matrix (Fin n) (Fin n) ℝ} {y : ℝ}
    (h : ∀ i j, DifferentiableAt ℝ (fun v => M v i j) y) :
    DifferentiableAt ℝ (fun v => (M v).det) y := by
  have hfun : (fun v => (M v).det)
      = fun v => ∑ σ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, M v (σ i) i := by
    funext v
    exact Matrix.det_apply' (M v)
  rw [hfun]
  refine differentiableAt_finsetSum _ _ fun σ _ => ?_
  exact (differentiableAt_finsetProd _ _ fun i _ => h (σ i) i).const_mul _

theorem differentiableAt_adjugate_of_entries {M : ℝ → Matrix (Fin n) (Fin n) ℝ} {y : ℝ}
    (h : ∀ i j, DifferentiableAt ℝ (fun v => M v i j) y) (i j : Fin n) :
    DifferentiableAt ℝ (fun v => (M v).adjugate i j) y := by
  have hfun : (fun v => (M v).adjugate i j)
      = fun v => ((M v).updateRow j (Pi.single i 1)).det := by
    funext v
    exact Matrix.adjugate_apply (M v) i j
  rw [hfun]
  refine differentiableAt_det_of_entries fun k l => ?_
  by_cases hk : k = j
  · have : (fun v => ((M v).updateRow j (Pi.single i 1)) k l)
        = fun _ : ℝ => (Pi.single i (1 : ℝ) : Fin n → ℝ) l := by
      funext v
      simp [Matrix.updateRow_apply, hk]
    rw [this]
    exact differentiableAt_const _
  · have : (fun v => ((M v).updateRow j (Pi.single i 1)) k l) = fun v => M v k l := by
      funext v
      simp [Matrix.updateRow_apply, hk]
    rw [this]
    exact h k l

theorem differentiableAt_inv_of_entries {M : ℝ → Matrix (Fin n) (Fin n) ℝ} {y : ℝ}
    (h : ∀ i j, DifferentiableAt ℝ (fun v => M v i j) y) (hdet : (M y).det ≠ 0) (i j : Fin n) :
    DifferentiableAt ℝ (fun v => (M v)⁻¹ i j) y := by
  have hfun : (fun v => (M v)⁻¹ i j)
      = fun v => ((M v).det)⁻¹ * (M v).adjugate i j := by
    funext v
    rw [Matrix.inv_def]
    simp only [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  rw [hfun]
  exact DifferentiableAt.mul (DifferentiableAt.inv (differentiableAt_det_of_entries h) hdet)
    (differentiableAt_adjugate_of_entries h i j)

/-! ## The derivative of the inverse curve -/

/-- **The inverse curve of an invertible differentiable matrix curve is differentiable, with the
Riccati derivative `-A⁻¹A'A⁻¹`.** -/
theorem matrixHasDerivAt_inv {J : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {J' : Matrix (Fin n) (Fin n) ℝ} {y : ℝ} (hJ : MatrixHasDerivAt J J' y)
    (hdet : (J y).det ≠ 0) :
    MatrixHasDerivAt (fun v => (J v)⁻¹) (-((J y)⁻¹ * J' * (J y)⁻¹)) y := by
  have hent : ∀ i j, DifferentiableAt ℝ (fun v => J v i j) y := fun i j => (hJ i j).differentiableAt
  have hinvdiff : ∀ i j, DifferentiableAt ℝ (fun v => (J v)⁻¹ i j) y :=
    differentiableAt_inv_of_entries hent hdet
  set W' : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun i j => deriv (fun v => (J v)⁻¹ i j) y with hW'
  have hWd : MatrixHasDerivAt (fun v => (J v)⁻¹) W' y := fun i j => (hinvdiff i j).hasDerivAt
  -- the product is eventually the identity
  have hdetcont : ContinuousAt (fun v => (J v).det) y :=
    (differentiableAt_det_of_entries hent).continuousAt
  have hev : ∀ᶠ v in nhds y, (J v)⁻¹ * J v = 1 := by
    filter_upwards [hdetcont.eventually_ne hdet] with v hv
    exact Matrix.nonsing_inv_mul (J v) (isUnit_iff_ne_zero.mpr hv)
  have hzero : MatrixHasDerivAt (fun v => (J v)⁻¹ * J v) 0 y := by
    intro i j
    have hcst : HasDerivAt (fun _ : ℝ => (1 : Matrix (Fin n) (Fin n) ℝ) i j) 0 y :=
      hasDerivAt_const y _
    refine hcst.congr_of_eventuallyEq ?_
    filter_upwards [hev] with v hv
    rw [hv]
  have huniq : W' * J y + (J y)⁻¹ * J' = 0 :=
    Matrix.ext fun i j => ((hWd.mul hJ) i j).unique (hzero i j)
  have hinvJ : J y * (J y)⁻¹ = 1 := Matrix.mul_nonsing_inv (J y) (isUnit_iff_ne_zero.mpr hdet)
  have hval : W' = -((J y)⁻¹ * J' * (J y)⁻¹) := by
    have h1 : W' * J y = -((J y)⁻¹ * J') := by
      have := huniq
      rw [add_eq_zero_iff_eq_neg] at this
      exact this
    calc W' = W' * (J y * (J y)⁻¹) := by rw [hinvJ, Matrix.mul_one]
      _ = (W' * J y) * (J y)⁻¹ := by rw [Matrix.mul_assoc]
      _ = -((J y)⁻¹ * J' * (J y)⁻¹) := by rw [h1, Matrix.neg_mul]
  rw [← hval]
  exact hWd

end GaloisForLFunctions.HTGeometry
