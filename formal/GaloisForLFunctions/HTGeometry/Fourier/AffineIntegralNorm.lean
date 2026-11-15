import GaloisForLFunctions.HTGeometry.AffineLatticePoisson

/-!
# Affine invariance of the Fourier integral norm

The inverse Fourier integral norm is unchanged by invertible affine changes
of frequency coordinates. Translation contributes a unit phase; the linear
Jacobian cancels the determinant of the inverse adjoint.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace GaloisForLFunctions.HTGeometry.IntegerLatticePoisson

variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- A real adjoint has the same determinant as the original endomorphism. -/
theorem det_real_adjoint (f : E →ₗ[ℝ] E) : f.adjoint.det = f.det := by
  classical
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun ι ℝ).toBasis,
    LinearMap.toMatrix_adjoint, Matrix.det_conjTranspose, star_trivial,
    LinearMap.det_toMatrix]

theorem det_inverseAdjointEquiv (B : E ≃L[ℝ] E) :
    LinearMap.det (inverseAdjointEquiv B : E →ₗ[ℝ] E) =
      LinearMap.det (B.symm : E →ₗ[ℝ] E) := by
  change (ContinuousLinearMap.adjoint B.symm.toContinuousLinearMap).toLinearMap.det = _
  rw [← ContinuousLinearMap.adjoint_toLinearMap, det_real_adjoint]
  rfl

/-- The two Jacobian factors in affine Fourier covariance are reciprocal. -/
theorem latticeScale_mul_inverseAdjoint (B : E ≃L[ℝ] E) :
    latticeScale B * latticeScale (inverseAdjointEquiv B) = 1 := by
  have hc : (B : E →ₗ[ℝ] E).comp (B.symm : E →ₗ[ℝ] E) = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact B.apply_symm_apply x
  have hd := congrArg (fun T : E →ₗ[ℝ] E => T.det) hc
  rw [LinearMap.det_comp, LinearMap.det_id] at hd
  unfold latticeScale
  rw [det_inverseAdjointEquiv, ← mul_inv, ← abs_mul, hd, abs_one, inv_one]

/-- Change of variables for a real-valued integral, including nonintegrable functions. -/
theorem integral_real_comp_linearEquiv (B : E ≃L[ℝ] E) (g : E → ℝ) :
    (∫ x, g (B x)) = latticeScale B * ∫ y, g y := by
  have hmap : Measure.map B (volume : Measure E) =
      ENNReal.ofReal (latticeScale B) • volume := by
    simpa [latticeScale] using
      (Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure E)
        (LinearEquiv.isUnit_det' B.toLinearEquiv).ne_zero)
  calc
    _ = ∫ y, g y ∂Measure.map B volume :=
      (integral_map_equiv B.toHomeomorph.toMeasurableEquiv g).symm
    _ = _ := by
      rw [hmap, integral_smul_measure,
        ENNReal.toReal_ofReal (latticeScale_pos B).le, smul_eq_mul]

/-- Inverse Fourier covariance has the same inverse-adjoint frequency map. -/
theorem fourierInv_comp_linearEquiv (f : E → ℂ) (B : E ≃L[ℝ] E) (w : E) :
    (𝓕⁻ (fun x => f (B x))) w =
      latticeScale B • (𝓕⁻ f) (inverseAdjointEquiv B w) := by
  rw [Real.fourierInv_eq_fourier_neg, fourier_comp_linearEquiv,
    Real.fourierInv_eq_fourier_neg]
  simp only [map_neg, inverseAdjointEquiv_apply]

/-- Translating frequency coordinates preserves the inverse Fourier modulus pointwise. -/
theorem norm_fourierInv_comp_add (f : E → ℂ) (a w : E) :
    ‖(𝓕⁻ (fun x => f (x + a))) w‖ = ‖(𝓕⁻ f) w‖ := by
  rw [Real.fourierInv_eq_fourier_neg, fourier_comp_add,
    Real.fourierInv_eq_fourier_neg]
  simp [Complex.norm_exp]

/-- The Fourier Jacobian cancels after integrating over the dual coordinates. -/
theorem integral_norm_fourierInv_comp_linearEquiv (f : E → ℂ) (B : E ≃L[ℝ] E) :
    (∫ w, ‖(𝓕⁻ (fun x => f (B x))) w‖) = ∫ w, ‖(𝓕⁻ f) w‖ := by
  calc
    _ = ∫ w, latticeScale B * ‖(𝓕⁻ f) (inverseAdjointEquiv B w)‖ := by
      apply integral_congr_ae
      filter_upwards [] with w
      rw [fourierInv_comp_linearEquiv, norm_smul, Real.norm_eq_abs,
        abs_of_pos (latticeScale_pos B)]
    _ = latticeScale B *
        (latticeScale (inverseAdjointEquiv B) * ∫ w, ‖(𝓕⁻ f) w‖) := by
      rw [integral_const_mul]
      exact congrArg (latticeScale B * ·)
        (integral_real_comp_linearEquiv (inverseAdjointEquiv B) (fun w : E => ‖(𝓕⁻ f) w‖))
    _ = _ := by rw [← mul_assoc, latticeScale_mul_inverseAdjoint, one_mul]

/-- Every invertible affine frequency change preserves the inverse Fourier integral norm. -/
theorem integral_norm_fourierInv_comp_affine (f : E → ℂ) (B : E ≃L[ℝ] E) (a : E) :
    (∫ w, ‖(𝓕⁻ (fun x => f (a + B x))) w‖) = ∫ w, ‖(𝓕⁻ f) w‖ := by
  have he : (fun x => f (a + B x)) = (fun x => (fun y => f (y + a)) (B x)) := by
    funext x
    rw [add_comm a]
  rw [he, integral_norm_fourierInv_comp_linearEquiv (fun y => f (y + a)) B]
  apply integral_congr_ae
  filter_upwards [] with w
  exact norm_fourierInv_comp_add f a w


end GaloisForLFunctions.HTGeometry.IntegerLatticePoisson
