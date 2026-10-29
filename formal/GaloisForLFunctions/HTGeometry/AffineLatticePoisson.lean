import GaloisForLFunctions.HTGeometry.SchwartzPoissonSummation
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Poisson summation on affine lattices

An invertible real linear change of variables rescales the Fourier integral by
the inverse absolute determinant and transforms frequency by the inverse adjoint.
Translation contributes an exponential phase. Applying these identities to
Schwartz functions gives Poisson summation on every affine full lattice, with
absolute convergence on both the physical and dual lattices.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace GaloisForLFunctions.HTGeometry.IntegerLatticePoisson

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι
local notation "Z" => ι → ℤ

/-- The inverse covolume of a lattice parametrized by `B`. -/
def latticeScale (B : E ≃L[ℝ] E) : ℝ := |LinearMap.det (B : E →ₗ[ℝ] E)|⁻¹

omit [Fintype ι] in
theorem latticeScale_pos (B : E ≃L[ℝ] E) : 0 < latticeScale B := by
  unfold latticeScale
  exact inv_pos.mpr (abs_pos.mpr (LinearEquiv.isUnit_det' B.toLinearEquiv).ne_zero)

/-- Frequencies transform by the adjoint of the inverse lattice map. -/
def inverseAdjoint (B : E ≃L[ℝ] E) : E →L[ℝ] E :=
  ContinuousLinearMap.adjoint B.symm.toContinuousLinearMap

/-- The dual lattice is parametrized by the adjoint of the inverse lattice map. -/
def inverseAdjointEquiv (B : E ≃L[ℝ] E) : E ≃L[ℝ] E where
  toLinearEquiv :=
    { toLinearMap := (inverseAdjoint B).toLinearMap
      invFun := ContinuousLinearMap.adjoint B.toContinuousLinearMap
      left_inv x := by
        have h : B.symm.toContinuousLinearMap.comp B.toContinuousLinearMap =
            ContinuousLinearMap.id ℝ E := by
          apply ContinuousLinearMap.ext
          intro y
          exact B.symm_apply_apply y
        have hh := congrArg (fun T : E →L[ℝ] E => ContinuousLinearMap.adjoint T) h
        rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] at hh
        exact congrArg (fun T : E →L[ℝ] E => T x) hh
      right_inv x := by
        have h : B.toContinuousLinearMap.comp B.symm.toContinuousLinearMap =
            ContinuousLinearMap.id ℝ E := by
          apply ContinuousLinearMap.ext
          intro y
          exact B.apply_symm_apply y
        have hh := congrArg (fun T : E →L[ℝ] E => ContinuousLinearMap.adjoint T) h
        rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] at hh
        exact congrArg (fun T : E →L[ℝ] E => T x) hh }
  continuous_toFun := (inverseAdjoint B).continuous
  continuous_invFun := (ContinuousLinearMap.adjoint B.toContinuousLinearMap).continuous

@[simp] theorem inverseAdjointEquiv_apply (B : E ≃L[ℝ] E) (x : E) :
    inverseAdjointEquiv B x = inverseAdjoint B x := rfl

@[simp] theorem inverseAdjointEquiv_symm_toContinuousLinearMap (B : E ≃L[ℝ] E) :
    (inverseAdjointEquiv B).symm.toContinuousLinearMap =
      ContinuousLinearMap.adjoint B.toContinuousLinearMap := rfl

theorem inverseAdjointEquiv_involutive (B : E ≃L[ℝ] E) :
    inverseAdjointEquiv (inverseAdjointEquiv B) = B := by
  apply ContinuousLinearEquiv.ext
  funext x
  exact congrArg (fun T : E →L[ℝ] E => T x)
    (ContinuousLinearMap.adjoint_adjoint B.toContinuousLinearMap)


/-- Invertible linear changes of variables preserve integrability. -/
theorem integrable_comp_linearEquiv {f : E → ℂ} (hf : Integrable f) (B : E ≃L[ℝ] E) :
    Integrable (fun x => f (B x)) := by
  have hmap : Measure.map B (volume : Measure E) =
      ENNReal.ofReal (latticeScale B) • volume := by
    simpa [latticeScale] using
      (Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure E)
        (LinearEquiv.isUnit_det' B.toLinearEquiv).ne_zero)
  apply (integrable_map_equiv B.toHomeomorph.toMeasurableEquiv f).mp
  change Integrable f (Measure.map B volume)
  rw [hmap]
  exact hf.smul_measure ENNReal.ofReal_ne_top

theorem integral_comp_linearEquiv (B : E ≃L[ℝ] E) (g : E → ℂ) :
    (∫ x, g (B x)) = latticeScale B • ∫ y, g y := by
  have hmap : Measure.map B (volume : Measure E) =
      ENNReal.ofReal (latticeScale B) • volume := by
    simpa [latticeScale] using
      (Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure E)
        (LinearEquiv.isUnit_det' B.toLinearEquiv).ne_zero)
  calc
    _ = ∫ y, g y ∂Measure.map B volume :=
      (integral_map_equiv B.toHomeomorph.toMeasurableEquiv g).symm
    _ = _ := by
      rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (by
        unfold latticeScale
        positivity)]

/-- Fourier covariance under an arbitrary invertible real linear change of variables. -/
theorem fourier_comp_linearEquiv (f : E → ℂ) (B : E ≃L[ℝ] E) (w : E) :
    (𝓕 (fun x => f (B x))) w =
      latticeScale B • (𝓕 f) (inverseAdjoint B w) := by
  let g : E → ℂ := fun y =>
    Complex.exp ((-2 * Real.pi * inner ℝ y (inverseAdjoint B w) : ℝ) * Complex.I) * f y
  have hinner (x : E) : inner ℝ (B x) (inverseAdjoint B w) = inner ℝ x w := by
    rw [inverseAdjoint, ContinuousLinearMap.adjoint_inner_right]
    change inner ℝ (B.symm (B x)) w = inner ℝ x w
    rw [B.symm_apply_apply]
  simp only [Real.fourier_eq', smul_eq_mul]
  change (∫ x, Complex.exp ((-2 * Real.pi * inner ℝ x w : ℝ) * Complex.I) * f (B x)) =
    latticeScale B • ∫ y, g y
  calc
    _ = ∫ x, g (B x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [g, hinner]
    _ = _ := integral_comp_linearEquiv B g

/-- Translation multiplies the Fourier transform by a phase. -/
theorem fourier_comp_add (f : E → ℂ) (a w : E) :
    (𝓕 (fun x => f (x + a))) w =
      Complex.exp ((2 * Real.pi * inner ℝ a w : ℝ) * Complex.I) * (𝓕 f) w := by
  let phase : ℂ := Complex.exp ((2 * Real.pi * inner ℝ a w : ℝ) * Complex.I)
  let kernel : E → ℂ := fun x =>
    Complex.exp ((-2 * Real.pi * inner ℝ x w : ℝ) * Complex.I)
  have hphase (x : E) : kernel x = phase * kernel (x + a) := by
    dsimp only [phase, kernel]
    rw [← Complex.exp_add]
    congr 1
    rw [inner_add_left]
    push_cast
    ring
  simp only [Real.fourier_eq', smul_eq_mul]
  change (∫ x, kernel x * f (x + a)) = phase * ∫ y, kernel y * f y
  calc
    _ = ∫ x, phase * (kernel (x + a) * f (x + a)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hphase, mul_assoc]
    _ = phase * ∫ x, kernel (x + a) * f (x + a) := integral_const_mul _ _
    _ = _ := congrArg (phase * ·) (integral_add_right_eq_self (fun x => kernel x * f x) a)

theorem fourier_schwartz_comp_linearEquiv (f : SchwartzMap E ℂ) (B : E ≃L[ℝ] E) (w : E) :
    (𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ B f)) w =
      latticeScale B • (𝓕 f) (inverseAdjoint B w) := by
  change (𝓕 (fun x => f (B x))) w = latticeScale B • (𝓕 (f : E → ℂ)) (inverseAdjoint B w)
  exact fourier_comp_linearEquiv (f : E → ℂ) B w

theorem fourier_schwartz_comp_add (f : SchwartzMap E ℂ) (a w : E) :
    (𝓕 (f.compSubConstCLM ℂ (-a))) w =
      Complex.exp ((2 * Real.pi * inner ℝ a w : ℝ) * Complex.I) * (𝓕 f) w := by
  change (𝓕 (fun x => f (x - (-a)))) w =
    Complex.exp ((2 * Real.pi * inner ℝ a w : ℝ) * Complex.I) * (𝓕 (f : E → ℂ)) w
  simpa only [sub_neg_eq_add] using fourier_comp_add (f : E → ℂ) a w

/-- Schwartz functions are absolutely summable on every affine full lattice. -/
theorem summable_norm_affine_lattice (f : SchwartzMap E ℂ) (B : E ≃L[ℝ] E) (a : E) :
    Summable (fun n : Z => ‖f (B (euclideanIntegerPoint n) + a)‖) := by
  have h := summable_norm_integerPoint
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ B (f.compSubConstCLM ℂ (-a)))
  simpa only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    SchwartzMap.compSubConstCLM_apply, Function.comp_apply, sub_neg_eq_add] using h

/-- The Fourier transform is absolutely summable on the dual lattice. -/
theorem summable_norm_dual_lattice (f : SchwartzMap E ℂ) (B : E ≃L[ℝ] E) :
    Summable (fun k : Z => ‖(𝓕 f) (inverseAdjoint B (euclideanIntegerPoint k))‖) := by
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ B f
  have h := (summable_norm_integerPoint (𝓕 g)).mul_left (latticeScale B)⁻¹
  refine h.congr fun k => ?_
  dsimp only [g]
  rw [fourier_schwartz_comp_linearEquiv, norm_smul, Real.norm_eq_abs,
    abs_of_pos (latticeScale_pos B), ← mul_assoc, inv_mul_cancel₀ (latticeScale_pos B).ne',
    one_mul]

/-- Translation phases preserve absolute summability on the dual lattice. -/
theorem summable_norm_affine_dual (f : SchwartzMap E ℂ) (B : E ≃L[ℝ] E) (a : E) :
    Summable (fun k : Z =>
      ‖Complex.exp ((2 * Real.pi * inner ℝ a
        (inverseAdjoint B (euclideanIntegerPoint k)) : ℝ) * Complex.I) *
          (𝓕 f) (inverseAdjoint B (euclideanIntegerPoint k))‖) := by
  simpa [norm_mul, Complex.norm_exp] using summable_norm_dual_lattice f B

/-- Poisson summation on an affine full lattice, with its determinant and dual frequencies. -/
theorem schwartz_poisson_affine (f : SchwartzMap E ℂ) (B : E ≃L[ℝ] E) (a : E) :
    (∑' n : Z, f (B (euclideanIntegerPoint n) + a)) =
      latticeScale B • ∑' k : Z,
        Complex.exp ((2 * Real.pi * inner ℝ a
          (inverseAdjoint B (euclideanIntegerPoint k)) : ℝ) * Complex.I) *
            (𝓕 f) (inverseAdjoint B (euclideanIntegerPoint k)) := by
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ B (f.compSubConstCLM ℂ (-a))
  calc
    _ = ∑' n : Z, g (euclideanIntegerPoint n) := by
      simp only [g, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
        SchwartzMap.compSubConstCLM_apply, Function.comp_apply, sub_neg_eq_add]
    _ = ∑' k : Z, (𝓕 g) (euclideanIntegerPoint k) := schwartz_poisson g
    _ = ∑' k : Z, latticeScale B •
        (Complex.exp ((2 * Real.pi * inner ℝ a
          (inverseAdjoint B (euclideanIntegerPoint k)) : ℝ) * Complex.I) *
            (𝓕 f) (inverseAdjoint B (euclideanIntegerPoint k))) := by
      apply tsum_congr
      intro k
      dsimp only [g]
      rw [fourier_schwartz_comp_linearEquiv, fourier_schwartz_comp_add]
    _ = _ := by simp only [Complex.real_smul, tsum_mul_left]

end GaloisForLFunctions.HTGeometry.IntegerLatticePoisson
