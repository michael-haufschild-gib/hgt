import GaloisForLFunctions.BiScaleUncertainty.Solenoidal.ToroidalFourier
import GaloisForLFunctions.HTGeometry.GaussianSchwartz
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Radial skew fields

Pullback by squared radius turns any one-dimensional Schwartz function into
an arbitrary-dimensional radial Schwartz function. Multiplying by a skew
matrix produces a toroidal field. A positive radial profile identifies
exactly the symmetric matrices as the kernel of this construction.

These are concrete fields in the Fourier-invariant space, implementing the
skew-matrix angular modes in Section 4.2 of https://arxiv.org/abs/2611.00362.
-/

noncomputable section
open scoped SchwartzMap FourierTransform LineDeriv BigOperators
open LineDeriv
namespace GaloisForLFunctions.BiScaleUncertainty.Solenoidal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A proper polynomial pullback preserves all Schwartz seminorms. -/
def radialSchwartz (f : SchwartzMap ℝ ℂ) : ScalarSchwartz ι :=
  SchwartzMap.compCLM ℂ (Function.hasTemperateGrowth_norm_sq (Space ι))
    (by
      refine ⟨1, 1, fun x => ?_⟩
      simp only [pow_one, one_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖)]
      nlinarith [sq_nonneg (‖x‖ - 1)]) f

omit [DecidableEq ι] in
@[simp] theorem radialSchwartz_apply (f : SchwartzMap ℝ ℂ) (x : Space ι) :
    radialSchwartz f x = f (‖x‖ ^ 2) := rfl

private def coordinate (i : ι) : Space ι →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp ((innerSL ℝ).flip (EuclideanSpace.single i 1))

private theorem coordinate_apply (i : ι) (x : Space ι) : coordinate i x = (x i : ℂ) := by
  change (inner ℝ x (EuclideanSpace.single i 1) : ℂ) = _
  simp [EuclideanSpace.inner_single_right]

private theorem fderiv_real_apply (f : SchwartzMap ℝ ℂ) (r t : ℝ) :
    fderiv ℝ f r t = (t : ℂ) * deriv f r := by
  simpa only [smul_eq_mul, mul_one, fderiv_apply_one_eq_deriv, Complex.real_smul] using
    (fderiv ℝ f r).map_smul t 1

/-- The coordinate derivative of a radial pullback is radial times that coordinate. -/
theorem lineDeriv_radialSchwartz (f : SchwartzMap ℝ ℂ) (i : ι) (x : Space ι) :
    (∂_{(EuclideanSpace.single i 1 : Space ι)} (radialSchwartz (ι := ι) f)) x =
      (2 * (x i : ℂ)) * deriv f (‖x‖ ^ 2) := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have h := (f.hasFDerivAt (‖x‖ ^ 2)).comp x
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  change fderiv ℝ (fun y : Space ι => f (‖y‖ ^ 2)) x _ = _
  change (fderiv ℝ (f ∘ fun y : Space ι => ‖y‖ ^ 2) x) _ = _
  rw [h.fderiv]
  simp [EuclideanSpace.inner_single_right, Complex.real_smul, mul_assoc]

/-- Product rule for a coordinate times a radial Schwartz profile. -/
theorem lineDeriv_position_radialSchwartz (f : SchwartzMap ℝ ℂ) (i j : ι)
    (x : Space ι) :
    (∂_{(EuclideanSpace.single i 1 : Space ι)} (position j (radialSchwartz f))) x =
      (if i = j then f (‖x‖ ^ 2) else 0) +
        2 * (x i : ℂ) * (x j : ℂ) * deriv f (‖x‖ ^ 2) := by
  have hf := (f.hasFDerivAt (‖x‖ ^ 2)).comp x
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hp := ((coordinate j).hasFDerivAt).mul hf
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have heq : (position j (radialSchwartz f) : Space ι → ℂ) =
      fun y => coordinate j y * f (‖y‖ ^ 2) := by
    funext y
    rw [position_apply, radialSchwartz_apply, coordinate_apply]
  rw [heq]
  change (fderiv ℝ (⇑(coordinate j) * ⇑f ∘ fun y : Space ι => ‖y‖ ^ 2) x) _ = _
  rw [hp.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    coordinate_apply, fderiv_real_apply, innerSL_apply_apply, EuclideanSpace.inner_single_right,
    one_mul, smul_eq_mul, Function.comp_apply]
  by_cases h : i = j
  · subst j
    simp
    ring
  · simp [h, Ne.symm h]
    ring

/-- Antisymmetrization gives a toroidal field without imposing conditions on the matrix. -/
def skewRadialField (A : ι → ι → ℂ) (f : SchwartzMap ℝ ℂ) : Field ι :=
  fun i => ∑ j, (A i j - A j i) • position j (radialSchwartz f)

omit [DecidableEq ι] in
private theorem skew_sum_zero (A : ι → ι → ℂ) (x : Space ι) :
    ∑ i, ∑ j, (A i j - A j i) * (x i : ℂ) * (x j : ℂ) = 0 := by
  have h : (∑ i, ∑ j, (A i j - A j i) * (x i : ℂ) * (x j : ℂ)) =
      -(∑ i, ∑ j, (A i j - A j i) * (x i : ℂ) * (x j : ℂ)) := by
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hz := congrArg (fun z : ℂ => z + ∑ i, ∑ j,
    (A i j - A j i) * (x i : ℂ) * (x j : ℂ)) h
  rw [neg_add_cancel, ← two_mul] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

/-- The field is tangent to every centered sphere. -/
theorem radialContraction_skewRadialField (A : ι → ι → ℂ) (f : SchwartzMap ℝ ℂ) :
    radialContraction (skewRadialField A f) = 0 := by
  ext x
  rw [radialContraction_pointwise]
  simp only [skewRadialField, sum_apply, smul_apply, position_apply, zero_apply,
    radialSchwartz_apply, smul_eq_mul, Finset.mul_sum]
  have h := congrArg (fun z : ℂ => z * f (‖x‖ ^ 2)) (skew_sum_zero A x)
  simp only [Finset.sum_mul, zero_mul] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Its actual divergence vanishes by skew symmetry and the radial derivative formula. -/
theorem divergence_skewRadialField (A : ι → ι → ℂ) (f : SchwartzMap ℝ ℂ) :
    divergence (skewRadialField A f) = 0 := by
  ext x
  rw [divergence_apply]
  simp only [skewRadialField, lineDerivOp_sum, lineDerivOp_smul, sum_apply,
    smul_apply, smul_eq_mul, lineDeriv_position_radialSchwartz, zero_apply]
  have hz (i j : ι) : (A i j - A j i) * (if i = j then f (‖x‖ ^ 2) else 0) = 0 := by
    split_ifs with h
    · subst j; simp
    · simp
  simp only [mul_add, hz, zero_add]
  have h := congrArg (fun z : ℂ => z * (2 * deriv f (‖x‖ ^ 2))) (skew_sum_zero A x)
  simp only [Finset.sum_mul, zero_mul] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every matrix and every Schwartz profile produce a toroidal Schwartz field. -/
theorem skewRadialField_mem_toroidal (A : ι → ι → ℂ) (f : SchwartzMap ℝ ℂ) :
    skewRadialField A f ∈ toroidal :=
  ⟨divergence_skewRadialField A f, radialContraction_skewRadialField A f⟩

/-- Evaluation on coordinate vectors recovers the skew part of the matrix. -/
theorem skewRadialField_gaussian_single (A : ι → ι → ℂ) (i j : ι) :
    skewRadialField A gaussianSchwartz i (EuclideanSpace.single j 1) =
      (A i j - A j i) * gaussianSchwartz 1 := by
  simp [skewRadialField, position_apply, PiLp.single_apply, apply_ite, ite_mul]

/-- The positive radial profile loses exactly the symmetric part of a matrix. -/
theorem skewRadialField_gaussian_eq_zero_iff (A : ι → ι → ℂ) :
    skewRadialField A gaussianSchwartz = 0 ↔ ∀ i j, A i j = A j i := by
  constructor
  · intro h i j
    have hv := congrArg (fun U : Field ι => U i (EuclideanSpace.single j 1)) h
    rw [skewRadialField_gaussian_single] at hv
    have hg : gaussianSchwartz 1 ≠ 0 := by
      simpa only [gaussianSchwartz_apply, Complex.ofReal_ne_zero] using (gaussReal_pos 1).ne'
    exact sub_eq_zero.mp ((mul_eq_zero.mp hv).resolve_right hg)
  · intro h
    funext i
    simp only [skewRadialField, h, sub_self, zero_smul, Finset.sum_const_zero, Pi.zero_apply]

/-- Every dimension at least two contains a nonzero toroidal Schwartz field. -/
theorem exists_nonzero_toroidal [Nontrivial ι] :
    ∃ U : Field ι, U ∈ toroidal ∧ U ≠ 0 := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  let A : ι → ι → ℂ := fun k l => if k = i ∧ l = j then 1 else 0
  refine ⟨skewRadialField A gaussianSchwartz, skewRadialField_mem_toroidal _ _, ?_⟩
  intro h
  have he := (skewRadialField_gaussian_eq_zero_iff A).mp h i j
  simp [A, hij, Ne.symm hij] at he

#print axioms skewRadialField_mem_toroidal
#print axioms skewRadialField_gaussian_eq_zero_iff
#print axioms exists_nonzero_toroidal
end GaloisForLFunctions.BiScaleUncertainty.Solenoidal
