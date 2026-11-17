import GaloisForLFunctions.HTGeometry.EuclideanCompactStokes

/-!
# Compact Jacobian minors are null Lagrangians

Integration by parts and symmetry of second derivatives cancel the
integral of every two-direction Jacobian minor. Consequently adding
the gradient of a compactly supported C² map preserves the integral
of a two-by-two determinant relative to an affine background.
The determinant itself is not convex: this is a concrete quasiconvex
mechanism distinct from convex tangent support.
-/

open MeasureTheory Set
namespace GaloisForLFunctions.HilbertMetric.Geometry.CompactJacobian
open HTGeometry
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev CompactC2 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  {u : E → ℝ // ContDiff ℝ 2 u ∧ HasCompactSupport u}

def slope (u : E → ℝ) (w : E) (x : E) : ℝ := fderiv ℝ u x w

private theorem slope_contDiff (u : CompactC2 E) (w : E) : ContDiff ℝ 1 (slope u.val w) :=
  (u.property.1.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

private theorem slope_compact {u : E → ℝ} (hu : HasCompactSupport u) (w : E) :
    HasCompactSupport (slope u w) :=
  (hu.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ => L w) rfl

private theorem second_slope_continuous (u : CompactC2 E) (s t : E) :
    Continuous (slope (slope u.val t) s) :=
  ((slope_contDiff u t).continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- Mixed directional derivatives commute for the actual C² test function. -/
theorem slope_comm (u : CompactC2 E) (s t x : E) :
    slope (slope u.val t) s x = slope (slope u.val s) t x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u.val) x :=
    (u.property.1.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x
  have he (v w : E) : slope (slope u.val w) v x =
      fderiv ℝ (fderiv ℝ u.val) x v w := by
    unfold slope
    rw [fderiv_clm_apply hd (differentiableAt_const w)]
    simp
  rw [he, he]
  exact (u.property.1.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)) s t

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

private theorem slope_product_integrable (u v : CompactC2 E) (s t : E) :
    Integrable (fun x => slope u.val s x * slope v.val t x) μ :=
  ((slope_contDiff u s).continuous.mul (slope_contDiff v t).continuous).integrable_of_hasCompactSupport
    (slope_compact u.property.2 s).mul_right

private theorem integral_slope_product (u v : CompactC2 E) (s t : E) :
    (∫ x, slope u.val s x * slope v.val t x ∂μ) =
      -(∫ x, u.val x * slope (slope v.val t) s x ∂μ) := by
  have hsecond : Integrable (fun x => u.val x * slope (slope v.val t) s x) μ :=
    (u.property.1.continuous.mul (second_slope_continuous v s t)).integrable_of_hasCompactSupport
      u.property.2.mul_right
  have hproduct : Integrable (fun x => u.val x * slope v.val t x) μ :=
    (u.property.1.continuous.mul (slope_contDiff v t).continuous).integrable_of_hasCompactSupport
      u.property.2.mul_right
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := μ) (f := u.val) (g := slope v.val t) (v := s)
    (slope_product_integrable μ u v s t) hsecond hproduct
    (fun x _ => u.property.1.differentiable (by norm_num) x)
    (fun x _ => (slope_contDiff v t).differentiable one_ne_zero x)
  change (∫ x, u.val x * slope (slope v.val t) s x ∂μ) =
    -(∫ x, slope u.val s x * slope v.val t x ∂μ) at h
  linarith only [h]

/-- Swapping the two derivative directions preserves the full integrated Jacobian product. -/
theorem integral_slope_product_symm (u v : CompactC2 E) (s t : E) :
    (∫ x, slope u.val s x * slope v.val t x ∂μ) =
      ∫ x, slope u.val t x * slope v.val s x ∂μ := by
  rw [integral_slope_product, integral_slope_product]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => congrArg (fun z : ℝ => u.val x * z)
    (slope_comm v s t x)

def minor (u v : CompactC2 E) (s t x : E) : ℝ :=
  slope u.val s x * slope v.val t x - slope u.val t x * slope v.val s x

/-- Every compact two-direction Jacobian minor has integral zero. -/
theorem integral_minor (u v : CompactC2 E) (s t : E) : ∫ x, minor u v s t x ∂μ = 0 := by
  change (∫ x, slope u.val s x * slope v.val t x - slope u.val t x * slope v.val s x ∂μ) = 0
  rw [integral_sub (slope_product_integrable μ u v s t)
    (slope_product_integrable μ u v t s), integral_slope_product_symm μ u v s t, sub_self]

private theorem slope_integrable (u : CompactC2 E) (s : E) : Integrable (slope u.val s) μ :=
  (slope_contDiff u s).continuous.integrable_of_hasCompactSupport (slope_compact u.property.2 s)

private theorem integral_slope (u : CompactC2 E) (s : E) : ∫ x, slope u.val s x ∂μ = 0 :=
  integral_fderiv_apply_eq_zero_of_hasCompactSupport μ
    (u.property.1.of_le (by norm_num)) u.property.2 s

/-- The genuine two-row, two-direction Jacobian matrix. -/
def jacobian (u v : CompactC2 E) (s t x : E) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![slope u.val s x, slope u.val t x; slope v.val s x, slope v.val t x]

private theorem determinant_expansion (A : Matrix (Fin 2) (Fin 2) ℝ)
    (u v : CompactC2 E) (s t x : E) :
    (A + jacobian u v s t x).det - A.det =
      A 0 0 * slope v.val t x + A 1 1 * slope u.val s x -
        A 0 1 * slope v.val s x - A 1 0 * slope u.val t x + minor u v s t x := by
  simp only [Matrix.det_fin_two, Matrix.add_apply]
  change (A 0 0 + slope u.val s x) * (A 1 1 + slope v.val t x) -
      (A 0 1 + slope u.val t x) * (A 1 0 + slope v.val s x) -
      (A 0 0 * A 1 1 - A 0 1 * A 1 0) = _
  unfold minor
  ring

/-- The determinant difference is integrable even on the full Haar space. -/
theorem determinant_excess_integrable (A : Matrix (Fin 2) (Fin 2) ℝ)
    (u v : CompactC2 E) (s t : E) :
    Integrable (fun x => (A + jacobian u v s t x).det - A.det) μ := by
  have h1 := (slope_integrable μ v t).const_mul (A 0 0)
  have h2 := (slope_integrable μ u s).const_mul (A 1 1)
  have h3 := (slope_integrable μ v s).const_mul (A 0 1)
  have h4 := (slope_integrable μ u t).const_mul (A 1 0)
  have hm : Integrable (minor u v s t) μ :=
    (slope_product_integrable μ u v s t).sub (slope_product_integrable μ u v t s)
  simp_rw [determinant_expansion]
  exact (((h1.add h2).sub h3).sub h4).add hm

/-- Determinant action is unchanged by every compact C² gradient perturbation. -/
theorem integral_determinant_excess (A : Matrix (Fin 2) (Fin 2) ℝ)
    (u v : CompactC2 E) (s t : E) :
    (∫ x, (A + jacobian u v s t x).det - A.det ∂μ) = 0 := by
  have h1 := (slope_integrable μ v t).const_mul (A 0 0)
  have h2 := (slope_integrable μ u s).const_mul (A 1 1)
  have h3 := (slope_integrable μ v s).const_mul (A 0 1)
  have h4 := (slope_integrable μ u t).const_mul (A 1 0)
  have hm : Integrable (minor u v s t) μ :=
    (slope_product_integrable μ u v s t).sub (slope_product_integrable μ u v t s)
  have h12 : Integrable (fun x => A 0 0 * slope v.val t x + A 1 1 * slope u.val s x) μ := h1.add h2
  have h123 : Integrable (fun x => A 0 0 * slope v.val t x + A 1 1 * slope u.val s x -
      A 0 1 * slope v.val s x) μ := h12.sub h3
  have h1234 : Integrable (fun x => A 0 0 * slope v.val t x + A 1 1 * slope u.val s x -
      A 0 1 * slope v.val s x - A 1 0 * slope u.val t x) μ := h123.sub h4
  simp_rw [determinant_expansion]
  rw [integral_add h1234 hm,
    integral_sub h123 h4, integral_sub h12 h3,
    integral_add h1 h2, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_slope, integral_slope,
    integral_slope, integral_slope, integral_minor]
  ring

/-- The determinant is not convex, despite its exact compact-variation invariance. -/
theorem determinant_not_convex :
    ¬ ConvexOn ℝ univ (fun A : Matrix (Fin 2) (Fin 2) ℝ => A.det) := by
  intro h
  let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
  have hc : ((1 / 2 : ℝ) • A + (1 / 2 : ℝ) • (-A)).det ≤
      (1 / 2 : ℝ) * A.det + (1 / 2 : ℝ) * (-A).det :=
    h.2 (mem_univ A) (mem_univ (-A)) (by norm_num) (by norm_num) (by norm_num)
  norm_num [A, Matrix.det_fin_two, Matrix.add_apply, Matrix.smul_apply,
    Matrix.neg_apply] at hc

#print axioms integral_minor
#print axioms integral_determinant_excess
#print axioms determinant_not_convex
end
end GaloisForLFunctions.HilbertMetric.Geometry.CompactJacobian
