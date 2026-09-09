import GaloisForLFunctions.HTGeometry.ComplexMetricActionCurrent

set_option autoImplicit false
namespace GaloisForLFunctions.HTGeometry.EinsteinActionBoundary
open CoordinateMetricTwoJet
noncomputable section
variable {d : ℕ}

/-- Metric compatibility identifies the half-trace volume derivative with the connection trace. -/
theorem halfTrace_eq_connectionTrace (J : CoordinateMetricTwoJet d ℂ) (hJ : J.metric.det ≠ 0)
    (hs : J.metric.transpose = J.metric)
    (hf : ∀ k i j, J.first k i j = J.first k j i) (k : Fin d) :
    (J.metric⁻¹ * J.first k).trace / 2 = ∑ b, J.christoffel b b k := by
  have ht : (J.metric⁻¹ * (connectionMatrix J k).transpose * J.metric).trace =
      (connectionMatrix J k).trace := by
    rw [Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv J.metric (isUnit_iff_ne_zero.mpr hJ),
      Matrix.one_mul, Matrix.trace_transpose]
  have hA (u i j : Fin d) : J.christoffel u i j = J.christoffel u j i := by
    unfold christoffel
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    rw [hf m i j]
    ring
  rw [metric_compatibility J hJ hs hf k, Matrix.mul_add, Matrix.trace_add,
    ← Matrix.mul_assoc, ht, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul J.metric (isUnit_iff_ne_zero.mpr hJ), Matrix.one_mul]
  have ha : (connectionMatrix J k).trace = ∑ b, J.christoffel b b k := by
    unfold Matrix.trace Matrix.diag connectionMatrix
    apply Finset.sum_congr rfl
    intro b _
    exact hA b k b
  rw [ha]
  ring
end
end GaloisForLFunctions.HTGeometry.EinsteinActionBoundary

namespace GaloisForLFunctions.HTGeometry.ComplexMetricActionBoundary
open ScalarTwoJet ComplexMetricField EinsteinActionBoundary MetricPathDensity
noncomputable section
variable {d : ℕ}
local notation "Point" => Fin d → ℝ
local notation "MetricField" => ComplexMetricField.Field d

/-- Spatial volume ratio using the same determinant branch, normalized at the reference point. -/
def localVolume (g : MetricField) (x y : Point) : ℂ :=
  Complex.exp (Complex.log ((g y).det / (g x).det) / 2)

private def detDifferential (g : MetricField) (x : Point) : Point →L[ℝ] ℂ :=
  ∑ σ : Equiv.Perm (Fin d), (Equiv.Perm.sign σ : ℂ) •
    ∑ i, (∏ j ∈ Finset.univ.erase i, g x (σ j) j) • fderiv ℝ (fun y => g y (σ i) i) x

private theorem det_hasFDerivAt (g : MetricField) (x : Point)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x) :
    HasFDerivAt (fun y => (g y).det) (detDifferential g x) x := by
  have hd := HasFDerivAt.fun_sum (u := Finset.univ) (fun σ _ =>
    (HasFDerivAt.finsetProd (u := Finset.univ) (fun i _ => (hg (σ i) i).hasFDerivAt)).const_mul
      (Equiv.Perm.sign σ : ℂ))
  convert! hd using 1
  · funext y
    exact Matrix.det_apply' (g y)

private theorem localVolume_hasFDerivAt (g : MetricField) (x : Point)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x) (hdet : (g x).det ≠ 0) :
    HasFDerivAt (localVolume g x) ((1 / (2 * (g x).det)) • detDifferential g x) x := by
  have hd : HasFDerivAt (fun y => (g y).det / (g x).det)
      (((g x).det)⁻¹ • detDifferential g x) x := by
    simpa only [div_eq_mul_inv, mul_comm] using (det_hasFDerivAt g x hg).const_mul ((g x).det)⁻¹
  have hr : (g x).det / (g x).det = 1 := div_self hdet
  have hl := (Complex.hasStrictFDerivAt_log_real (hr ▸ Complex.one_mem_slitPlane)).hasFDerivAt.comp x hd
  have hv := (hl.const_mul (1 / 2 : ℂ)).cexp
  convert! hv using 1
  · funext y
    simp only [localVolume, Function.comp_apply]
    congr 1
    ring
  · ext v
    simp only [smul_apply, ContinuousLinearMap.comp_apply, Function.comp_apply, hr, Complex.log_one,
      Complex.exp_zero, inv_one, one_smul, one_apply_eq_self, smul_eq_mul, mul_zero]
    ring

/-- The original local volume factor has an actual derivative in every coordinate direction. -/
theorem localVolume_coordDeriv (g : MetricField) (x : Point)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x) (hdet : (g x).det ≠ 0) (k : Fin d) :
    coordDeriv k (localVolume g x) x = ((g x)⁻¹ * (twoJet g x).first k).trace / 2 := by
  unfold coordDeriv
  rw [(localVolume_hasFDerivAt g x hg hdet).fderiv]
  have ht : detDifferential g x (Pi.single k 1) =
      determinantSlope (g x) ((twoJet g x).first k) := by
    simp only [detDifferential, sum_apply, smul_apply,
      smul_eq_mul, determinantSlope, twoJet, coordDeriv]
  rw [smul_apply, ht, determinantSlope_eq_det_mul_trace _ _ hdet]
  change (1 / (2 * (g x).det)) * ((g x).det * _) = _
  field_simp

/-- The formal current divergence equals the actual derivative of its full volume density. -/
theorem current_density_divergence (g h : MetricField) (x : Point)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 3 (fun y => h y i j) x)
    (hdet : (g x).det ≠ 0) (hs : ∀ y i j, g y i j = g y j i) :
    (∑ a, coordDeriv a (fun y => localVolume g x y * current (twoJet g y) (twoJet h y) a) x) =
      divergence (twoJet g x) (twoJet h x) := by
  have hgd (i j : Fin d) := (hg i j).differentiableAt (by norm_num)
  have hmetric : (twoJet g x).metric.transpose = (twoJet g x).metric := by
    ext i j
    exact hs x j i
  have hfirst (k i j : Fin d) : (twoJet g x).first k i j = (twoJet g x).first k j i :=
    congrArg (fun f => coordDeriv k f x) (funext fun y => hs y i j)
  unfold divergence
  apply Finset.sum_congr rfl
  intro a _
  rw [coordDeriv_mul (localVolume_hasFDerivAt g x hgd hdet).differentiableAt
    (current_differentiableAt g h x hg hh hdet a), localVolume_coordDeriv g x hgd hdet,
    current_coordDeriv g h x hg hh hdet]
  erw [halfTrace_eq_connectionTrace (twoJet g x) hdet hmetric hfirst]
  have hv : localVolume g x x = 1 := by simp [localVolume, hdet]
  rw [hv]
  ring

/-- Complete actual field jets commute with affine variation, including ordered second partials. -/
theorem twoJet_affine (g h : MetricField) (x : Point)
    (hg : ∀ i j, ContDiffAt ℝ 2 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun y => h y i j) x) (t : ℂ) :
    twoJet (fun y => g y + t • h y) x =
      CoordinateMetricTwoJet.Linearization.affine (twoJet g x) (twoJet h x) t := by
  have hs (i j : Fin d) : ofField (fun y => g y i j + t * h y i j) x =
      ScalarTwoJet.add (ofField (fun y => g y i j) x)
        (ScalarTwoJet.mul (ScalarTwoJet.constant t) (ofField (fun y => h y i j) x)) := by
    rw [ofField_add (hg i j) (contDiffAt_const.mul (hh i j)),
      ofField_mul contDiffAt_const (hh i j), ofField_constant]
  have he : ComplexCoordinateMetricTwoJet.toSpace (twoJet (fun y => g y + t • h y) x) =
      ComplexCoordinateMetricTwoJet.toSpace
        (CoordinateMetricTwoJet.Linearization.affine (twoJet g x) (twoJet h x) t) := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext k i j
        change (ofField (fun y => g y i j + t * h y i j) x).first k = _
        rw [hs]
        simp only [ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.constant,
          zero_mul, zero_add, ComplexCoordinateMetricTwoJet.toSpace,
          CoordinateMetricTwoJet.Linearization.affine, twoJet, Matrix.add_apply,
          Matrix.smul_apply, smul_eq_mul]
        rfl
      · funext k l i j
        change (ofField (fun y => g y i j + t * h y i j) x).second k l = _
        rw [hs]
        simp only [ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.constant,
          zero_mul, zero_add, add_zero, ComplexCoordinateMetricTwoJet.toSpace,
          CoordinateMetricTwoJet.Linearization.affine, twoJet, Matrix.add_apply,
          Matrix.smul_apply, smul_eq_mul]
        rfl
  exact congrArg ComplexCoordinateMetricTwoJet.ofSpace he

/-- Relative action density of the actual affine field, formed before jet extraction. -/
def fieldDensityPath (g h : MetricField) (x : Point) (Λ t : ℂ) : ℂ :=
  Complex.exp (Complex.log ((g x + t • h x).det / (g x).det) / 2) *
    ((twoJet (fun y => g y + t • h y) x).scalar - 2 * Λ)

/-- The actual-field density equals the previously differentiated complete-jet density. -/
theorem fieldDensityPath_eq (g h : MetricField) (x : Point) (Λ : ℂ)
    (hg : ∀ i j, ContDiffAt ℝ 2 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun y => h y i j) x) :
    fieldDensityPath g h x Λ = densityPath (twoJet g x) (twoJet h x) Λ := by
  funext t
  unfold fieldDensityPath
  erw [twoJet_affine g h x hg hh t]
  simp only [densityPath, volumeRatio, path, smul_zero, add_zero, twoJet]

/-- Actual local Einstein--Hilbert variation, with its complete spatial boundary density.
No field equation or boundary condition is imposed. -/
theorem density_first_variation (g h : MetricField) (x : Point) (Λ : ℂ)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 3 (fun y => h y i j) x)
    (hdet : (g x).det ≠ 0) (hs : ∀ y i j, g y i j = g y j i) :
    deriv (fieldDensityPath g h x Λ) 0 =
      -(∑ i, ∑ j, ((g x)⁻¹ * h x * ((g x)⁻¹).transpose) i j *
        ((twoJet g x).einstein i j + Λ * g x i j)) +
      ∑ a, coordDeriv a (fun y => localVolume g x y * current (twoJet g y) (twoJet h y) a) x := by
  rw [fieldDensityPath_eq g h x Λ
    (fun i j => (hg i j).of_le (by norm_num)) (fun i j => (hh i j).of_le (by norm_num)),
    current_density_divergence g h x hg hh hdet hs]
  exact densityPath_first_variation (twoJet g x) (twoJet h x) Λ hdet
    (by ext i j; exact hs x j i)
    (fun k i j => congrArg (fun f => coordDeriv k f x) (funext fun y => hs y i j))

end
end GaloisForLFunctions.HTGeometry.ComplexMetricActionBoundary
