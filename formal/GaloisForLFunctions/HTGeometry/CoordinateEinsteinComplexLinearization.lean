import GaloisForLFunctions.HTGeometry.CoordinateEinsteinComplexVariations

/-!
# Actual complex linearization of the complete Einstein metric jet

Every term is forced by differentiating the existing coordinate curvature contraction.
The inverse derivative follows from Cramer's rule and the local inverse identity.
The resulting finite contraction equals the actual complex directional derivative on
complete metric-jet space. The fixed cosmological term is retained explicitly.

These identities do not assert that a chosen reconstructed perturbation satisfies the
linearized Einstein equation; that requires evaluating the displayed contraction.
-/

open Complex Set Filter Topology
open scoped BigOperators ContDiff
namespace GaloisForLFunctions.HTGeometry.CoordinateMetricTwoJet.Linearization
noncomputable section
variable {d : ℕ}

local notation "Mat" => Matrix (Fin d) (Fin d) ℂ
local notation "Jet" => CoordinateMetricTwoJet d ℂ

private abbrev MatrixDerivative (F : ℂ → Mat) (F' : Mat) (t : ℂ) : Prop :=
  ∀ i j, HasDerivAt (fun s => F s i j) (F' i j) t

private theorem matrix_mul {F G : ℂ → Mat} {F' G' : Mat} {t : ℂ}
    (hF : MatrixDerivative F F' t) (hG : MatrixDerivative G G' t) :
    MatrixDerivative (fun s => F s * G s) (F' * G t + F t * G') t := by
  intro i j
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => (hF i k).mul (hG k j))
  simpa [Matrix.mul_apply, Finset.sum_add_distrib] using h

private theorem det_differentiable {F : ℂ → Mat} {t : ℂ}
    (hF : ∀ i j, DifferentiableAt ℂ (fun s => F s i j) t) :
    DifferentiableAt ℂ (fun s => (F s).det) t := by
  simp only [Matrix.det_apply']
  exact DifferentiableAt.fun_sum fun σ _ =>
    (DifferentiableAt.fun_finsetProd fun i _ => hF (σ i) i).const_mul _

private theorem adjugate_differentiable {F : ℂ → Mat} {t : ℂ}
    (hF : ∀ i j, DifferentiableAt ℂ (fun s => F s i j) t) (i j : Fin d) :
    DifferentiableAt ℂ (fun s => (F s).adjugate i j) t := by
  simp only [Matrix.adjugate_apply]
  apply det_differentiable
  intro k l
  by_cases hk : k = j
  · simp [Matrix.updateRow_apply, hk]
  · simpa [Matrix.updateRow_apply, hk] using hF k l

private theorem inverse_differentiable {F : ℂ → Mat} {t : ℂ}
    (hF : ∀ i j, DifferentiableAt ℂ (fun s => F s i j) t)
    (hdet : (F t).det ≠ 0) (i j : Fin d) :
    DifferentiableAt ℂ (fun s => (F s)⁻¹ i j) t := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact ((det_differentiable hF).inv hdet).mul (adjugate_differentiable hF i j)

/-- Actual complex derivative of a matrix inverse, proved entrywise from Cramer's rule. -/
theorem matrix_inverse_hasDerivAt {F : ℂ → Mat} {F' : Mat} {t : ℂ}
    (hF : ∀ i j, HasDerivAt (fun s => F s i j) (F' i j) t)
    (hdet : (F t).det ≠ 0) (i j : Fin d) :
    HasDerivAt (fun s => (F s)⁻¹ i j) (-((F t)⁻¹ * F' * (F t)⁻¹) i j) t := by
  have hent := fun i j => (hF i j).differentiableAt
  let W : Mat := fun i j => deriv (fun s => (F s)⁻¹ i j) t
  have hW : MatrixDerivative (fun s => (F s)⁻¹) W t :=
    fun i j => (inverse_differentiable hent hdet i j).hasDerivAt
  have he : ∀ᶠ s in 𝓝 t, (F s)⁻¹ * F s = 1 := by
    filter_upwards [(det_differentiable hent).continuousAt.eventually_ne hdet] with s hs
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hs)
  have hz : MatrixDerivative (fun s => (F s)⁻¹ * F s) 0 t := by
    intro i j
    apply (hasDerivAt_const t ((1 : Mat) i j)).congr_of_eventuallyEq
    filter_upwards [he] with s hs
    rw [hs]
  have hp : W * F t + (F t)⁻¹ * F' = 0 :=
    Matrix.ext fun i j => ((matrix_mul hW hF) i j).unique (hz i j)
  have hv : W = -((F t)⁻¹ * F' * (F t)⁻¹) := by
    have hm := congrArg (fun A : Mat => A * (F t)⁻¹) hp
    simpa only [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr hdet), Matrix.mul_one, Matrix.zero_mul,
      add_eq_zero_iff_eq_neg] using hm
  simpa only [hv, Matrix.neg_apply] using hW i j

/-- Actual affine variation of every coordinate in the complete metric two-jet. -/
def affine (J K : Jet) (t : ℂ) : Jet where
  metric := J.metric + t • K.metric
  first k := J.first k + t • K.first k
  second k l := J.second k l + t • K.second k l

@[simp] theorem affine_zero (J K : Jet) : affine J K 0 = J := by
  simp [affine]

/-- Forced first variation of the inverse metric. -/
def inverse (J K : Jet) : Mat := -(J.metric⁻¹ * K.metric * J.metric⁻¹)

/-- Every term in the variation of the actual spatial inverse derivative. -/
def inverseSpatial (J K : Jet) (k : Fin d) : Mat :=
  -(inverse J K * J.first k * J.metric⁻¹ + J.metric⁻¹ * K.first k * J.metric⁻¹ +
    J.metric⁻¹ * J.first k * inverse J K)

/-- The linearized Christoffel symbols retain the metric-inverse variation. -/
def connection (J K : Jet) (u i j : Fin d) : ℂ :=
  (1 / 2 : ℂ) * ∑ m,
    (inverse J K u m * (J.first i m j + J.first j m i - J.first m i j) +
      J.metric⁻¹ u m * (K.first i m j + K.first j m i - K.first m i j))

/-- Complete spatial connection variation, including every mixed product. -/
def connectionSpatial (J K : Jet) (k u i j : Fin d) : ℂ :=
  (1 / 2 : ℂ) * ∑ m,
    ((inverseSpatial J K k u m * (J.first i m j + J.first j m i - J.first m i j) +
      J.inverseDerivative k u m * (K.first i m j + K.first j m i - K.first m i j)) +
    (inverse J K u m * (J.second k i m j + J.second k j m i - J.second k m i j) +
      J.metric⁻¹ u m * (K.second k i m j + K.second k j m i - K.second k m i j)))

/-- The linearized coordinate Riemann tensor with all connection-product terms. -/
def curvature (J K : Jet) (u i k l : Fin d) : ℂ :=
  connectionSpatial J K k u l i - connectionSpatial J K l u k i +
    ∑ m, ((connection J K u k m * J.christoffel m l i + J.christoffel u k m * connection J K m l i) -
      (connection J K u l m * J.christoffel m k i + J.christoffel u l m * connection J K m k i))

/-- Linearized Ricci contraction. -/
def ricci (J K : Jet) (i j : Fin d) : ℂ := ∑ u, curvature J K u i u j

/-- Scalar variation retains the inverse-metric contraction against background Ricci. -/
def scalar (J K : Jet) : ℂ :=
  ∑ i, ∑ j, (inverse J K i j * J.ricci i j + J.metric⁻¹ i j * ricci J K i j)

/-- Complete linearized Einstein contraction in coordinate-jet data. -/
def einstein (J K : Jet) (i j : Fin d) : ℂ :=
  ricci J K i j - ((1 / 2 : ℂ) * scalar J K * J.metric i j +
    (1 / 2 : ℂ) * J.scalar * K.metric i j)

private theorem affine_metric_hasDerivAt (J K : Jet) (i j : Fin d) :
    HasDerivAt (fun t => (affine J K t).metric i j) (K.metric i j) 0 := by
  simpa [affine] using ((hasDerivAt_id (0 : ℂ)).mul_const (K.metric i j)).const_add (J.metric i j)

private theorem affine_first_hasDerivAt (J K : Jet) (k i j : Fin d) :
    HasDerivAt (fun t => (affine J K t).first k i j) (K.first k i j) 0 := by
  simpa [affine] using ((hasDerivAt_id (0 : ℂ)).mul_const (K.first k i j)).const_add (J.first k i j)

private theorem affine_second_hasDerivAt (J K : Jet) (k l i j : Fin d) :
    HasDerivAt (fun t => (affine J K t).second k l i j) (K.second k l i j) 0 := by
  simpa [affine] using ((hasDerivAt_id (0 : ℂ)).mul_const (K.second k l i j)).const_add (J.second k l i j)

/-- Actual inverse-metric variation of the affine complete jet. -/
theorem inverse_hasDerivAt (J K : Jet) (hJ : J.metric.det ≠ 0) (i j : Fin d) :
    HasDerivAt (fun t => (affine J K t).metric⁻¹ i j) (inverse J K i j) 0 := by
  simpa [inverse] using matrix_inverse_hasDerivAt (affine_metric_hasDerivAt J K)
    (by simpa using hJ) i j

/-- Actual variation of the spatial inverse derivative. -/
theorem inverseSpatial_hasDerivAt (J K : Jet) (hJ : J.metric.det ≠ 0) (k i j : Fin d) :
    HasDerivAt (fun t => (affine J K t).inverseDerivative k i j) (inverseSpatial J K k i j) 0 := by
  have hd := matrix_mul (matrix_mul (inverse_hasDerivAt J K hJ)
    (affine_first_hasDerivAt J K k)) (inverse_hasDerivAt J K hJ)
  convert! (hd i j).neg using 1
  simp [inverseSpatial, Matrix.add_mul]

/-- Actual first variation of every Christoffel entry. -/
theorem connection_hasDerivAt (J K : Jet) (hJ : J.metric.det ≠ 0) (u i j : Fin d) :
    HasDerivAt (fun t => (affine J K t).christoffel u i j) (connection J K u i j) 0 := by
  have hfirst (m : Fin d) := ((affine_first_hasDerivAt J K i m j).add
    (affine_first_hasDerivAt J K j m i)).sub (affine_first_hasDerivAt J K m i j)
  have hd := (HasDerivAt.fun_sum (u := Finset.univ)
    (fun m _ => (inverse_hasDerivAt J K hJ u m).mul (hfirst m))).const_mul (1 / 2 : ℂ)
  simpa [CoordinateMetricTwoJet.christoffel, connection] using hd

/-- Actual variation of the complete spatial Christoffel derivative. -/
theorem connectionSpatial_hasDerivAt (J K : Jet) (hJ : J.metric.det ≠ 0)
    (k u i j : Fin d) :
    HasDerivAt (fun t => (affine J K t).christoffelDerivative k u i j)
      (connectionSpatial J K k u i j) 0 := by
  have hfirst (m : Fin d) := ((affine_first_hasDerivAt J K i m j).add
    (affine_first_hasDerivAt J K j m i)).sub (affine_first_hasDerivAt J K m i j)
  have hsecond (m : Fin d) := ((affine_second_hasDerivAt J K k i m j).add
    (affine_second_hasDerivAt J K k j m i)).sub (affine_second_hasDerivAt J K k m i j)
  have hd := (HasDerivAt.fun_sum (u := Finset.univ) (fun m _ =>
    ((inverseSpatial_hasDerivAt J K hJ k u m).mul (hfirst m)).add
      ((inverse_hasDerivAt J K hJ u m).mul (hsecond m)))).const_mul (1 / 2 : ℂ)
  simpa [CoordinateMetricTwoJet.christoffelDerivative, connectionSpatial] using hd

/-- Actual variation of the full coordinate Riemann tensor. -/
theorem curvature_hasDerivAt (J K : Jet) (hJ : J.metric.det ≠ 0) (u i k l : Fin d) :
    HasDerivAt (fun t => (affine J K t).riemann u i k l) (curvature J K u i k l) 0 := by
  have hc := connection_hasDerivAt J K hJ
  have hd := ((connectionSpatial_hasDerivAt J K hJ k u l i).sub
    (connectionSpatial_hasDerivAt J K hJ l u k i)).add
    (HasDerivAt.fun_sum (u := Finset.univ) (fun m _ =>
      ((hc u k m).mul (hc m l i)).sub ((hc u l m).mul (hc m k i))))
  convert! hd using 1
  simp [curvature]

/-- Actual variation of Ricci curvature. -/
theorem ricci_hasDerivAt (J K : Jet) (hJ : J.metric.det ≠ 0) (i j : Fin d) :
    HasDerivAt (fun t => (affine J K t).ricci i j) (ricci J K i j) 0 := by
  simpa [CoordinateMetricTwoJet.ricci, ricci] using
    HasDerivAt.fun_sum (u := Finset.univ) (fun u _ => curvature_hasDerivAt J K hJ u i u j)

/-- Actual scalar-curvature variation retains both differentiated contraction factors. -/
theorem scalar_hasDerivAt (J K : Jet) (hJ : J.metric.det ≠ 0) :
    HasDerivAt (fun t => (affine J K t).scalar) (scalar J K) 0 := by
  simpa [CoordinateMetricTwoJet.scalar, scalar] using
    HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => HasDerivAt.fun_sum (u := Finset.univ)
      (fun j _ => (inverse_hasDerivAt J K hJ i j).mul (ricci_hasDerivAt J K hJ i j)))

/-- The explicit linearized Einstein contraction is the actual complex derivative. -/
theorem einstein_hasDerivAt (J K : Jet) (hJ : J.metric.det ≠ 0) (i j : Fin d) :
    HasDerivAt (fun t => (affine J K t).einstein i j) (einstein J K i j) 0 := by
  convert! (ricci_hasDerivAt J K hJ i j).sub
    (((scalar_hasDerivAt J K hJ).const_mul (1 / 2 : ℂ)).mul (affine_metric_hasDerivAt J K i j)) using 1
  simp [einstein]

/-- The finite contraction is the actual complex directional derivative on complete jet space. -/
theorem einstein_eq_fderiv (J K : Jet) (hJ : J.metric.det ≠ 0) (i j : Fin d) :
    einstein J K i j =
      fderiv ℂ (ComplexCoordinateMetricTwoJet.einsteinComponent i j)
        (ComplexCoordinateMetricTwoJet.toSpace J) (ComplexCoordinateMetricTwoJet.toSpace K) := by
  have hs := ComplexCoordinateMetricTwoJet.contDiffAt_einsteinComponent
    (n := 1) (ComplexCoordinateMetricTwoJet.toSpace J) hJ i j
  have hline : HasDerivAt
      (fun t : ℂ => ComplexCoordinateMetricTwoJet.toSpace J +
        t • ComplexCoordinateMetricTwoJet.toSpace K)
      (ComplexCoordinateMetricTwoJet.toSpace K) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const
      (ComplexCoordinateMetricTwoJet.toSpace K)).const_add
      (ComplexCoordinateMetricTwoJet.toSpace J)
  have hs0 := hs
  rw [← show ComplexCoordinateMetricTwoJet.toSpace J + (0 : ℂ) •
      ComplexCoordinateMetricTwoJet.toSpace K =
      ComplexCoordinateMetricTwoJet.toSpace J by simp] at hs0
  have hd := (hs0.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt 0 hline
  have hder : HasDerivAt (fun t => (affine J K t).einstein i j)
      (fderiv ℂ (ComplexCoordinateMetricTwoJet.einsteinComponent i j)
        (ComplexCoordinateMetricTwoJet.toSpace J) (ComplexCoordinateMetricTwoJet.toSpace K)) 0 := by
    convert! hd using 1
    simp
  exact (einstein_hasDerivAt J K hJ i j).unique hder

/-- The cosmological term contributes its first variation and is retained explicitly. -/
def cosmological (J K : Jet) (Λ : ℂ) (i j : Fin d) : ℂ :=
  einstein J K i j + Λ * K.metric i j

/-- Actual first variation of Einstein plus the fixed cosmological metric term. -/
theorem cosmological_hasDerivAt (J K : Jet) (hJ : J.metric.det ≠ 0) (Λ : ℂ) (i j : Fin d) :
    HasDerivAt (fun t => (affine J K t).einstein i j + Λ * (affine J K t).metric i j)
      (cosmological J K Λ i j) 0 := by
  exact (einstein_hasDerivAt J K hJ i j).add ((affine_metric_hasDerivAt J K i j).const_mul Λ)

end
end GaloisForLFunctions.HTGeometry.CoordinateMetricTwoJet.Linearization
