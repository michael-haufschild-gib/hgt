import GaloisForLFunctions.HTGeometry.CoordinateCurvatureTwoJet
import GaloisForLFunctions.HTGeometry.MatrixAffineInverseCubicRemainder
import GaloisForLFunctions.HTGeometry.CubicDerivativeCurve

/-!
# Actual quadratic and cubic coefficients of the coordinate Einstein tensor

The complete affine metric two-jet and the actual inverse-metric derivative chain are propagated
through every finite curvature contraction. The resulting second and third components are
explicit diagonal Einstein source coefficients, certified against ordinary iterated derivatives.
The construction takes metric data and its variation, with no supplied nonlinear source map.
-/

namespace GaloisForLFunctions.HTGeometry
open scoped BigOperators
noncomputable section

namespace CoordinateMetricTwoJet
variable {d : ℕ}

/-- Affine perturbation of every component of the complete spatial metric two-jet. -/
def affinePerturbation (J K : CoordinateMetricTwoJet d ℝ) (t : ℝ) : CoordinateMetricTwoJet d ℝ where
  metric := J.metric + t • K.metric
  first := fun k => J.first k + t • K.first k
  second := fun k l => J.second k l + t • K.second k l

/-- The parameter domain where the perturbed metric value is nondegenerate. -/
def affineNondegenerateDomain (J K : CoordinateMetricTwoJet d ℝ) : Set ℝ :=
  {t | (J.metric + t • K.metric).det ≠ 0}

/-- Nondegeneracy is an open condition on the actual affine parameter. -/
theorem isOpen_affineNondegenerateDomain (J K : CoordinateMetricTwoJet d ℝ) :
    IsOpen (affineNondegenerateDomain J K) := by
  have hc : Continuous (fun t : ℝ => (J.metric + t • K.metric).det) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hd : DifferentiableAt ℝ (fun u : ℝ => (J.metric + u • K.metric).det) t := by
      apply differentiableAt_det_of_entries
      intro i j
      exact ((differentiableAt_const _).add ((differentiableAt_id).mul_const (K.metric i j)))
    exact hd.continuousAt
  have hopen : IsOpen {y : ℝ | y ≠ 0} := isOpen_ne
  exact hopen.preimage hc

/-- The affine metric value as a certified curve. -/
def affineMetricCurve (J K : CoordinateMetricTwoJet d ℝ) (i j : Fin d) :
    CubicDerivativeCurve (affineNondegenerateDomain J K) :=
  CubicDerivativeCurve.affine (J.metric i j) (K.metric i j)

/-- Every first spatial derivative of the affine metric as a certified curve. -/
def affineFirstCurve (J K : CoordinateMetricTwoJet d ℝ) (k i j : Fin d) :
    CubicDerivativeCurve (affineNondegenerateDomain J K) :=
  CubicDerivativeCurve.affine (J.first k i j) (K.first k i j)

/-- Every ordered second spatial derivative of the affine metric as a certified curve. -/
def affineSecondCurve (J K : CoordinateMetricTwoJet d ℝ) (k l i j : Fin d) :
    CubicDerivativeCurve (affineNondegenerateDomain J K) :=
  CubicDerivativeCurve.affine (J.second k l i j) (K.second k l i j)

/-- Actual affine inverse entries with their certified derivative chain through order three. -/
def affineInverseCurve (J K : CoordinateMetricTwoJet d ℝ) (i j : Fin d) :
    CubicDerivativeCurve (affineNondegenerateDomain J K) where
  value := fun t => (J.metric + t • K.metric)⁻¹ i j
  first := fun t => matrixAffineInverseFirstDerivative J.metric K.metric t i j
  second := fun t => matrixAffineInverseSecondDerivative J.metric K.metric t i j
  third := fun t => matrixAffineInverseThirdDerivative J.metric K.metric t i j
  has_first := fun t ht => matrixHasDerivAt_affineInverse J.metric K.metric t ht i j
  has_second := fun t ht => matrixHasDerivAt_affineInverseFirstDerivative J.metric K.metric t ht i j
  has_third := fun t ht => matrixHasDerivAt_affineInverseSecondDerivative J.metric K.metric t ht i j

/-- Spatial inverse derivative `-G (partial_k g) G`, retaining all perturbative product terms. -/
def affineInverseSpatialCurve (J K : CoordinateMetricTwoJet d ℝ) (k i j : Fin d) :
    CubicDerivativeCurve (affineNondegenerateDomain J K) :=
  CubicDerivativeCurve.constant (-1) * CubicDerivativeCurve.sum (fun l : Fin d =>
    CubicDerivativeCurve.sum (fun m : Fin d => affineInverseCurve J K i m * affineFirstCurve J K k m l) *
      affineInverseCurve J K l j)

/-- Complete Christoffel curve through cubic perturbative order. -/
def affineChristoffelCurve (J K : CoordinateMetricTwoJet d ℝ) (u i j : Fin d) :
    CubicDerivativeCurve (affineNondegenerateDomain J K) :=
  CubicDerivativeCurve.constant (1 / 2) * CubicDerivativeCurve.sum (fun m : Fin d =>
    affineInverseCurve J K u m *
      (affineFirstCurve J K i m j + affineFirstCurve J K j m i - affineFirstCurve J K m i j))

/-- Full Christoffel spatial derivative, including the changing inverse metric. -/
def affineChristoffelSpatialCurve (J K : CoordinateMetricTwoJet d ℝ) (k u i j : Fin d) :
    CubicDerivativeCurve (affineNondegenerateDomain J K) :=
  CubicDerivativeCurve.constant (1 / 2) * CubicDerivativeCurve.sum (fun m : Fin d =>
    affineInverseSpatialCurve J K k u m *
      (affineFirstCurve J K i m j + affineFirstCurve J K j m i - affineFirstCurve J K m i j) +
    affineInverseCurve J K u m *
      (affineSecondCurve J K k i m j + affineSecondCurve J K k j m i - affineSecondCurve J K k m i j))

/-- Complete coordinate Riemann curve through order three. -/
def affineRiemannCurve (J K : CoordinateMetricTwoJet d ℝ) (u i k l : Fin d) :
    CubicDerivativeCurve (affineNondegenerateDomain J K) :=
  affineChristoffelSpatialCurve J K k u l i - affineChristoffelSpatialCurve J K l u k i +
    CubicDerivativeCurve.sum (fun m : Fin d =>
      affineChristoffelCurve J K u k m * affineChristoffelCurve J K m l i -
        affineChristoffelCurve J K u l m * affineChristoffelCurve J K m k i)

/-- Complete Ricci curve, without selecting a helicity grade. -/
def affineRicciCurve (J K : CoordinateMetricTwoJet d ℝ) (i j : Fin d) :
    CubicDerivativeCurve (affineNondegenerateDomain J K) :=
  CubicDerivativeCurve.sum (fun u : Fin d => affineRiemannCurve J K u i u j)

/-- Scalar curvature curve with every inverse-metric contraction retained. -/
def affineScalarCurve (J K : CoordinateMetricTwoJet d ℝ) :
    CubicDerivativeCurve (affineNondegenerateDomain J K) :=
  CubicDerivativeCurve.sum (fun i : Fin d => CubicDerivativeCurve.sum (fun j : Fin d =>
    affineInverseCurve J K i j * affineRicciCurve J K i j))

/-- The full coordinate Einstein curve constructed from actual metric and inverse derivatives. -/
def affineEinsteinCurve (J K : CoordinateMetricTwoJet d ℝ) (i j : Fin d) :
    CubicDerivativeCurve (affineNondegenerateDomain J K) :=
  affineRicciCurve J K i j -
    CubicDerivativeCurve.constant (1 / 2) * affineScalarCurve J K * affineMetricCurve J K i j

/-- The inverse spatial curve has the literal metric-jet inverse derivative as its value. -/
theorem affineInverseSpatialCurve_value (J K : CoordinateMetricTwoJet d ℝ) (k i j : Fin d) (t : ℝ) :
    (affineInverseSpatialCurve J K k i j).value t = (affinePerturbation J K t).inverseDerivative k i j := by
  simp [affineInverseSpatialCurve, affineInverseCurve, affineFirstCurve,
    inverseDerivative, affinePerturbation, Matrix.mul_apply]

/-- The Christoffel curve represents the full affine metric Christoffel expression. -/
theorem affineChristoffelCurve_value (J K : CoordinateMetricTwoJet d ℝ) (u i j : Fin d) (t : ℝ) :
    (affineChristoffelCurve J K u i j).value t = (affinePerturbation J K t).christoffel u i j := by
  simp [affineChristoffelCurve, affineInverseCurve, affineFirstCurve, christoffel, affinePerturbation]

/-- Spatial Christoffel differentiation and parameter differentiation use the same full expression. -/
theorem affineChristoffelSpatialCurve_value
    (J K : CoordinateMetricTwoJet d ℝ) (k u i j : Fin d) (t : ℝ) :
    (affineChristoffelSpatialCurve J K k u i j).value t =
      (affinePerturbation J K t).christoffelDerivative k u i j := by
  simp [affineChristoffelSpatialCurve, affineInverseSpatialCurve_value, affineInverseCurve,
    affineFirstCurve, affineSecondCurve, christoffelDerivative, affinePerturbation]

/-- Value identification of the entire Riemann derivative curve. -/
theorem affineRiemannCurve_value (J K : CoordinateMetricTwoJet d ℝ) (u i k l : Fin d) (t : ℝ) :
    (affineRiemannCurve J K u i k l).value t = (affinePerturbation J K t).riemann u i k l := by
  simp [affineRiemannCurve, affineChristoffelSpatialCurve_value, affineChristoffelCurve_value, riemann]

/-- Value identification of the full Ricci derivative curve. -/
theorem affineRicciCurve_value (J K : CoordinateMetricTwoJet d ℝ) (i j : Fin d) (t : ℝ) :
    (affineRicciCurve J K i j).value t = (affinePerturbation J K t).ricci i j := by
  simp [affineRicciCurve, affineRiemannCurve_value, ricci]

/-- Value identification of the full scalar curvature derivative curve. -/
theorem affineScalarCurve_value (J K : CoordinateMetricTwoJet d ℝ) (t : ℝ) :
    (affineScalarCurve J K).value t = (affinePerturbation J K t).scalar := by
  simp [affineScalarCurve, affineInverseCurve, affineRicciCurve_value, scalar, affinePerturbation]

/-- The generated curve is the actual coordinate Einstein contraction of the affine two-jet. -/
theorem affineEinsteinCurve_value (J K : CoordinateMetricTwoJet d ℝ) (i j : Fin d) (t : ℝ) :
    (affineEinsteinCurve J K i j).value t = (affinePerturbation J K t).einstein i j := by
  simp [affineEinsteinCurve, affineRicciCurve_value, affineScalarCurve_value, affineMetricCurve,
    einstein, affinePerturbation]

/-- The complete diagonal quadratic Einstein coefficient, including every contraction channel. -/
def affineEinsteinQuadraticCoefficient (J K : CoordinateMetricTwoJet d ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => (affineEinsteinCurve J K i j).second 0 / 2

/-- The complete diagonal cubic Einstein coefficient, without a supplied third-variation map. -/
def affineEinsteinCubicCoefficient (J K : CoordinateMetricTwoJet d ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => (affineEinsteinCurve J K i j).third 0 / 6

/-- The fixed cosmological term in the actual coordinate Einstein equation. -/
def affineEinsteinCosmologicalCurve (J K : CoordinateMetricTwoJet d ℝ) (Λ : ℝ) (i j : Fin d) :
    CubicDerivativeCurve (affineNondegenerateDomain J K) :=
  affineEinsteinCurve J K i j + CubicDerivativeCurve.constant Λ * affineMetricCurve J K i j

/-- The full cosmological curve represents `G_ij + Lambda g_ij` at every parameter. -/
theorem affineEinsteinCosmologicalCurve_value
    (J K : CoordinateMetricTwoJet d ℝ) (Λ : ℝ) (i j : Fin d) (t : ℝ) :
    (affineEinsteinCosmologicalCurve J K Λ i j).value t =
      (affinePerturbation J K t).einstein i j + Λ * (affinePerturbation J K t).metric i j := by
  simp [affineEinsteinCosmologicalCurve, affineEinsteinCurve_value, affineMetricCurve, affinePerturbation]

/-- A fixed cosmological term has no second or third affine metric coefficient. -/
theorem affineEinsteinCosmologicalCurve_higher_components
    (J K : CoordinateMetricTwoJet d ℝ) (Λ : ℝ) (i j : Fin d) (t : ℝ) :
    (affineEinsteinCosmologicalCurve J K Λ i j).second t = (affineEinsteinCurve J K i j).second t ∧
      (affineEinsteinCosmologicalCurve J K Λ i j).third t = (affineEinsteinCurve J K i j).third t := by
  change
    (CubicDerivativeCurve.add (affineEinsteinCurve J K i j)
      (CubicDerivativeCurve.mul (CubicDerivativeCurve.constant Λ) (affineMetricCurve J K i j))).second t = _ ∧
    (CubicDerivativeCurve.add (affineEinsteinCurve J K i j)
      (CubicDerivativeCurve.mul (CubicDerivativeCurve.constant Λ) (affineMetricCurve J K i j))).third t = _
  simp [affineMetricCurve, CubicDerivativeCurve.add, CubicDerivativeCurve.mul,
    CubicDerivativeCurve.constant, CubicDerivativeCurve.affine]

/-- The constructed quadratic coefficient is exactly half the actual second parameter derivative. -/
theorem affineEinsteinQuadraticCoefficient_eq_iteratedDeriv
    (J K : CoordinateMetricTwoJet d ℝ) (hJ : J.metric.det ≠ 0) (i j : Fin d) :
    affineEinsteinQuadraticCoefficient J K i j =
      iteratedDeriv 2 (fun t => (affinePerturbation J K t).einstein i j) 0 / 2 := by
  have ht : (0 : ℝ) ∈ affineNondegenerateDomain J K := by simpa [affineNondegenerateDomain] using hJ
  have h := (affineEinsteinCurve J K i j).iteratedDeriv_two_value
    (isOpen_affineNondegenerateDomain J K) ht
  have heq : (affineEinsteinCurve J K i j).value =
      fun t => (affinePerturbation J K t).einstein i j := funext (affineEinsteinCurve_value J K i j)
  rw [heq] at h
  exact congrArg (fun x : ℝ => x / 2) h.symm

/-- The constructed cubic coefficient is exactly one sixth of the actual third parameter derivative. -/
theorem affineEinsteinCubicCoefficient_eq_iteratedDeriv
    (J K : CoordinateMetricTwoJet d ℝ) (hJ : J.metric.det ≠ 0) (i j : Fin d) :
    affineEinsteinCubicCoefficient J K i j =
      iteratedDeriv 3 (fun t => (affinePerturbation J K t).einstein i j) 0 / 6 := by
  have ht : (0 : ℝ) ∈ affineNondegenerateDomain J K := by simpa [affineNondegenerateDomain] using hJ
  have h := (affineEinsteinCurve J K i j).iteratedDeriv_three_value
    (isOpen_affineNondegenerateDomain J K) ht
  have heq : (affineEinsteinCurve J K i j).value =
      fun t => (affinePerturbation J K t).einstein i j := funext (affineEinsteinCurve_value J K i j)
  rw [heq] at h
  exact congrArg (fun x : ℝ => x / 6) h.symm

/-- The diagonal quadratic source is also the actual coefficient of the cosmological equation. -/
theorem affineEinsteinQuadraticCoefficient_eq_cosmological_iteratedDeriv
    (J K : CoordinateMetricTwoJet d ℝ) (hJ : J.metric.det ≠ 0) (Λ : ℝ) (i j : Fin d) :
    affineEinsteinQuadraticCoefficient J K i j = iteratedDeriv 2
      (fun t => (affinePerturbation J K t).einstein i j + Λ * (affinePerturbation J K t).metric i j) 0 / 2 := by
  have ht : (0 : ℝ) ∈ affineNondegenerateDomain J K := by simpa [affineNondegenerateDomain] using hJ
  have h := (affineEinsteinCosmologicalCurve J K Λ i j).iteratedDeriv_two_value
    (isOpen_affineNondegenerateDomain J K) ht
  have heq : (affineEinsteinCosmologicalCurve J K Λ i j).value = fun t =>
      (affinePerturbation J K t).einstein i j + Λ * (affinePerturbation J K t).metric i j :=
    funext (affineEinsteinCosmologicalCurve_value J K Λ i j)
  rw [heq, (affineEinsteinCosmologicalCurve_higher_components J K Λ i j 0).1] at h
  exact congrArg (fun x : ℝ => x / 2) h.symm

/-- The full diagonal cubic source is the actual coefficient of the cosmological equation. -/
theorem affineEinsteinCubicCoefficient_eq_cosmological_iteratedDeriv
    (J K : CoordinateMetricTwoJet d ℝ) (hJ : J.metric.det ≠ 0) (Λ : ℝ) (i j : Fin d) :
    affineEinsteinCubicCoefficient J K i j = iteratedDeriv 3
      (fun t => (affinePerturbation J K t).einstein i j + Λ * (affinePerturbation J K t).metric i j) 0 / 6 := by
  have ht : (0 : ℝ) ∈ affineNondegenerateDomain J K := by simpa [affineNondegenerateDomain] using hJ
  have h := (affineEinsteinCosmologicalCurve J K Λ i j).iteratedDeriv_three_value
    (isOpen_affineNondegenerateDomain J K) ht
  have heq : (affineEinsteinCosmologicalCurve J K Λ i j).value = fun t =>
      (affinePerturbation J K t).einstein i j + Λ * (affinePerturbation J K t).metric i j :=
    funext (affineEinsteinCosmologicalCurve_value J K Λ i j)
  rw [heq, (affineEinsteinCosmologicalCurve_higher_components J K Λ i j 0).2] at h
  exact congrArg (fun x : ℝ => x / 6) h.symm

end CoordinateMetricTwoJet
end
end GaloisForLFunctions.HTGeometry
