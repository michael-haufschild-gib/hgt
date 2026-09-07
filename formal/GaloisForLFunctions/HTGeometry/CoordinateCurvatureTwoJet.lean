import GaloisForLFunctions.HTGeometry.CoordinateCurvature

/-!
# Coordinate Einstein curvature from the complete metric two-jet

Differentiating the actual inverse-metric identity gives `∂ₖ G = -G (∂ₖ g) G`.
The coordinate Christoffel derivative, Riemann tensor, and Einstein tensor consequently factor
through the metric value and all first and second coordinate derivatives. The finite contraction
formulas below are proved equal to the existing differential definitions on smooth metrics.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators ContDiff
noncomputable section

/-- Complete metric value, first partials, and ordered second partials at a chart point.
No symmetry or integrability is imposed on an arbitrary algebraic jet. -/
structure CoordinateMetricTwoJet (d : ℕ) (𝕜 : Type*) where
  metric : Matrix (Fin d) (Fin d) 𝕜
  first : Fin d → Matrix (Fin d) (Fin d) 𝕜
  second : Fin d → Fin d → Matrix (Fin d) (Fin d) 𝕜

namespace CoordinateMetricTwoJet

variable {d : ℕ} {𝕜 : Type*} [Field 𝕜]

/-- Christoffel symbols expressed in metric-jet coordinates. -/
def christoffel (J : CoordinateMetricTwoJet d 𝕜) (u i j : Fin d) : 𝕜 :=
  (1 / 2 : 𝕜) * ∑ m, J.metric⁻¹ u m *
    (J.first i m j + J.first j m i - J.first m i j)

/-- The inverse-metric derivative forced by differentiating the inverse identity. -/
def inverseDerivative (J : CoordinateMetricTwoJet d 𝕜) (k : Fin d) :
    Matrix (Fin d) (Fin d) 𝕜 := -(J.metric⁻¹ * J.first k * J.metric⁻¹)

/-- Complete first Christoffel derivative, including the inverse-metric derivative term. -/
def christoffelDerivative (J : CoordinateMetricTwoJet d 𝕜) (k u i j : Fin d) : 𝕜 :=
  (1 / 2 : 𝕜) * ∑ m,
    (J.inverseDerivative k u m * (J.first i m j + J.first j m i - J.first m i j) +
      J.metric⁻¹ u m * (J.second k i m j + J.second k j m i - J.second k m i j))

/-- Coordinate Riemann tensor from the complete metric two-jet. -/
def riemann (J : CoordinateMetricTwoJet d 𝕜) (u i k l : Fin d) : 𝕜 :=
  J.christoffelDerivative k u l i - J.christoffelDerivative l u k i +
    ∑ m, (J.christoffel u k m * J.christoffel m l i -
      J.christoffel u l m * J.christoffel m k i)

/-- Coordinate Ricci contraction of the metric two-jet. -/
def ricci (J : CoordinateMetricTwoJet d 𝕜) : Matrix (Fin d) (Fin d) 𝕜 :=
  fun i j => ∑ u, J.riemann u i u j

/-- Scalar curvature contraction of the metric two-jet. -/
def scalar (J : CoordinateMetricTwoJet d 𝕜) : 𝕜 :=
  ∑ i, ∑ j, J.metric⁻¹ i j * J.ricci i j

/-- Einstein tensor expressed as a rational finite contraction of the metric two-jet. -/
def einstein (J : CoordinateMetricTwoJet d 𝕜) : Matrix (Fin d) (Fin d) 𝕜 :=
  fun i j => J.ricci i j - (1 / 2 : 𝕜) * J.scalar * J.metric i j

end CoordinateMetricTwoJet

namespace SmoothPseudoMetric

variable {d : ℕ} (g : SmoothPseudoMetric d)

/-- The complete two-jet extracted from an actual smooth nondegenerate metric field. -/
def twoJet (x : Fin d → ℝ) : CoordinateMetricTwoJet d ℝ where
  metric := g.metric x
  first := fun k i j => coordPartial k (fun y => g.metric y i j) x
  second := fun k l i j => coordPartial k (fun y => coordPartial l (fun z => g.metric z i j) y) x

private theorem metric_differentiable (x : Fin d → ℝ) (i j : Fin d) :
    DifferentiableAt ℝ (fun y => g.metric y i j) x :=
  differentiableAt_of_contDiff_infty (g.contDiff_metric i j) x

private theorem inverse_differentiable (x : Fin d → ℝ) (i j : Fin d) :
    DifferentiableAt ℝ (fun y => g.chart.inverseMetric y i j) x :=
  differentiableAt_of_contDiff_infty (g.chart.contDiff_inverseMetric i j) x

/-- The coordinate derivative of the actual inverse metric is fixed by its metric first jet. -/
theorem coordPartial_inverseMetric (x : Fin d → ℝ) (k : Fin d) :
    (fun i j => coordPartial k (fun y => g.chart.inverseMetric y i j) x) =
      (g.twoJet x).inverseDerivative k := by
  let Q : Matrix (Fin d) (Fin d) ℝ :=
    fun i j => coordPartial k (fun y => g.chart.inverseMetric y i j) x
  let H := (g.twoJet x).first k
  let G := g.chart.inverseMetric x
  have hprod : Q * g.metric x + G * H = 0 := by
    ext i j
    have hid : (fun y => ∑ m, g.chart.inverseMetric y i m * g.metric y m j) =
        fun _ : Fin d → ℝ => (1 : Matrix (Fin d) (Fin d) ℝ) i j := by
      funext y
      exact congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M i j)
        (Matrix.nonsing_inv_mul (g.metric y) (g.isUnit_det y))
    have hd := congrArg (fun f => coordPartial k f x) hid
    have hterm (m : Fin d) : DifferentiableAt ℝ
        (fun y => g.chart.inverseMetric y i m * g.metric y m j) x :=
      (g.inverse_differentiable x i m).mul (g.metric_differentiable x m j)
    rw [coordPartial_sum (s := Finset.univ) (fun m _ => hterm m) k,
      coordPartial_const] at hd
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply]
    dsimp only [Q, G, H, twoJet]
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ m, coordPartial k (fun y => g.chart.inverseMetric y i m * g.metric y m j) x := by
        apply Finset.sum_congr rfl
        intro m _
        rw [coordPartial_mul (g.inverse_differentiable x i m) (g.metric_differentiable x m j) k]
        ring
      _ = 0 := hd
  have hinv : g.metric x * G = 1 := Matrix.mul_nonsing_inv (g.metric x) (g.isUnit_det x)
  change Q = -(G * H * G)
  have hright := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M * G) hprod
  rw [Matrix.add_mul, Matrix.mul_assoc Q, hinv, Matrix.mul_one, Matrix.zero_mul] at hright
  exact eq_neg_of_add_eq_zero_left hright

end SmoothPseudoMetric

private theorem coordPartial_sub {d : ℕ} {f h : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x) (k : Fin d) :
    coordPartial k (fun y => f y - h y) x = coordPartial k f x - coordPartial k h x := by
  have heq : (fun y => f y - h y) = f - h := rfl
  rw [heq]
  simp [coordPartial, fderiv_sub hf hh]

variable {d : ℕ} (g : SmoothPseudoMetric d)

/-- The finite first-jet formula agrees with the actual coordinate Christoffel symbols. -/
theorem coordinateChristoffel_eq_twoJet (x : Fin d → ℝ) (u i j : Fin d) :
    coordinateChristoffel g x u i j = (g.twoJet x).christoffel u i j := rfl

/-- The full finite Christoffel derivative equals its actual coordinate partial derivative. -/
theorem coordPartial_coordinateChristoffel_eq_twoJet (x : Fin d → ℝ) (k u i j : Fin d) :
    coordPartial k (fun y => coordinateChristoffel g y u i j) x =
      (g.twoJet x).christoffelDerivative k u i j := by
  have hfirst (l a b : Fin d) :
      DifferentiableAt ℝ (fun y => coordPartial l (fun z => g.metric z a b) y) x :=
    differentiableAt_of_contDiff_infty (contDiff_coordPartial (g.contDiff_metric a b) l) x
  have hlin (m : Fin d) : DifferentiableAt ℝ
      (fun y => coordPartial i (fun z => g.metric z m j) y +
        coordPartial j (fun z => g.metric z m i) y - coordPartial m (fun z => g.metric z i j) y) x :=
    ((hfirst i m j).add (hfirst j m i)).sub (hfirst m i j)
  have hinv (m : Fin d) := g.inverse_differentiable x u m
  have hterm (m : Fin d) : DifferentiableAt ℝ
      (fun y => g.chart.inverseMetric y u m *
        (coordPartial i (fun z => g.metric z m j) y +
          coordPartial j (fun z => g.metric z m i) y - coordPartial m (fun z => g.metric z i j) y)) x :=
    (hinv m).mul (hlin m)
  have hsum := DifferentiableAt.fun_sum (fun m (_ : m ∈ Finset.univ) => hterm m)
  dsimp only [coordinateChristoffel]
  rw [coordPartial_const_mul hsum, coordPartial_sum (s := Finset.univ) (fun m _ => hterm m)]
  unfold CoordinateMetricTwoJet.christoffelDerivative
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  have hadd : DifferentiableAt ℝ (fun y => coordPartial i (fun z => g.metric z m j) y +
      coordPartial j (fun z => g.metric z m i) y) x := (hfirst i m j).add (hfirst j m i)
  rw [coordPartial_mul (hinv m) (hlin m), coordPartial_sub hadd (hfirst m i j),
    coordPartial_add (hfirst i m j) (hfirst j m i)]
  have hG := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M u m) (g.coordPartial_inverseMetric x k)
  rw [hG]
  dsimp only [SmoothPseudoMetric.twoJet]
  rw [SmoothPseudoMetric.chart_inverseMetric]
  ring

/-- Actual coordinate Riemann curvature depends only on the complete metric two-jet. -/
theorem coordinateRiemann_eq_twoJet (x : Fin d → ℝ) (u i k l : Fin d) :
    coordinateRiemann g x u i k l = (g.twoJet x).riemann u i k l := by
  rw [coordinateRiemann, coordPartial_coordinateChristoffel_eq_twoJet,
    coordPartial_coordinateChristoffel_eq_twoJet]
  simp only [CoordinateMetricTwoJet.riemann, coordinateChristoffel_eq_twoJet]

/-- Actual Ricci curvature equals the finite metric-jet contraction. -/
theorem coordinateRicci_eq_twoJet (x : Fin d → ℝ) :
    coordinateRicci g x = (g.twoJet x).ricci := by
  ext i j
  simp only [coordinateRicci, CoordinateMetricTwoJet.ricci, coordinateRiemann_eq_twoJet]

/-- Actual scalar curvature equals the finite metric-jet contraction. -/
theorem coordinateScalarCurvature_eq_twoJet (x : Fin d → ℝ) :
    coordinateScalarCurvature g x = (g.twoJet x).scalar := by
  simp only [coordinateScalarCurvature, CoordinateMetricTwoJet.scalar, coordinateRicci_eq_twoJet]
  rfl

/-- The complete coordinate Einstein tensor is determined by the actual metric two-jet. -/
theorem coordinateEinsteinTensor_eq_twoJet (x : Fin d → ℝ) :
    coordinateEinsteinTensor g x = (g.twoJet x).einstein := by
  ext i j
  simp only [coordinateEinsteinTensor, CoordinateMetricTwoJet.einstein,
    coordinateRicci_eq_twoJet, coordinateScalarCurvature_eq_twoJet]
  rfl

end
end GaloisForLFunctions.HTGeometry
