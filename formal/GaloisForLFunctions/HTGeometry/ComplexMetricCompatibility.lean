import GaloisForLFunctions.HTGeometry.ComplexMetricFieldBianchi
import Mathlib.Tactic.NoncommRing

set_option autoImplicit false

namespace GaloisForLFunctions.HTGeometry.CoordinateMetricTwoJet
noncomputable section
variable {d : ℕ}

/-- Christoffel symbols with the upper and final lower indices arranged as a matrix. -/
def connectionMatrix (J : CoordinateMetricTwoJet d ℂ) (k : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  fun u v => J.christoffel u k v

/-- The first-kind connection matrix, before raising its first tensor index. -/
def lowerConnection (J : CoordinateMetricTwoJet d ℂ) (k : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  fun u v => (1 / 2 : ℂ) * (J.first k u v + J.first v u k - J.first u k v)

/-- The displayed Christoffel formula is exactly raising the first-kind connection index. -/
theorem connectionMatrix_eq (J : CoordinateMetricTwoJet d ℂ) (k : Fin d) :
    connectionMatrix J k = J.metric⁻¹ * lowerConnection J k := by
  ext u v
  simp only [connectionMatrix, christoffel, lowerConnection, Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Lowering the actual Christoffel matrix recovers the first-kind expression. -/
theorem metric_mul_connection (J : CoordinateMetricTwoJet d ℂ) (hJ : J.metric.det ≠ 0) (k : Fin d) :
    J.metric * connectionMatrix J k = lowerConnection J k := by
  rw [connectionMatrix_eq, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv J.metric (isUnit_iff_ne_zero.mpr hJ), Matrix.one_mul]

/-- The metric first jet is the sum of the two forced connection actions. -/
theorem metric_compatibility (J : CoordinateMetricTwoJet d ℂ) (hJ : J.metric.det ≠ 0)
    (hSym : J.metric.transpose = J.metric)
    (hFirst : ∀ k u v, J.first k u v = J.first k v u) (k : Fin d) :
    J.first k = (connectionMatrix J k).transpose * J.metric + J.metric * connectionMatrix J k := by
  have ht : (connectionMatrix J k).transpose * J.metric = (lowerConnection J k).transpose := by
    rw [← hSym, ← Matrix.transpose_mul, metric_mul_connection J hJ]
  rw [ht, metric_mul_connection J hJ]
  ext u v
  simp only [Matrix.add_apply, Matrix.transpose_apply, lowerConnection]
  rw [hFirst k v u, hFirst u v k, hFirst v k u]
  ring

/-- The inverse-metric derivative has the opposite actions on its two raised indices. -/
theorem inverse_compatibility (J : CoordinateMetricTwoJet d ℂ) (hJ : J.metric.det ≠ 0)
    (hSym : J.metric.transpose = J.metric)
    (hFirst : ∀ k u v, J.first k u v = J.first k v u) (k : Fin d) :
    J.inverseDerivative k =
      -(connectionMatrix J k * J.metric⁻¹ + J.metric⁻¹ * (connectionMatrix J k).transpose) := by
  unfold inverseDerivative
  rw [metric_compatibility J hJ hSym hFirst k]
  have hleft := Matrix.nonsing_inv_mul J.metric (isUnit_iff_ne_zero.mpr hJ)
  have hright := Matrix.mul_nonsing_inv J.metric (isUnit_iff_ne_zero.mpr hJ)
  noncomm_ring [hleft, hright]
  rw [← Matrix.mul_assoc J.metric⁻¹ J.metric, hleft, Matrix.one_mul]

end
end GaloisForLFunctions.HTGeometry.CoordinateMetricTwoJet

namespace GaloisForLFunctions.HTGeometry.ComplexMetricField
open ScalarTwoJet
noncomputable section
variable {d : ℕ}

private theorem metric_symmetry (g : Field d) (x : Fin d → ℝ)
    (hs : ∀ y i j, g y i j = g y j i) : (twoJet g x).metric.transpose = (twoJet g x).metric := by
  ext i j
  exact hs x j i

private theorem first_symmetry (g : Field d) (x : Fin d → ℝ)
    (hs : ∀ y i j, g y i j = g y j i) (k i j : Fin d) :
    (twoJet g x).first k i j = (twoJet g x).first k j i :=
  congrArg (fun f => coordDeriv k f x) (funext fun y => hs y i j)

/-- Actual metric compatibility follows from the literal metric-derived connection. -/
theorem metric_compatibility (g : Field d) (x : Fin d → ℝ) (hdet : (g x).det ≠ 0)
    (hs : ∀ y i j, g y i j = g y j i) (k : Fin d) :
    ComplexCoordinateConnection.matrixPartial g x k =
      (connection g x k).transpose * g x + g x * connection g x k :=
  CoordinateMetricTwoJet.metric_compatibility (twoJet g x) hdet
    (metric_symmetry g x hs) (first_symmetry g x hs) k

/-- Actual inverse-metric compatibility, with both connection terms retained. -/
theorem inverse_compatibility (g : Field d) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x) (hdet : (g x).det ≠ 0)
    (hs : ∀ y i j, g y i j = g y j i) (k : Fin d) :
    ComplexCoordinateConnection.matrixPartial (fun y => (g y)⁻¹) x k =
      -(connection g x k * (g x)⁻¹ + (g x)⁻¹ * (connection g x k).transpose) := by
  rw [inverse_partial g x hg hdet]
  exact CoordinateMetricTwoJet.inverse_compatibility (twoJet g x) hdet
    (metric_symmetry g x hs) (first_symmetry g x hs) k

end
end GaloisForLFunctions.HTGeometry.ComplexMetricField
