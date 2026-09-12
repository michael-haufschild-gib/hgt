import GaloisForLFunctions.HTGeometry.ComplexMetricCompatibility

set_option autoImplicit false
namespace GaloisForLFunctions.HTGeometry.ComplexCoordinateConnection
open ScalarTwoJet Filter Topology
noncomputable section
variable {d n : ℕ}

/-- Product rule for the original matrix coordinate derivative. -/
theorem matrixPartial_mul (M N : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ)
    (x : Fin d → ℝ) (hM : ∀ u v, DifferentiableAt ℝ (fun y => M y u v) x)
    (hN : ∀ u v, DifferentiableAt ℝ (fun y => N y u v) x) (k : Fin d) :
    matrixPartial (fun y => M y*N y) x k =
      matrixPartial M x k*N x + M x*matrixPartial N x k := by
  ext u v
  simp only [Matrix.mul_apply, Matrix.add_apply, matrixPartial]
  rw [coordDeriv_sum (s := Finset.univ) (F := fun a y => M y u a*N y a v)
    (fun a _ => (hM u a).mul (hN a v))]
  simp_rw [coordDeriv_mul (hM u _) (hN _ v)]
  exact Finset.sum_add_distrib

/-- An identity on a genuine neighborhood can be differentiated entrywise. -/
theorem matrixPartial_congr {M N : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ}
    {x : Fin d → ℝ} (h : M =ᶠ[𝓝 x] N) (k : Fin d) :
    matrixPartial M x k = matrixPartial N x k := by
  ext u v
  have he : (fun y => M y u v) =ᶠ[𝓝 x] (fun y => N y u v) :=
    h.mono (fun _ he => congrArg (fun P => P u v) he)
  exact congrArg (fun D => D (Pi.single k 1)) (he.fderiv_eq (𝕜 := ℝ))

/-- The commuted compatibility derivatives are precisely metric-skew curvature. -/
theorem curvature_metric_defect (G Gi Gj A B DiB DjA : Matrix (Fin n) (Fin n) ℂ)
    (hi : Gi = A.transpose*G+G*A) (hj : Gj = B.transpose*G+G*B) :
    (DiB-DjA+A*B-B*A).transpose*G + G*(DiB-DjA+A*B-B*A) =
      (DiB.transpose*G+B.transpose*Gi+Gi*B+G*DiB) -
      (DjA.transpose*G+A.transpose*Gj+Gj*A+G*DjA) := by
  rw [hi,hj]
  simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul]
  noncomm_ring

end
end GaloisForLFunctions.HTGeometry.ComplexCoordinateConnection

namespace GaloisForLFunctions.HTGeometry.ComplexMetricField
open ScalarTwoJet ComplexCoordinateConnection Filter Topology
noncomputable section
variable {d : ℕ}

/-- Differentiating the literal metric-compatibility identity keeps all four terms. -/
theorem metric_compatibility_derivative (g : Field d) (x : Fin d → ℝ)
    (hg : ∀ u v, ContDiffAt ℝ 3 (fun y => g y u v) x)
    (hdet : (g x).det ≠ 0) (hs : ∀ y u v, g y u v = g y v u) (i j : Fin d) :
    matrixPartial (fun y => matrixPartial g y j) x i =
      (first (connection g) x i j).transpose*g x +
      (connection g x j).transpose*matrixPartial g x i +
      matrixPartial g x i*connection g x j + g x*first (connection g) x i j := by
  have hc (u v : Fin d) : ContinuousAt (fun y => g y u v) x := (hg u v).continuousAt
  have hd : ContinuousAt (fun y => (g y).det) x := by
    simp only [Matrix.det_apply']
    fun_prop
  have he : (fun y => matrixPartial g y j) =ᶠ[𝓝 x]
      (fun y => (connection g y j).transpose*g y + g y*connection g y j) := by
    filter_upwards [hd.eventually_ne hdet] with y hy
    exact metric_compatibility g y hy hs j
  rw [matrixPartial_congr he i]
  have hgD (u v : Fin d) := (hg u v).differentiableAt (by norm_num)
  have hAD (k u v : Fin d) :=
    (connection_contDiffAt g x hg hdet k u v).differentiableAt (by norm_num)
  have hm (M N : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℂ)
      (hM : ∀ u v, DifferentiableAt ℝ (fun y => M y u v) x)
      (hN : ∀ u v, DifferentiableAt ℝ (fun y => N y u v) x) (u v : Fin d) :
      DifferentiableAt ℝ (fun y => (M y*N y) u v) x := by
    change DifferentiableAt ℝ (fun y => ∑ a, M y u a*N y a v) x
    exact DifferentiableAt.fun_sum (fun a _ => (hM u a).mul (hN a v))
  have hsum : matrixPartial
      (fun y => (connection g y j).transpose*g y + g y*connection g y j) x i =
      matrixPartial (fun y => (connection g y j).transpose*g y) x i +
      matrixPartial (fun y => g y*connection g y j) x i := by
    ext u v
    exact coordDeriv_add (hm _ _ (fun u v => hAD j v u) hgD u v)
      (hm _ _ hgD (hAD j) u v) i
  rw [hsum, matrixPartial_mul (fun y => (connection g y j).transpose) g x
    (fun u v => hAD j v u) hgD i,
    matrixPartial_mul g (fun y => connection g y j) x hgD (hAD j) i]
  change ((first (connection g) x i j).transpose*g x +
    (connection g x j).transpose*matrixPartial g x i) +
    (matrixPartial g x i*connection g x j+g x*first (connection g) x i j) = _
  simp only [add_assoc]

/-- Commuting actual metric derivatives proves skewness of the actual curvature
with respect to that metric; no curvature-symmetry premise is supplied. -/
theorem curvature_metric_skew (g : Field d) (x : Fin d → ℝ)
    (hg : ∀ u v, ContDiffAt ℝ 3 (fun y => g y u v) x)
    (hdet : (g x).det ≠ 0) (hs : ∀ y u v, g y u v = g y v u) (i j : Fin d) :
    (curvature (connection g) x i j).transpose*g x +
      g x*curvature (connection g) x i j = 0 := by
  have hc : matrixPartial (fun y => matrixPartial g y j) x i =
      matrixPartial (fun y => matrixPartial g y i) x j := by
    ext u v
    exact coordDeriv_comm ((hg u v).of_le (by norm_num)) i j
  rw [metric_compatibility_derivative g x hg hdet hs i j,
    metric_compatibility_derivative g x hg hdet hs j i] at hc
  change (first (connection g) x i j-first (connection g) x j i+
      connection g x i*connection g x j-connection g x j*connection g x i).transpose*g x +
    g x*(first (connection g) x i j-first (connection g) x j i+
      connection g x i*connection g x j-connection g x j*connection g x i) = 0
  rw [curvature_metric_defect (g x) (matrixPartial g x i) (matrixPartial g x j)
    (connection g x i) (connection g x j) (first (connection g) x i j)
    (first (connection g) x j i) (metric_compatibility g x hdet hs i)
    (metric_compatibility g x hdet hs j)]
  exact sub_eq_zero.mpr hc

end
end GaloisForLFunctions.HTGeometry.ComplexMetricField
