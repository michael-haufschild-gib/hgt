import GaloisForLFunctions.HTGeometry.ComplexMetricCurvatureSymmetry

set_option autoImplicit false
namespace GaloisForLFunctions.HTGeometry.ComplexCoordinateConnection
open ScalarTwoJet Filter Topology
noncomputable section
variable {d n : ℕ}

theorem matrix_mul_differentiableAt
    (M N : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ) (x : Fin d → ℝ)
    (hM : ∀ u v, DifferentiableAt ℝ (fun y => M y u v) x)
    (hN : ∀ u v, DifferentiableAt ℝ (fun y => N y u v) x) (u v : Fin n) :
    DifferentiableAt ℝ (fun y => (M y*N y) u v) x := by
  change DifferentiableAt ℝ (fun y => ∑ a, M y u a*N y a v) x
  exact DifferentiableAt.fun_sum (fun a _ => (hM u a).mul (hN a v))

theorem matrixPartial_add
    (M N : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ) (x : Fin d → ℝ)
    (hM : ∀ u v, DifferentiableAt ℝ (fun y => M y u v) x)
    (hN : ∀ u v, DifferentiableAt ℝ (fun y => N y u v) x) (k : Fin d) :
    matrixPartial (fun y => M y+N y) x k = matrixPartial M x k+matrixPartial N x k := by
  ext u v
  exact coordDeriv_add (hM u v) (hN u v) k

theorem matrixPartial_transpose (M : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ)
    (x : Fin d → ℝ) (k : Fin d) :
    matrixPartial (fun y => (M y).transpose) x k = (matrixPartial M x k).transpose := rfl

theorem matrixPartial_zero (x : Fin d → ℝ) (k : Fin d) :
    matrixPartial (fun _ : Fin d → ℝ => (0 : Matrix (Fin n) (Fin n) ℂ)) x k = 0 := by
  ext u v
  simp [matrixPartial, coordDeriv]

/-- The metric-skew defect is a linear map, so all form-index connection actions
remain within its kernel. -/
def metricSkewMap (G : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun R := R.transpose*G+G*R
  map_add' R S := by
    simp only [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' c R := by
    change (c • R).transpose*G+G*(c • R) = c • (R.transpose*G+G*R)
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add]

/-- Differentiating metric skewness with the original compatible connection
keeps all coefficient derivatives and both endomorphism connection terms. -/
theorem covariant_metric_skew
    (g R : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin d → ℝ) (k : Fin d)
    (hg : ∀ u v, DifferentiableAt ℝ (fun y => g y u v) x)
    (hR : ∀ u v, DifferentiableAt ℝ (fun y => R y u v) x)
    (hmet : matrixPartial g x k = A.transpose*g x+g x*A)
    (hsk : (fun y => (R y).transpose*g y+g y*R y) =ᶠ[𝓝 x] fun _ => 0) :
    metricSkewMap (g x) (matrixPartial R x k+A*R x-R x*A) = 0 := by
  have hd := matrixPartial_congr hsk k
  rw [matrixPartial_zero,
    matrixPartial_add (fun y => (R y).transpose*g y) (fun y => g y*R y) x
      (matrix_mul_differentiableAt _ _ x (fun u v => hR v u) hg)
      (matrix_mul_differentiableAt _ _ x hg hR) k,
    matrixPartial_mul (fun y => (R y).transpose) g x (fun u v => hR v u) hg k,
    matrixPartial_mul g R x hg hR k, matrixPartial_transpose] at hd
  have h0 := hsk.self_of_nhds
  change (R x).transpose*g x+g x*R x = 0 at h0
  change (matrixPartial R x k+A*R x-R x*A).transpose*g x+
    g x*(matrixPartial R x k+A*R x-R x*A) = 0
  calc
    _ = ((matrixPartial R x k).transpose*g x+(R x).transpose*matrixPartial g x k+
        (matrixPartial g x k*R x+g x*matrixPartial R x k)) -
        A.transpose*((R x).transpose*g x+g x*R x) -
        ((R x).transpose*g x+g x*R x)*A := by
      rw [hmet]
      simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul]
      noncomm_ring
    _ = 0 := by rw [hd,h0]; simp

/-- Curvature of a C2 connection has actual differentiable entries. -/
theorem curvature_differentiableAt (A : Field d n) (x : Fin d → ℝ)
    (hA : ∀ i u v, ContDiffAt ℝ 2 (fun y => A y i u v) x) (i j : Fin d) (u v : Fin n) :
    DifferentiableAt ℝ (fun y => curvature A y i j u v) x := by
  have ha (k a b) := (hA k a b).differentiableAt (by norm_num)
  have hf (k l a b) : DifferentiableAt ℝ (fun y => first A y k l a b) x :=
    (coordDeriv_hasFDerivAt (hA l a b) k).differentiableAt
  exact (((hf i j u v).sub (hf j i u v)).add
    (matrix_mul_differentiableAt (fun y => A y i) (fun y => A y j) x (ha i) (ha j) u v)).sub
    (matrix_mul_differentiableAt (fun y => A y j) (fun y => A y i) x (ha j) (ha i) u v)

/-- Matrix form of the full tensor derivative, including both form-index actions. -/
theorem tensorPartial_eq (A : Field d d) (x : Fin d → ℝ) (k i j : Fin d) :
    (tensorPartial A x k i j : Matrix (Fin d) (Fin d) ℂ) =
      exteriorPartial A x k i j -
        ∑ a, (A x k a i • curvature A x a j + A x k a j • curvature A x i a) := by
  ext u v
  simp only [tensorPartial, Matrix.sub_apply, Matrix.sum_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]

/-- The full covariant derivative retains alternation in its curvature-form slots. -/
theorem tensorPartial_form_skew (A : Field d d) (x : Fin d → ℝ)
    (hA : ∀ i u v, ContDiffAt ℝ 2 (fun y => A y i u v) x) (k i j : Fin d) :
    (tensorPartial A x k i j : Matrix (Fin d) (Fin d) ℂ) + tensorPartial A x k j i = 0 := by
  have hc : (fun y => curvature A y i j+curvature A y j i) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [] with y
    rw [curvature_skew A y i j]
    exact neg_add_cancel _
  have hd := matrixPartial_congr hc k
  have hc0 : curvature A x i j+curvature A x j i = 0 := hc.self_of_nhds
  rw [matrixPartial_add (fun y => curvature A y i j) (fun y => curvature A y j i) x
      (curvature_differentiableAt A x hA i j) (curvature_differentiableAt A x hA j i) k,
    matrixPartial_zero] at hd
  have he : exteriorPartial A x k i j+exteriorPartial A x k j i = 0 := by
    unfold exteriorPartial
    calc
      _ = (matrixPartial (fun y => curvature A y i j) x k+
          matrixPartial (fun y => curvature A y j i) x k) +
          A x k*(curvature A x i j+curvature A x j i) -
          (curvature A x i j+curvature A x j i)*A x k := by noncomm_ring
      _ = 0 := by rw [hd, hc0]; simp
  have hs : (∑ a, (A x k a i • curvature A x a j+A x k a j • curvature A x i a)) +
      (∑ a, (A x k a j • curvature A x a i+A x k a i • curvature A x j a)) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro a _
    rw [curvature_skew A x a i, curvature_skew A x j a]
    simp only [smul_neg]
    abel
  rw [tensorPartial_eq, tensorPartial_eq]
  calc
    _ = (exteriorPartial A x k i j+exteriorPartial A x k j i) -
        ((∑ a, (A x k a i • curvature A x a j+A x k a j • curvature A x i a)) +
        (∑ a, (A x k a j • curvature A x a i+A x k a i • curvature A x j a))) := by abel
    _ = 0 := by rw [he,hs]; simp

end
end GaloisForLFunctions.HTGeometry.ComplexCoordinateConnection

namespace GaloisForLFunctions.HTGeometry.ComplexMetricField
open ScalarTwoJet ComplexCoordinateConnection Filter Topology
noncomputable section
variable {d : ℕ}

/-- The actual covariant curvature derivative is metric-skew, with every
connection action retained and no curvature-symmetry premise. -/
theorem tensorPartial_metric_skew (g : Field d) (x : Fin d → ℝ)
    (hg : ∀ u v, ContDiffAt ℝ 3 (fun y => g y u v) x)
    (hdet : (g x).det ≠ 0) (hs : ∀ y u v, g y u v = g y v u) (k i j : Fin d) :
    metricSkewMap (g x) (tensorPartial (connection g) x k i j) = 0 := by
  have hgn : ∀ᶠ y in 𝓝 x, ∀ u v, ContDiffAt ℝ 3 (fun z => g z u v) y :=
    Filter.eventually_all.mpr fun u => Filter.eventually_all.mpr fun v =>
      (hg u v).eventually (by norm_num)
  have hc (u v : Fin d) : ContinuousAt (fun y => g y u v) x := (hg u v).continuousAt
  have hd : ContinuousAt (fun y => (g y).det) x := by
    simp only [Matrix.det_apply']
    fun_prop
  have hsk : (fun y => (curvature (connection g) y i j).transpose*g y+
      g y*curvature (connection g) y i j) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hgn,hd.eventually_ne hdet] with y hy hdy
    exact curvature_metric_skew g y hy hdy hs i j
  have hA := connection_contDiffAt g x hg hdet
  have he : metricSkewMap (g x) (exteriorPartial (connection g) x k i j) = 0 :=
    covariant_metric_skew g (fun y => curvature (connection g) y i j) (connection g x k) x k
      (fun u v => (hg u v).differentiableAt (by norm_num))
      (curvature_differentiableAt (connection g) x hA i j)
      (metric_compatibility g x hdet hs k) hsk
  rw [tensorPartial_eq, map_sub, map_sum,he]
  have hz (a : Fin d) : metricSkewMap (g x)
      (connection g x k a i • curvature (connection g) x a j+
        connection g x k a j • curvature (connection g) x i a) = 0 := by
    rw [map_add,map_smul,map_smul]
    change connection g x k a i •
      ((curvature (connection g) x a j).transpose*g x+g x*curvature (connection g) x a j) +
      connection g x k a j •
      ((curvature (connection g) x i a).transpose*g x+g x*curvature (connection g) x i a) = 0
    rw [curvature_metric_skew g x hg hdet hs a j,curvature_metric_skew g x hg hdet hs i a]
    simp
  simp_rw [hz]
  simp

end
end GaloisForLFunctions.HTGeometry.ComplexMetricField
