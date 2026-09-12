import GaloisForLFunctions.HTGeometry.ComplexMetricBianchiContraction
import Mathlib.LinearAlgebra.Matrix.Trace

set_option autoImplicit false
namespace GaloisForLFunctions.HTGeometry.ComplexCoordinateConnection
open ScalarTwoJet CurvatureContraction
noncomputable section
variable {d : ℕ}

/-- Ricci curvature of the actual connection. -/
def ricciField (A : Field d d) (x : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  fun b j => ∑ u, curvature A x u j u b

/-- Covariant derivative of a covariant two-tensor field, with both index actions. -/
def covariantTwo (A : Field d d) (S : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℂ)
    (x : Fin d → ℝ) (k : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  matrixPartial S x k - (A x k).transpose*S x - S x*A x k

/-- Taking the Ricci trace commutes with the full covariant derivative. -/
theorem ricciTrace_tensorPartial (A : Field d d) (x : Fin d → ℝ)
    (hA : ∀ i u v, ContDiffAt ℝ 2 (fun y => A y i u v) x) (k b j : Fin d) :
    ricciTrace (tensorPartial A x) k b j = covariantTwo A (ricciField A) x k b j := by
  have hd : coordDeriv k (fun y => ∑ u, curvature A y u j u b) x =
      ∑ u, coordDeriv k (fun y => curvature A y u j u b) x :=
    coordDeriv_sum (fun u _ => curvature_differentiableAt A x hA u j u b) k
  have hc : (∑ u, ∑ a, A x k u a*curvature A x u j a b) =
      ∑ u, ∑ a, A x k a u*curvature A x a j u b := Finset.sum_comm
  unfold ricciTrace covariantTwo ricciField
  simp only [tensorPartial, exteriorPartial, matrixPartial, Matrix.sub_apply,
    Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [hd]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  rw [hc]
  have h1 : (∑ u, ∑ a, curvature A x u j u a*A x k a b) =
      ∑ a, ∑ u, A x k a b*curvature A x u j u a := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro u _
    ring
  have h2 : (∑ u, ∑ a, A x k a j*curvature A x u a u b) =
      ∑ a, ∑ u, curvature A x u a u b*A x k a j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [h1,h2]
  ring

/-- Bilinear contraction, without a complex conjugation. -/
def tensorPair (H S : Matrix (Fin d) (Fin d) ℂ) : ℂ := ∑ b, ∑ j, H b j*S b j

/-- The contraction is a matrix trace, with its index order explicit. -/
theorem tensorPair_trace (H S : Matrix (Fin d) (Fin d) ℂ) :
    tensorPair H S = Matrix.trace (H.transpose*S) := by
  unfold tensorPair Matrix.trace
  simp only [Matrix.diag,Matrix.mul_apply,Matrix.transpose_apply]
  exact Finset.sum_comm

/-- Full product rule for inverse-metric/tensor contraction. -/
theorem tensorPair_partial (H S : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℂ)
    (x : Fin d → ℝ) (hH : ∀ u v, DifferentiableAt ℝ (fun y => H y u v) x)
    (hS : ∀ u v, DifferentiableAt ℝ (fun y => S y u v) x) (k : Fin d) :
    coordDeriv k (fun y => tensorPair (H y) (S y)) x =
      tensorPair (matrixPartial H x k) (S x)+tensorPair (H x) (matrixPartial S x k) := by
  unfold tensorPair
  rw [coordDeriv_sum (s := Finset.univ) (F := fun b y => ∑ j, H y b j*S y b j)
    (fun b _ => DifferentiableAt.fun_sum (fun j _ => (hH b j).mul (hS b j))) k]
  have hj (b : Fin d) := coordDeriv_sum (s := Finset.univ)
    (F := fun j y => H y b j*S y b j) (fun j _ => (hH b j).mul (hS b j)) k
  simp_rw [hj]
  simp_rw [coordDeriv_mul (hH _ _) (hS _ _)]
  simp only [Finset.sum_add_distrib,matrixPartial]

/-- Inverse metric compatibility cancels precisely the two covariant index actions. -/
theorem tensorPair_covariant (H S A P : Matrix (Fin d) (Fin d) ℂ) :
    tensorPair H (P-A.transpose*S-S*A) =
      tensorPair (-(A*H+H*A.transpose)) S+tensorPair H P := by
  simp only [tensorPair_trace,Matrix.transpose_neg,Matrix.transpose_add,
    Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.neg_mul,Matrix.add_mul,
    Matrix.mul_sub,Matrix.trace_sub,Matrix.trace_neg,Matrix.trace_add]
  rw [← Matrix.mul_assoc H.transpose A.transpose S]
  rw [Matrix.trace_mul_cycle' H.transpose S A, ← Matrix.mul_assoc A H.transpose S]
  ring

end
end GaloisForLFunctions.HTGeometry.ComplexCoordinateConnection

namespace GaloisForLFunctions.HTGeometry.ComplexMetricField
open ScalarTwoJet ComplexCoordinateConnection CurvatureContraction
noncomputable section
variable {d : ℕ}

/-- Differentiability of each entry of the actual inverse metric. -/
theorem inverse_differentiableAt (g : Field d) (x : Fin d → ℝ)
    (hg : ∀ u v, DifferentiableAt ℝ (fun y => g y u v) x)
    (hdet : (g x).det ≠ 0) (u v : Fin d) :
    DifferentiableAt ℝ (fun y => (g y)⁻¹ u v) x := by
  have hd (M : Field d) (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x) :
      DifferentiableAt ℝ (fun y => (M y).det) x := by
    simp only [Matrix.det_apply']
    fun_prop
  have ha : DifferentiableAt ℝ (fun y => (g y).adjugate u v) x := by
    have he : (fun y => (g y).adjugate u v) =
        fun y => ((g y).updateRow v (Pi.single u 1)).det := by
      funext y
      exact Matrix.adjugate_apply (g y) u v
    rw [he]
    apply hd
    intro i j
    by_cases hi : i = v
    · simpa [Matrix.updateRow_apply,hi] using
        (differentiableAt_const ((Pi.single u (1 : ℂ) : Fin d → ℂ) j) :
          DifferentiableAt ℝ (fun _ : Fin d → ℝ => (Pi.single u (1 : ℂ) : Fin d → ℂ) j) x)
    · simpa [Matrix.updateRow_apply,hi] using hg i j
  have he : (fun y => (g y)⁻¹ u v) = fun y => ((g y).det)⁻¹*(g y).adjugate u v := by
    funext y
    rw [Matrix.inv_def,Ring.inverse_eq_inv',Matrix.smul_apply,smul_eq_mul]
  rw [he]
  exact ((hd g hg).inv hdet).mul ha

/-- Metric compatibility commutes the full inverse contraction with actual differentiation. -/
theorem scalar_partial (g S : Field d) (x : Fin d → ℝ)
    (hg : ∀ u v, ContDiffAt ℝ 3 (fun y => g y u v) x)
    (hS : ∀ u v, DifferentiableAt ℝ (fun y => S y u v) x)
    (hdet : (g x).det ≠ 0) (hs : ∀ y u v, g y u v = g y v u) (k : Fin d) :
    coordDeriv k (fun y => tensorPair (g y)⁻¹ (S y)) x =
      tensorPair (g x)⁻¹ (covariantTwo (connection g) S x k) := by
  rw [tensorPair_partial _ _ x
    (inverse_differentiableAt g x (fun u v => (hg u v).differentiableAt (by norm_num)) hdet) hS,
    inverse_compatibility g x hg hdet hs]
  exact (tensorPair_covariant _ _ _ _).symm

/-- The scalar trace in contracted Bianchi is the actual scalar-curvature derivative. -/
theorem scalarTrace_eq_partial (g : Field d) (x : Fin d → ℝ)
    (hg : ∀ u v, ContDiffAt ℝ 3 (fun y => g y u v) x)
    (hdet : (g x).det ≠ 0) (hs : ∀ y u v, g y u v = g y v u) (k : Fin d) :
    scalarTrace (g x)⁻¹ (tensorPartial (connection g) x) k =
      coordDeriv k (fun y => tensorPair (g y)⁻¹ (ricciField (connection g) y)) x := by
  have hA := connection_contDiffAt g x hg hdet
  have hR (u v : Fin d) : DifferentiableAt ℝ (fun y => ricciField (connection g) y u v) x :=
    DifferentiableAt.fun_sum (fun a _ => curvature_differentiableAt (connection g) x hA a v a u)
  rw [scalar_partial g _ x hg hR hdet hs]
  unfold scalarTrace tensorPair
  simp_rw [ricciTrace_tensorPartial (connection g) x hA]

end
end GaloisForLFunctions.HTGeometry.ComplexMetricField
