import GaloisForLFunctions.HTGeometry.ConnectionJetBianchi
import GaloisForLFunctions.HTGeometry.ComplexCoordinateDerivativeRules
import Mathlib.Data.Matrix.Basic

set_option autoImplicit false

namespace GaloisForLFunctions.HTGeometry.ComplexCoordinateConnection
open ScalarTwoJet
noncomputable section
variable {d n : ℕ}

/-- An actual complex connection field on a real coordinate chart. -/
abbrev Field (d n : ℕ) := (Fin d → ℝ) → Fin d → Matrix (Fin n) (Fin n) ℂ

/-- Entrywise actual coordinate derivative of a matrix field. -/
def matrixPartial (M : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ)
    (x : Fin d → ℝ) (k : Fin d) : Matrix (Fin n) (Fin n) ℂ :=
  fun u v => coordDeriv k (fun y => M y u v) x

/-- Actual first coordinate derivatives of the connection matrices. -/
def first (A : Field d n) (x : Fin d → ℝ) (k i : Fin d) : Matrix (Fin n) (Fin n) ℂ :=
  fun u v => coordDeriv k (fun y => A y i u v) x

/-- Actual ordered second coordinate derivatives of the connection matrices. -/
def second (A : Field d n) (x : Fin d → ℝ) (k i j : Fin d) : Matrix (Fin n) (Fin n) ℂ :=
  fun u v => coordDeriv k (coordDeriv i (fun y => A y j u v)) x

/-- Curvature constructed from the actual connection and its actual first derivatives. -/
def curvature (A : Field d n) (x : Fin d → ℝ) (i j : Fin d) : Matrix (Fin n) (Fin n) ℂ :=
  ConnectionBianchi.curvature (A x) (first A x) i j

/-- Covariant exterior derivative, with the literal coordinate derivative of curvature. -/
def exteriorPartial (A : Field d n) (x : Fin d → ℝ) (k i j : Fin d) : Matrix (Fin n) (Fin n) ℂ :=
  matrixPartial (fun y => curvature A y i j) x k +
    A x k * curvature A x i j - curvature A x i j * A x k

private theorem matrix_mul_partial (M N : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ)
    (x : Fin d → ℝ) (hM : ∀ u v, DifferentiableAt ℝ (fun y => M y u v) x)
    (hN : ∀ u v, DifferentiableAt ℝ (fun y => N y u v) x) (k : Fin d) (u v : Fin n) :
    coordDeriv k (fun y => (M y * N y) u v) x =
      (matrixPartial M x k * N x + M x * matrixPartial N x k) u v := by
  simp only [Matrix.mul_apply, Matrix.add_apply, matrixPartial]
  rw [coordDeriv_sum (s := Finset.univ) (F := fun a y => M y u a * N y a v) (fun a _ => (hM u a).mul (hN a v))]
  simp_rw [coordDeriv_mul (hM u _) (hN _ v)]
  exact Finset.sum_add_distrib

/-- Every term in the curvature derivative is obtained by differentiating the actual field. -/
theorem curvature_partial (A : Field d n) (x : Fin d → ℝ)
    (hA : ∀ i u v, ContDiffAt ℝ 2 (fun y => A y i u v) x) (k i j : Fin d) :
    matrixPartial (fun y => curvature A y i j) x k =
      ConnectionBianchi.curvaturePartial (A x) (first A x) (second A x) k i j := by
  have hd (a : Fin d) (u v : Fin n) := (hA a u v).differentiableAt (by norm_num)
  have hfirst (a b : Fin d) (u v : Fin n) :
      DifferentiableAt ℝ (fun y => first A y a b u v) x :=
    (coordDeriv_hasFDerivAt (hA b u v) a).differentiableAt
  have hmul (a b : Fin d) (u v : Fin n) :
      DifferentiableAt ℝ (fun y => (A y a * A y b) u v) x := by
    change DifferentiableAt ℝ (fun y => ∑ m, A y a u m * A y b m v) x
    exact DifferentiableAt.fun_sum (fun m _ => (hd a u m).mul (hd b m v))
  ext u v
  have hdiff : DifferentiableAt ℝ (fun y => first A y i j u v - first A y j i u v) x :=
    (hfirst i j u v).sub (hfirst j i u v)
  have hsum : DifferentiableAt ℝ (fun y => first A y i j u v - first A y j i u v +
      (A y i * A y j) u v) x := hdiff.add (hmul i j u v)
  simp only [matrixPartial, curvature, ConnectionBianchi.curvature, Matrix.sub_apply, Matrix.add_apply]
  rw [coordDeriv_sub hsum (hmul j i u v),
    coordDeriv_add hdiff (hmul i j u v),
    coordDeriv_sub (hfirst i j u v) (hfirst j i u v),
    matrix_mul_partial _ _ x (hd i) (hd j), matrix_mul_partial _ _ x (hd j) (hd i)]
  simp only [ConnectionBianchi.curvaturePartial, Matrix.add_apply, Matrix.sub_apply]
  have hm (a : Fin d) : matrixPartial (fun y => A y a) x k = first A x k a := rfl
  rw [hm i, hm j]
  dsimp only [first, second]
  ring

/-- Differential Bianchi identity for an actual C2 complex connection on real coordinates. -/
theorem bianchi (A : Field d n) (x : Fin d → ℝ)
    (hA : ∀ i u v, ContDiffAt ℝ 2 (fun y => A y i u v) x) (k i j : Fin d) :
    exteriorPartial A x k i j + exteriorPartial A x i j k + exteriorPartial A x j k i = 0 := by
  have hs (a b c : Fin d) : second A x a b c = second A x b a c := by
    ext u v
    exact coordDeriv_comm (hA c u v) a b
  simp only [exteriorPartial]
  rw [curvature_partial A x hA, curvature_partial A x hA, curvature_partial A x hA]
  exact ConnectionBianchi.bianchi (A x) (first A x) (second A x) hs k i j

/-- The actual curvature is alternating in its coordinate-form slots. -/
theorem curvature_skew (A : Field d n) (x : Fin d → ℝ) (i j : Fin d) :
    curvature A x i j = -curvature A x j i :=
  ConnectionBianchi.curvature_skew (A x) (first A x) i j

/-- Full tensor covariant derivative, retaining connection action on both form indices. -/
def tensorPartial (A : Field d d) (x : Fin d → ℝ) (k i j : Fin d)
    (u v : Fin d) : ℂ :=
  exteriorPartial A x k i j u v -
    ∑ a, (A x k a i * curvature A x a j u v + A x k a j * curvature A x i a u v)

/-- Full coordinate differential Bianchi identity for an actual torsion-free connection. -/
theorem tensor_bianchi (A : Field d d) (x : Fin d → ℝ)
    (hA : ∀ i u v, ContDiffAt ℝ 2 (fun y => A y i u v) x)
    (ht : ∀ a b c, A x a c b = A x b c a) (k i j u v : Fin d) :
    tensorPartial A x k i j u v + tensorPartial A x i j k u v +
      tensorPartial A x j k i u v = 0 := by
  have he := congrArg (fun M => M u v) (bianchi A x hA k i j)
  have hf (a b : Fin d) : curvature A x a b u v = -curvature A x b a u v :=
    congrArg (fun M => M u v) (curvature_skew A x a b)
  have hs : (∑ a, (A x k a i * curvature A x a j u v + A x k a j * curvature A x i a u v)) +
      (∑ a, (A x i a j * curvature A x a k u v + A x i a k * curvature A x j a u v)) +
      (∑ a, (A x j a k * curvature A x a i u v + A x j a i * curvature A x k a u v)) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro a _
    rw [ht k i a, ht k j a, ht i j a, hf a j, hf a k, hf a i]
    ring
  simp only [Matrix.add_apply, Matrix.zero_apply] at he
  unfold tensorPartial
  linear_combination he - hs

end
end GaloisForLFunctions.HTGeometry.ComplexCoordinateConnection
