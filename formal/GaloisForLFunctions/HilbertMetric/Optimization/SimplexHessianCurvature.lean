import GaloisForLFunctions.HilbertMetric.Optimization.WeightedSimplexResponse

/-!
# Simplex response as diagonal Hessian curvature

For a constant diagonal difference tensor, the affine connection is flat,
but its Hessian curvature has eigenvalues equal to the squared connection
coefficients and annihilates off-diagonal symmetric tensors. This is the
model of Kobayashi, arXiv:2611.16381, Theorem 5.5. Exponential coefficients
identify its normalized positive spectrum with the simplex sampling law,
and its diagonal curvature response with weighted simplex response.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HilbertMetric.Optimization
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Constant difference tensor from the Euclidean connection. -/
def diagonalDifference (a u v : ι → ℝ) : ι → ℝ := fun i => a i * u i * v i

/-- The corresponding connection in global affine coordinates. -/
def diagonalStatisticalConnection (a : ι → ℝ)
    (X Y : (ι → ℝ) → (ι → ℝ)) (x : ι → ℝ) : ι → ℝ :=
  fderiv ℝ Y x (X x) + diagonalDifference a (X x) (Y x)

theorem diagonalStatisticalConnection_constant (a u v x : ι → ℝ) :
    diagonalStatisticalConnection a (fun _ => u) (fun _ => v) x =
      diagonalDifference a u v := by
  have hd : fderiv ℝ (fun _ : ι → ℝ => v) x = 0 :=
    congrFun (fderiv_const (𝕜 := ℝ) (E := ι → ℝ) v) x
  rw [diagonalStatisticalConnection, hd]
  simp

theorem diagonalStatisticalConnection_constant_fun (a u v : ι → ℝ) :
    diagonalStatisticalConnection a (fun _ => u) (fun _ => v) =
      fun _ => diagonalDifference a u v :=
  funext (diagonalStatisticalConnection_constant a u v)

/-- Symmetry of the constant Christoffel coefficients gives zero torsion. -/
theorem diagonalStatisticalConnection_torsion (a u v x : ι → ℝ) :
    diagonalStatisticalConnection a (fun _ => u) (fun _ => v) x =
      diagonalStatisticalConnection a (fun _ => v) (fun _ => u) x := by
  simp only [diagonalStatisticalConnection_constant]
  funext i
  dsimp only [diagonalDifference]
  ring

/-- The covariant derivative of the Euclidean metric is the fully symmetric diagonal cubic. -/
theorem diagonalStatisticalConnection_cubic (a u v w x : ι → ℝ) :
    (∑ i, -(diagonalStatisticalConnection a (fun _ => u) (fun _ => v) x i * w i +
      v i * diagonalStatisticalConnection a (fun _ => u) (fun _ => w) x i)) =
      ∑ i, (-2 * a i) * u i * v i * w i := by
  simp only [diagonalStatisticalConnection_constant]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [diagonalDifference]
  ring

/-- The curvature vanishes on the constant frame, hence all its coordinate components vanish. -/
theorem diagonalStatisticalConnection_flat (a u v w x : ι → ℝ) :
    diagonalStatisticalConnection a (fun _ => u)
        (diagonalStatisticalConnection a (fun _ => v) (fun _ => w)) x -
      diagonalStatisticalConnection a (fun _ => v)
        (diagonalStatisticalConnection a (fun _ => u) (fun _ => w)) x = 0 := by
  simp only [diagonalStatisticalConnection_constant_fun]
  funext i
  simp only [Pi.sub_apply, Pi.zero_apply, diagonalDifference]
  ring

/-- Minus the covariant derivative of the constant difference tensor. -/
def diagonalHessianTensor (a u v w z : ι → ℝ) : ℝ :=
  ∑ i, (diagonalDifference a (diagonalDifference a u v) w i +
      diagonalDifference a v (diagonalDifference a u w) i -
      diagonalDifference a u (diagonalDifference a v w) i) * z i

omit [DecidableEq ι] in
theorem diagonalHessianTensor_eq (a u v w z : ι → ℝ) :
    diagonalHessianTensor a u v w z = ∑ i, a i ^ 2 * u i * v i * w i * z i := by
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [diagonalDifference]
  ring

/-- The tensor is the negative covariant derivative for the actual constant-frame connection. -/
theorem diagonalHessianTensor_connection (a u v w z x : ι → ℝ) :
    diagonalHessianTensor a u v w z =
      ∑ i, -(diagonalStatisticalConnection a (fun _ => u)
          (fun _ => diagonalDifference a v w) x i -
        diagonalDifference a
          (diagonalStatisticalConnection a (fun _ => u) (fun _ => v) x) w i -
        diagonalDifference a v
          (diagonalStatisticalConnection a (fun _ => u) (fun _ => w) x) i) * z i := by
  simp only [diagonalStatisticalConnection_constant]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Curvature operator in the Frobenius metric; it preserves symmetric matrices. -/
def diagonalHessianOperator (a : ι → ℝ) (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => a i ^ 2 * A i i)

/-- The operator realizes the four-tensor on symmetric rank-one tensors. -/
theorem diagonalHessianOperator_rankOne (a u v : ι → ℝ) :
    (∑ i, ∑ j, diagonalHessianOperator a (fun k l => u k * u l) i j * (v i * v j)) =
      diagonalHessianTensor a u u v v := by
  rw [diagonalHessianTensor_eq]
  simp only [diagonalHessianOperator, Matrix.diagonal_apply]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Every diagonal matrix is acted on coordinatewise by the squared coefficients. -/
omit [Fintype ι] in
theorem diagonalHessianOperator_diagonal (a v : ι → ℝ) :
    diagonalHessianOperator a (Matrix.diagonal v) =
      Matrix.diagonal (fun i => a i ^ 2 * v i) := by
  simp only [diagonalHessianOperator, Matrix.diagonal_apply_eq]

/-- The Hessian curvature quadratic form is an explicit sum of squares. -/
theorem diagonalHessianOperator_energy (a : ι → ℝ) (A : Matrix ι ι ℝ) :
    (∑ i, ∑ j, diagonalHessianOperator a A i j * A i j) =
      ∑ i, (a i * A i i) ^ 2 := by
  simp only [diagonalHessianOperator, Matrix.diagonal_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro i _
  ring

variable {n : ℕ}

/-- Constant connection coefficients realizing the inverse simplex metric. -/
def simplexStatisticalCoefficient (c : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  -Real.exp (-c i / 2)

theorem simplexStatisticalCoefficient_sq (c : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    simplexStatisticalCoefficient c i ^ 2 = simplexCompliance c i := by
  rw [simplexStatisticalCoefficient, neg_sq, pow_two, ← Real.exp_add]
  have he : -c i / 2 + -c i / 2 = -c i := by ring
  rw [he, Real.exp_neg]
  rfl

/-- The positive principal curvatures, normalized by their sum, give the sampling law. -/
theorem simplexHessian_normalized_spectrum (c : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    simplexStatisticalCoefficient c i ^ 2 /
      (∑ j, simplexStatisticalCoefficient c j ^ 2) = simplexSampling c i := by
  simp only [simplexStatisticalCoefficient_sq, simplexSampling, simplexComplianceMass]

/-- Applying curvature to a centered diagonal tensor gives the constrained response. -/
theorem simplexHessian_weighted_response (c g : Fin (n + 1) → ℝ) :
    diagonalHessianOperator (simplexStatisticalCoefficient c)
        (Matrix.diagonal (fun i => g i - simplexDualMean c g)) =
      Matrix.diagonal (weightedSimplexResponse c g) := by
  rw [diagonalHessianOperator_diagonal]
  congr 1
  funext i
  rw [simplexStatisticalCoefficient_sq]
  rfl

/-- No diagonal curvature is invisible; the kernel consists exactly of off-diagonal tensors. -/
theorem simplexHessian_kernel (c : Fin (n + 1) → ℝ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    diagonalHessianOperator (simplexStatisticalCoefficient c) A = 0 ↔ ∀ i, A i i = 0 := by
  constructor
  · intro h i
    have hi := congrFun (congrFun h i) i
    simp only [diagonalHessianOperator, Matrix.diagonal_apply_eq, Matrix.zero_apply,
      simplexStatisticalCoefficient_sq, simplexCompliance] at hi
    exact (mul_eq_zero.mp hi).resolve_left (inv_ne_zero (Real.exp_ne_zero _))
  · intro h
    ext i j
    simp only [diagonalHessianOperator, h, mul_zero, Matrix.diagonal_zero, Matrix.zero_apply]

#print axioms diagonalStatisticalConnection_flat
#print axioms diagonalStatisticalConnection_cubic
#print axioms diagonalHessianTensor_connection
#print axioms diagonalHessianOperator_rankOne
#print axioms simplexHessian_normalized_spectrum
#print axioms simplexHessian_weighted_response
#print axioms simplexHessian_kernel

end
end GaloisForLFunctions.HilbertMetric.Optimization
