import GaloisForLFunctions.HTGeometry.QuantumNullSpaceTransport

/-!
# Sixth-order soft spectral filtering and rotating information

Equation (7) of arXiv:2609.07645 uses a sixth-order spectral cutoff.
With positive cutoff scale `delta = exp a`, the regular inverse is
`x^(5 : ℕ)/(x^(6 : ℕ)+delta^(6 : ℕ))`. The identities below hold even at zero eigenvalue.
On the corpus's rotating rank-one information projector, filtering changes
only the active eigenvalue and leaves the rotating null direction intact.
-/

open scoped BigOperators
noncomputable section
namespace HTGeometry

/-- Regularized inverse of a real eigenvalue, with strictly positive cutoff scale. -/
def quantumSoftInverse (a x : ℝ) : ℝ := x ^ (5 : ℕ) / (x ^ (6 : ℕ) + Real.exp a ^ (6 : ℕ))

/-- The fraction of the unregularized response suppressed by the cutoff. -/
def quantumSoftLoss (a x : ℝ) : ℝ := Real.exp a ^ (6 : ℕ) / (x ^ (6 : ℕ) + Real.exp a ^ (6 : ℕ))

private theorem soft_den_positive (a x : ℝ) : 0 < x ^ (6 : ℕ) + Real.exp a ^ (6 : ℕ) := by positivity

/-- Exact retained-plus-lost response decomposition, including the null eigenvalue. -/
theorem quantumSoft_response_partition (a x : ℝ) :
    x * quantumSoftInverse a x + quantumSoftLoss a x = 1 := by
  unfold quantumSoftInverse quantumSoftLoss
  field_simp [(soft_den_positive a x).ne']

/-- The regularized response retains the sign of the original nonzero eigenvalue. -/
theorem quantumSoftInverse_mul_nonnegative (a x : ℝ) : 0 ≤ x * quantumSoftInverse a x := by
  have h : x * quantumSoftInverse a x = x ^ (6 : ℕ) / (x ^ (6 : ℕ) + Real.exp a ^ (6 : ℕ)) := by
    unfold quantumSoftInverse
    ring
  rw [h]
  positivity

/-- Every response is attenuated by a factor strictly below one. -/
theorem quantumSoftInverse_mul_lt_one (a x : ℝ) : x * quantumSoftInverse a x < 1 := by
  have h := quantumSoft_response_partition a x
  have hp : 0 < quantumSoftLoss a x := by unfold quantumSoftLoss; positivity
  linarith

/-- No new zero eigenvalues are introduced by finite soft regularization. -/
theorem quantumSoftInverse_eq_zero_iff (a x : ℝ) : quantumSoftInverse a x = 0 ↔ x = 0 := by
  simp [quantumSoftInverse, div_eq_zero_iff, (soft_den_positive a x).ne']

/-- Opposite eigenvalues remain opposite after regularization. -/
theorem quantumSoftInverse_odd (a x : ℝ) : quantumSoftInverse a (-x) = -quantumSoftInverse a x := by
  unfold quantumSoftInverse
  ring

/-- Explicit differentiability at every eigenvalue, including the exact kernel. -/
theorem hasDerivAt_quantumSoftInverse (a x : ℝ) :
    HasDerivAt (quantumSoftInverse a)
      (x ^ (4 : ℕ) * (5 * Real.exp a ^ (6 : ℕ) - x ^ (6 : ℕ)) / (x ^ (6 : ℕ) + Real.exp a ^ (6 : ℕ)) ^ (2 : ℕ)) x := by
  have h := ((hasDerivAt_id x).pow 5).div
    (((hasDerivAt_id x).pow 6).add (hasDerivAt_const x (Real.exp a ^ (6 : ℕ))))
    (soft_den_positive a x).ne'
  exact h.congr_deriv (by dsimp; ring)

/-- Diagonal spectral regularization obeys the exact matrix response partition. -/
theorem quantumSoft_diagonal_partition {n : ℕ} (a : ℝ) (lambda : Fin n → ℝ) :
    Matrix.diagonal lambda * Matrix.diagonal (fun i => quantumSoftInverse a (lambda i)) +
      Matrix.diagonal (fun i => quantumSoftLoss a (lambda i)) = 1 := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact quantumSoft_response_partition a (lambda i)

/-- Soft information dimension is bounded by the number of available spectral channels. -/
theorem quantumSoft_effective_dimension_le (n : ℕ) (a : ℝ) (lambda : Fin n → ℝ) :
    ∑ i, lambda i * quantumSoftInverse a (lambda i) ≤ n := by
  calc
    _ ≤ ∑ _ : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ =>
      (quantumSoftInverse_mul_lt_one a (lambda i)).le
    _ = _ := by simp

/-- The filtered inverse on a rotating rank-one information projector. -/
def rotatingSoftInverse (a t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  quantumSoftInverse a 1 • rotatingInformation t

/-- Filtering rescales the active projector and does not change its orientation. -/
theorem rotatingSoft_response (a t : ℝ) :
    rotatingInformation t * rotatingSoftInverse a t =
      quantumSoftInverse a 1 • rotatingInformation t := by
  rw [rotatingSoftInverse, Matrix.mul_smul, rotatingInformation_idempotent]

/-- The old null direction's filtered quadratic response still follows the rotation angle. -/
theorem rotatingSoft_null_energy (a s t : ℝ) :
    (∑ i, ∑ j, rotatingNullDirection s i * rotatingSoftInverse a t i j * rotatingNullDirection s j) =
      quantumSoftInverse a 1 * Real.sin (t - s) ^ (2 : ℕ) := by
  have h := rotatingInformation_quadratic t (rotatingNullDirection s)
  rw [rotatingObservation_null_transport] at h
  rw [← h]
  simp only [rotatingSoftInverse, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end HTGeometry
