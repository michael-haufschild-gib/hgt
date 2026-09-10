import GaloisForLFunctions.HTGeometry.ConstraintLaplacian
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Neutral response drift in the constraint Laplacian

The marginal-projection mechanism of Araújo, arXiv:2609.05560, Corollary 3 applies to the
existing single-observer constraint Laplacian. Every finite-dimensional subspace supplies a
neutral sector, and its orthogonal complement decays with rate one. An explicit solution and
an explicit integrated bias separate the secular projection from the bounded transient.
-/
open scoped InnerProductSpace
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- Exact neutral-plus-decaying solution for a single-observer constraint operator. -/
def constraintResponseState (U : Submodule ℝ E) (x : E) (t : ℝ) : E :=
  U.starProjection x + Real.exp (-t) • (x - U.starProjection x)

/-- The neutral projection of the response state is constant. -/
theorem constraintResponseState_projection (U : Submodule ℝ E) (x : E) (t : ℝ) :
    U.starProjection (constraintResponseState U x t) = U.starProjection x := by
  have hp : U.starProjection (U.starProjection x) = U.starProjection x :=
    U.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x)
  simp [constraintResponseState, map_add, map_smul, map_sub, hp]

/-- The corpus's constraint Laplacian sees exactly the exponentially decaying component. -/
theorem constraintLaplacian_responseState (U : Submodule ℝ E) (x : E) (t : ℝ) :
    constraintLaplacian (fun _ : Fin 1 => U) (constraintResponseState U x t) =
      Real.exp (-t) • (x - U.starProjection x) := by
  rw [constraintLaplacian_apply]
  simp only [Fin.sum_univ_one]
  rw [constraintResponseState_projection]
  simp [constraintResponseState]

/-- The state solves the actual negative constraint-Laplacian ODE at every time. -/
theorem constraintResponseState_solves (U : Submodule ℝ E) (x : E) (t : ℝ) :
    HasDerivAt (constraintResponseState U x)
      (-constraintLaplacian (fun _ : Fin 1 => U) (constraintResponseState U x t)) t := by
  rw [constraintLaplacian_responseState]
  have h := (((hasDerivAt_id t).neg.exp).smul_const (x - U.starProjection x)).const_add
    (U.starProjection x)
  unfold constraintResponseState
  convert! h using 1
  simp only [Pi.neg_apply, id_eq, mul_neg, mul_one, neg_smul]

theorem constraintResponseState_initial (U : Submodule ℝ E) (x : E) :
    constraintResponseState U x 0 = x := by simp [constraintResponseState]

/-- Integrated scalar bias, separated into its neutral projection and its stable transient. -/
def constraintResponseMean (U : Submodule ℝ E) (x d : E) (m₀ t : ℝ) : ℝ :=
  m₀ + t * inner ℝ d (U.starProjection x) +
    (1 - Real.exp (-t)) * inner ℝ d (x - U.starProjection x)

/-- The mean derivative is the bias evaluated on the evolving disagreement state. -/
theorem constraintResponseMean_solves (U : Submodule ℝ E) (x d : E) (m₀ t : ℝ) :
    HasDerivAt (constraintResponseMean U x d m₀)
      (inner ℝ d (constraintResponseState U x t)) t := by
  have h₁ := ((hasDerivAt_id t).mul_const (inner ℝ d (U.starProjection x))).const_add m₀
  have h₂ := (((hasDerivAt_id t).neg.exp).const_sub 1).mul_const
    (inner ℝ d (x - U.starProjection x))
  unfold constraintResponseMean
  convert! h₁.add h₂ using 1
  simp [constraintResponseState, inner_add_right, real_inner_smul_right]

/-- Removing the secular term leaves the exact exponentially saturating transient. -/
theorem constraintResponseMean_transient (U : Submodule ℝ E) (x d : E) (m₀ t : ℝ) :
    constraintResponseMean U x d m₀ t - m₀ - t * inner ℝ d (U.starProjection x) =
      (1 - Real.exp (-t)) * inner ℝ d (x - U.starProjection x) := by
  unfold constraintResponseMean
  ring

/-- At every nonnegative time, the stable transient is bounded by its initial bias amplitude. -/
theorem constraintResponseMean_transient_bound (U : Submodule ℝ E) (x d : E) (m₀ s : ℝ) :
    |constraintResponseMean U x d m₀ (s ^ 2) - m₀ - s ^ 2 * inner ℝ d (U.starProjection x)| ≤
      |inner ℝ d (x - U.starProjection x)| := by
  rw [constraintResponseMean_transient, abs_mul]
  have he0 := (Real.exp_pos (-(s ^ 2))).le
  have he1 : Real.exp (-(s ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg s]
  rw [abs_of_nonneg (sub_nonneg.mpr he1)]
  nlinarith [abs_nonneg (inner ℝ d (x - U.starProjection x))]

/-- Purely neutral data exhibit exact secular drift with no transient. -/
theorem constraintResponseMean_neutral_input (U : Submodule ℝ E) (x d : E) (m₀ t : ℝ) :
    constraintResponseMean U (U.starProjection x) d m₀ t =
      m₀ + t * inner ℝ d (U.starProjection x) := by
  have hp : U.starProjection (U.starProjection x) = U.starProjection x :=
    U.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x)
  simp [constraintResponseMean, hp]

/-- A transverse bias has zero secular coefficient, without an assumed orthogonality premise. -/
theorem constraintResponseMean_transverse_bias (U : Submodule ℝ E) (x d : E) (m₀ t : ℝ) :
    constraintResponseMean U x (d - U.starProjection d) m₀ t =
      m₀ + (1 - Real.exp (-t)) * inner ℝ (d - U.starProjection d) (x - U.starProjection x) := by
  have hz : inner ℝ (d - U.starProjection d) (U.starProjection x) = 0 :=
    U.starProjection_inner_eq_zero d _ (U.starProjection_apply_mem x)
  simp [constraintResponseMean, hz]

end
end GaloisForLFunctions.HTGeometry
