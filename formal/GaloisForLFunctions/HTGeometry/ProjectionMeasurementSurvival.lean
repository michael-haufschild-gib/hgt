import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Projective-measurement survival from projection defect

For an orthogonal projection `P` and a pure state `psi`, the Born probability of the
`P` outcome is the expectation `Re <psi, P psi>`.  Orthogonality makes this expectation
exactly `||P psi||^(2 : ℕ)`.  Consequently, for a unit vector,

`Re <psi, P psi> = 1 - ||P psi - psi||^(2 : ℕ)`.

Thus every upper bound on the distance from the projected subspace is already a lower bound
on projective-measurement survival.  This is a static Hilbert-space value identity: it assumes
no Hamiltonian, time evolution, or repeated-measurement limit.
-/

namespace HTGeometry

noncomputable section

variable {k E : Type*} [RCLike k]
  [NormedAddCommGroup E] [InnerProductSpace k E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The Born expectation of an orthogonal projection is the squared norm retained by that
projection. -/
theorem re_inner_starProjection_eq_norm_sq
    (S : Submodule k E) [S.HasOrthogonalProjection] (psi : E) :
    RCLike.re (inner k psi (S.starProjection psi)) =
      ‖S.starProjection psi‖ ^ (2 : ℕ) := by
  have hfixed :
      S.starProjection (S.starProjection psi) = S.starProjection psi :=
    S.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem psi)
  calc
    RCLike.re (inner k psi (S.starProjection psi)) =
        RCLike.re (inner k psi (S.starProjection (S.starProjection psi))) := by
      rw [hfixed]
    _ = RCLike.re (inner k (S.starProjection psi) (S.starProjection psi)) := by
      rw [← S.inner_starProjection_left_eq_right]
    _ = ‖S.starProjection psi‖ ^ (2 : ℕ) := inner_self_eq_norm_sq _

omit [CompleteSpace E] in
/-- Exact defect-survival balance for an arbitrary state.  The squared distance from `psi` to
its projected component is the total squared norm minus the Born expectation of the projection. -/
theorem norm_starProjection_sub_sq_eq_norm_sq_sub_re_inner
    (S : Submodule k E) [S.HasOrthogonalProjection] (psi : E) :
    ‖S.starProjection psi - psi‖ ^ (2 : ℕ) =
      ‖psi‖ ^ (2 : ℕ) - RCLike.re (inner k psi (S.starProjection psi)) := by
  have hpythagoras := S.norm_sq_eq_add_norm_sq_starProjection psi
  rw [S.starProjection_orthogonal_val psi] at hpythagoras
  rw [re_inner_starProjection_eq_norm_sq S psi]
  rw [show S.starProjection psi - psi = -(psi - S.starProjection psi) by abel,
    norm_neg]
  nlinarith [hpythagoras]

omit [CompleteSpace E] in
/-- **Born survival law.**  For a unit pure state, projective-measurement survival is exactly one
minus the squared projection defect. -/
theorem bornSurvivalProbability_eq_one_sub_projectionDefectSq
    (S : Submodule k E) [S.HasOrthogonalProjection] (psi : E)
    (hpsi : ‖psi‖ = 1) :
    RCLike.re (inner k psi (S.starProjection psi)) =
      1 - ‖S.starProjection psi - psi‖ ^ (2 : ℕ) := by
  have hbalance := norm_starProjection_sub_sq_eq_norm_sq_sub_re_inner S psi
  rw [hpsi, one_pow] at hbalance
  linarith

omit [CompleteSpace E] in
/-- A projection-defect upper bound is, without loss of constants, a Born-survival lower bound. -/
theorem one_sub_le_bornSurvivalProbability_of_projectionDefectSq_le
    (S : Submodule k E) [S.HasOrthogonalProjection] (psi : E)
    (hpsi : ‖psi‖ = 1) {epsilon : ℝ}
    (hdefect : ‖S.starProjection psi - psi‖ ^ (2 : ℕ) ≤ epsilon) :
    1 - epsilon ≤ RCLike.re (inner k psi (S.starProjection psi)) := by
  rw [bornSurvivalProbability_eq_one_sub_projectionDefectSq S psi hpsi]
  linarith

end

end HTGeometry
