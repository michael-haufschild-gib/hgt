import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRecoveryCommutator

/-!
# Positivity of the recovery self-commutator is exactly gap log-convexity

A convergent quadratic-form expansion on the actual Hilbert basis identifies
positivity on the entire completion with nonnegative diagonal weights. This is
equivalent to increasing shift weights and to log-convexity of the optimal
physical recovery gaps. The equivalence does not assert that either holds.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial
attribute [local instance] cubicGradedLineNormedGroup cubicGradedLineInnerProductSpace
  cubicGradedLine_complete


def cubicRecoveryCommutatorWeight : ℕ → ℝ
  | 0 => (cubicRecoveryShiftWeight 0)^(2 : ℕ)
  | k+1 => (cubicRecoveryShiftWeight (k+1))^(2 : ℕ)-(cubicRecoveryShiftWeight k)^(2 : ℕ)

theorem cubicRecoveryCommutator_basis (k : ℕ) :
    cubicRecoveryCommutator (cubicHilbertBasis k)=
      cubicRecoveryCommutatorWeight k • cubicHilbertBasis k := by
  cases k with
  | zero => exact cubicRecoveryCommutator_zero_basis
  | succ k => exact cubicRecoveryCommutator_successor_basis k

theorem cubicRecoveryCommutator_quadratic_hasSum (x : cubicDefectHilbert) :
    HasSum (fun k : ℕ => cubicRecoveryCommutatorWeight k*(cubicHilbertBasis.repr x k)^(2 : ℕ))
      (inner ℝ x (cubicRecoveryCommutator x)) := by
  let F := (innerSL ℝ x).comp cubicRecoveryCommutator
  have hs := (cubicHilbertBasis.hasSum_repr x).mapL F
  have he : (fun k : ℕ => F (cubicHilbertBasis.repr x k • cubicHilbertBasis k))=
      (fun k : ℕ => cubicRecoveryCommutatorWeight k*(cubicHilbertBasis.repr x k)^(2 : ℕ)) := by
    funext k
    simp only [F,ContinuousLinearMap.comp_apply,map_smul,innerSL_apply_apply,
      cubicRecoveryCommutator_basis]
    change cubicHilbertBasis.repr x k*(cubicRecoveryCommutatorWeight k*
      inner ℝ x (cubicHilbertBasis k))=_
    rw [real_inner_comm (cubicHilbertBasis k) x,← HilbertBasis.repr_apply_apply]
    ring
  exact he ▸ hs

theorem cubicRecoveryCommutator_quadratic (x : cubicDefectHilbert) :
    inner ℝ x (cubicRecoveryCommutator x)=
      ∑' k : ℕ, cubicRecoveryCommutatorWeight k*(cubicHilbertBasis.repr x k)^(2 : ℕ) :=
  (cubicRecoveryCommutator_quadratic_hasSum x).tsum_eq.symm

theorem cubicRecoveryCommutator_positive_iff_weights :
    (∀ x : cubicDefectHilbert, 0 ≤ inner ℝ x (cubicRecoveryCommutator x)) ↔
      ∀ k, 0 ≤ cubicRecoveryCommutatorWeight k := by
  constructor
  · intro h k
    have hk := h (cubicHilbertBasis k)
    rw [cubicRecoveryCommutator_basis,real_inner_smul_right,cubicHilbertBasis_inner] at hk
    simpa only [ite_true,mul_one] using hk
  · intro h x
    rw [cubicRecoveryCommutator_quadratic]
    exact tsum_nonneg (fun k => mul_nonneg (h k) (sq_nonneg _))

theorem cubicRecoveryCommutatorWeight_nonneg_iff :
    (∀ k, 0 ≤ cubicRecoveryCommutatorWeight k) ↔
      ∀ k, cubicRecoveryShiftWeight k ≤ cubicRecoveryShiftWeight (k+1) := by
  constructor
  · intro h k
    have hk := h (k+1)
    change 0 ≤ (cubicRecoveryShiftWeight (k+1))^(2 : ℕ)-(cubicRecoveryShiftWeight k)^(2 : ℕ) at hk
    nlinarith [(cubicRecoveryShiftWeight_bounds k).1,(cubicRecoveryShiftWeight_bounds (k+1)).1]
  · intro h k
    cases k with
    | zero => exact sq_nonneg _
    | succ k =>
      change 0 ≤ (cubicRecoveryShiftWeight (k+1))^(2 : ℕ)-(cubicRecoveryShiftWeight k)^(2 : ℕ)
      have hs := h k
      have hp := (cubicRecoveryShiftWeight_bounds k).1
      have hq := (cubicRecoveryShiftWeight_bounds (k+1)).1
      nlinarith [mul_nonneg (sub_nonneg.mpr hs)
        (show 0 ≤ cubicRecoveryShiftWeight (k+1)+cubicRecoveryShiftWeight k by linarith)]

theorem cubicRecoveryShiftWeight_monotone_iff :
    (∀ k, cubicRecoveryShiftWeight k ≤ cubicRecoveryShiftWeight (k+1)) ↔
      ∀ k, (cubicGradedRecoveryGap (k+1))^(2 : ℕ) ≤
        cubicGradedRecoveryGap k*cubicGradedRecoveryGap (k+2) := by
  constructor
  · intro h k
    have hk := (div_le_div_iff₀ (cubicGradedRecoveryGap_positive k)
      (cubicGradedRecoveryGap_positive (k+1))).mp (h k)
    nlinarith
  · intro h k
    apply (div_le_div_iff₀ (cubicGradedRecoveryGap_positive k)
      (cubicGradedRecoveryGap_positive (k+1))).mpr
    nlinarith [h k]

theorem cubicRecoveryCommutator_positive_iff_logconvex :
    (∀ x : cubicDefectHilbert, 0 ≤ inner ℝ x (cubicRecoveryCommutator x)) ↔
      ∀ k, (cubicGradedRecoveryGap (k+1))^(2 : ℕ) ≤
        cubicGradedRecoveryGap k*cubicGradedRecoveryGap (k+2) := by
  rw [cubicRecoveryCommutator_positive_iff_weights,cubicRecoveryCommutatorWeight_nonneg_iff,
    cubicRecoveryShiftWeight_monotone_iff]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
