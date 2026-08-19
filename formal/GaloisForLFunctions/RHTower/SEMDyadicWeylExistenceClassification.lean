import GaloisForLFunctions.RHTower.TruncatedJetWeylBoundary
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Exact existence classification for internal SEM dyadic Weyl models

The determinant obstruction in `WeldWeylMultiplicity` is also sufficient.  If `2^k` divides the
actual SEM hole count, the ordinary cyclic clock--shift pair acts directly on that undoubled hole
space.  No auxiliary tensor factor and no arithmetic datum from the split enters the construction.

Consequently, existence of an internal SEM dyadic Weyl model is exactly hole-count divisibility.
Universal existence at one level is exactly the corresponding RH ladder rung; universal existence
at every level, or at cofinally many levels, is exactly RH.  Thus bare model existence is a sharp
certificate for the desired divisibility, but it is not an independent arithmetic producer of it.
-/

open Complex Matrix

noncomputable section

namespace RHTower

/-- The unit-holonomy boundary shift is the matrix of inverse cyclic rotation. -/
theorem boundaryCompletedJetShift_one_eq_finRotatePermMatrix (n : ℕ) :
    boundaryCompletedJetShift n 1 =
      Equiv.Perm.permMatrix ℂ
        ((finRotate (n + 1)).symm : Equiv.Perm (Fin (n + 1))) := by
  ext i j
  simp only [boundaryCompletedJetShift, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  by_cases hstep : (j : ℕ) + 1 = (i : ℕ)
  · have hj : j ≠ Fin.last n := by
      intro hjlast
      subst j
      simp only [Fin.val_last] at hstep
      exact (Nat.ne_of_lt i.isLt) hstep.symm
    have hrot : finRotate (n + 1) j = i := by
      apply Fin.ext
      rw [coe_finRotate_of_ne_last hj]
      exact hstep
    rw [if_pos hstep, if_pos]
    exact (Equiv.symm_apply_eq (finRotate (n + 1))).2 hrot.symm
  · rw [if_neg hstep]
    by_cases hwrap : (i : ℕ) = 0 ∧ (j : ℕ) = n
    · have hsymm : (finRotate (n + 1)).symm i = j := by
        have hi : i = 0 := Fin.ext hwrap.1
        have hj : j = Fin.last n := Fin.ext hwrap.2
        apply (finRotate (n + 1)).injective
        rw [(finRotate (n + 1)).apply_symm_apply]
        subst i
        subst j
        simp
      rw [if_pos hwrap, if_pos hsymm]
    · rw [if_neg hwrap, if_neg]
      intro hsymm
      have hrot : finRotate (n + 1) j = i := by
        exact ((Equiv.symm_apply_eq (finRotate (n + 1))).1 hsymm).symm
      by_cases hj : j = Fin.last n
      · have hi : i = 0 := by
          rw [← hrot, hj]
          simp
        apply hwrap
        exact ⟨congrArg Fin.val hi, congrArg Fin.val hj⟩
      · apply hstep
        rw [← coe_finRotate_of_ne_last hj]
        exact congrArg Fin.val hrot

/-- The unit-holonomy boundary shift is invertible, with transpose as a right inverse. -/
theorem boundaryCompletedJetShift_one_mul_transpose (n : ℕ) :
    boundaryCompletedJetShift n 1 * (boundaryCompletedJetShift n 1).transpose = 1 := by
  rw [boundaryCompletedJetShift_one_eq_finRotatePermMatrix, Matrix.transpose_permMatrix]
  rw [← Matrix.permMatrix_mul]
  simp

/-- The unit-holonomy boundary shift has nonzero determinant in every positive jet dimension. -/
theorem boundaryCompletedJetShift_one_det_ne_zero (n : ℕ) :
    (boundaryCompletedJetShift n 1).det ≠ 0 := by
  apply Matrix.det_ne_zero_of_right_inverse
  exact boundaryCompletedJetShift_one_mul_transpose n

/-- Dyadic divisibility of the actual hole count constructs an internal clock--shift model on the
undoubled SEM hole space.  The empty space is handled separately; every nonempty space uses the
unit-holonomy cyclic boundary shift. -/
theorem semDyadicWeylModel_of_pow_dvd_holeCount {k : ℕ}
    {ρ : ℂ} {r₀ R : ℝ} {N : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    {h : SEMSplitData ρ r₀ R N zs u} (hdvd : 2 ^ k ∣ zs.length) :
    Nonempty (SEMDyadicWeylModel k h) := by
  cases zs with
  | nil =>
      refine ⟨{
        U := 1
        V := 1
        det_U_ne_zero := by simp
        det_V_ne_zero := by simp
        weyl := ?_ }⟩
      ext i
      exact Fin.elim0 i
  | cons z zs =>
      let n := zs.length
      have hdvd' : 2 ^ k ∣ n + 1 := by
        simpa [n] using hdvd
      have hphase : Bottcher.dyadicRoot k ^ (n + 1) = 1 :=
        ((dyadicWeylPhase_isPrimitiveRoot k).pow_eq_one_iff_dvd (n + 1)).2 hdvd'
      refine ⟨{
        U := truncatedJetClock n (Bottcher.dyadicRoot k)
        V := boundaryCompletedJetShift n 1
        det_U_ne_zero := truncatedJetClock_det_ne_zero n
          ((dyadicWeylPhase_isPrimitiveRoot k).ne_zero
            (pow_ne_zero k (by norm_num)))
        det_V_ne_zero := boundaryCompletedJetShift_one_det_ne_zero n
        weyl := boundaryCompletedJetWeyl_of_phase_pow_card n
          (Bottcher.dyadicRoot k) 1 hphase }⟩

/-- **Exact local classification.** An internal depth-`k` SEM Weyl model exists exactly when the
actual undoubled hole count is divisible by `2^k`. -/
theorem semDyadicWeylModel_nonempty_iff_pow_dvd_holeCount {k : ℕ}
    {ρ : ℂ} {r₀ R : ℝ} {N : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    {h : SEMSplitData ρ r₀ R N zs u} :
    Nonempty (SEMDyadicWeylModel k h) ↔ 2 ^ k ∣ zs.length := by
  exact ⟨fun ⟨M⟩ => M.pow_dvd_holeCount, semDyadicWeylModel_of_pow_dvd_holeCount⟩

/-- **Source-blindness law.** Internal model existence depends only on hole-space dimension, not
on any other analytic or arithmetic datum of the SEM split. -/
theorem semDyadicWeylModel_nonempty_congr_holeCount {k : ℕ}
    {ρ ρ' : ℂ} {r₀ R r₀' R' : ℝ} {N N' : ℕ}
    {zs zs' : List ℂ} {u u' : ℂ → ℂ}
    {h : SEMSplitData ρ r₀ R N zs u} {h' : SEMSplitData ρ' r₀' R' N' zs' u'}
    (hlen : zs.length = zs'.length) :
    Nonempty (SEMDyadicWeylModel k h) ↔ Nonempty (SEMDyadicWeylModel k h') := by
  rw [semDyadicWeylModel_nonempty_iff_pow_dvd_holeCount,
    semDyadicWeylModel_nonempty_iff_pow_dvd_holeCount, hlen]

/-- At a fixed divisor centre, all dominating SEM presentations have the same internal-model
existence status. -/
theorem semDyadicWeylModel_nonempty_iff_of_semSplits {k : ℕ}
    {ρ : ℂ} {r₀ R r₀' R' : ℝ} {N N' : ℕ}
    {zs zs' : List ℂ} {u u' : ℂ → ℂ}
    {h : SEMSplitData ρ r₀ R N zs u} {h' : SEMSplitData ρ r₀' R' N' zs' u'} :
    Nonempty (SEMDyadicWeylModel k h) ↔ Nonempty (SEMDyadicWeylModel k h') := by
  apply semDyadicWeylModel_nonempty_congr_holeCount
  exact (semSplitData_count_eq h).symm.trans (semSplitData_count_eq h')

/-- **Levelwise route closure.** Universal internal SEM Weyl-model existence at depth `k` is
exactly the `k`-th RH ladder rung. -/
theorem rhLadder_iff_all_semDyadicWeylModels (k : ℕ) :
    RHLadder k ↔
      ∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∀ (r₀ R : ℝ) (N : ℕ) (zs : List ℂ) (u : ℂ → ℂ)
          (h : SEMSplitData ρ r₀ R N zs u),
          Nonempty (SEMDyadicWeylModel k h) := by
  constructor
  · intro hlad ρ hρ hzero r₀ R N zs u h
    apply semDyadicWeylModel_of_pow_dvd_holeCount
    rw [← semSplitData_count_eq h]
    exact (rhLadder_iff_toNat_dvd k).1 hlad ρ hρ hzero
  · exact rhLadder_of_semDyadicWeylModel k

/-- **All-level route closure.** Universal internal SEM Weyl models at every dyadic depth are
equivalent to RH; model existence is not a weaker source condition. -/
theorem riemannHypothesis_iff_all_semDyadicWeylModels :
    RiemannHypothesis ↔
      ∀ k : ℕ, ∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∀ (r₀ R : ℝ) (N : ℕ) (zs : List ℂ) (u : ℂ → ℂ)
          (h : SEMSplitData ρ r₀ R N zs u),
          Nonempty (SEMDyadicWeylModel k h) := by
  rw [rh_iff_forall_ladder]
  exact forall_congr' rhLadder_iff_all_semDyadicWeylModels

/-- **Cofinal route closure.** Cofinal internal SEM Weyl-model existence is also exactly RH. -/
theorem riemannHypothesis_iff_cofinal_semDyadicWeylModels :
    RiemannHypothesis ↔
      ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧
        ∀ ρ ∈ rightHalf, xi ρ = 0 →
          ∀ (r₀ R : ℝ) (N : ℕ) (zs : List ℂ) (u : ℂ → ℂ)
            (h : SEMSplitData ρ r₀ R N zs u),
            Nonempty (SEMDyadicWeylModel k h) := by
  constructor
  · intro hRH K
    refine ⟨K, le_rfl, ?_⟩
    exact (rhLadder_iff_all_semDyadicWeylModels K).1
      ((rh_iff_forall_ladder.1 hRH) K)
  · exact riemannHypothesis_of_cofinal_semDyadicWeylModels

end RHTower
