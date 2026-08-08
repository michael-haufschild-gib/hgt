import GaloisForLFunctions.RHTower.XiShiftedMomentFarRightAsymptotic
import GaloisForLFunctions.RHTower.XiShiftedHankelTerminalFlux
import GaloisForLFunctions.HTGeometry.ArcsineHankelPositiveDefinite
import GaloisForLFunctions.HTGeometry.PositiveDefiniteMatrixLimit

/-!
# Far-right positivity of every fixed shifted-Xi Hankel block

The all-order Xi moment recession is upgraded here from scalar convergence to matrix positivity.
After the exact diagonal congruence

`B(w) = (2w / log w) D(w) H(w²) D(w)`,  `D(w)ᵢᵢ = w^(2i)`,

the normalized block `B(w)` converges entrywise to the strictly positive-definite arcsine Hankel
block.  Openness of positive definiteness gives eventual positivity of `B(w)`, and invertibility of
the diagonal congruence transfers it back to the unnormalized shifted-Xi block `H(w²)`.

This is an unconditional least-defect-degree recession theorem: any failure of shifted Hankel
positivity must escape to unbounded polynomial degree as the mass moves to the far right.
-/

open Filter Matrix Topology
open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Moment normalization which exposes the universal arcsine limit. -/
def xiShiftedFarRightNormalizedMoment (w : ℝ) (k : ℕ) : ℝ :=
  2 * w ^ (2 * k + 1) / Real.log w *
    (xiShiftedReciprocalMoment (w ^ 2) k).re

/-- Normalized finite shifted-Xi Hankel block. -/
def xiShiftedFarRightNormalizedHankelMatrix (w : ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  _root_.HTGeometry.momentHankelMatrix (xiShiftedFarRightNormalizedMoment w) n

/-- Diagonal mass dilation implementing the exact congruence between normalized and original
shifted-Xi blocks. -/
def xiShiftedFarRightDilation (w : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => w ^ (2 * (i : ℕ)))

theorem xiShiftedFarRightNormalizedHankelMatrix_isHermitian (w : ℝ) (n : ℕ) :
    (xiShiftedFarRightNormalizedHankelMatrix w n).IsHermitian :=
  _root_.HTGeometry.momentHankelMatrix_isHermitian _ _

/-- Every normalized shifted-Xi Hankel entry converges to the matching arcsine moment. -/
theorem tendsto_xiShiftedFarRightNormalizedHankelMatrix_apply
    {n : ℕ} (i j : Fin n) :
    Tendsto
      (fun w : ℝ => xiShiftedFarRightNormalizedHankelMatrix w n i j)
      atTop
      (nhds ((_root_.HTGeometry.momentHankelMatrix normalizedCentralBinom n) i j)) := by
  simpa [xiShiftedFarRightNormalizedHankelMatrix,
    xiShiftedFarRightNormalizedMoment, _root_.HTGeometry.momentHankelMatrix] using
    tendsto_scaled_re_xiShiftedReciprocalMoment_squareParam ((i : ℕ) + (j : ℕ))

/-- Every fixed normalized shifted-Xi Hankel block is positive definite sufficiently far right. -/
theorem xiShiftedFarRightNormalizedHankelMatrix_posDef_eventually (n : ℕ) :
    ∀ᶠ w : ℝ in atTop, (xiShiftedFarRightNormalizedHankelMatrix w n).PosDef := by
  exact posDef_eventually_of_tendsto
    (normalizedCentralBinom_momentHankelMatrix_posDef n)
    (Filter.Eventually.of_forall fun w =>
      xiShiftedFarRightNormalizedHankelMatrix_isHermitian w n)
    tendsto_xiShiftedFarRightNormalizedHankelMatrix_apply

/-- Exact diagonal-congruence factorization of the far-right normalized block. -/
theorem xiShiftedFarRightNormalizedHankelMatrix_eq_congruence
    {w : ℝ} (hw : 1 < w) (n : ℕ) :
    xiShiftedFarRightNormalizedHankelMatrix w n =
      (2 * w / Real.log w) •
        (star (xiShiftedFarRightDilation w n) *
          xiShiftedMomentHankelMatrix (w ^ 2) n *
            xiShiftedFarRightDilation w n) := by
  have hw0 : w ≠ 0 := ne_of_gt (lt_trans zero_lt_one hw)
  have hlog : Real.log w ≠ 0 := ne_of_gt (Real.log_pos hw)
  ext i j
  simp only [xiShiftedFarRightNormalizedHankelMatrix,
    _root_.HTGeometry.momentHankelMatrix, xiShiftedFarRightNormalizedMoment,
    xiShiftedFarRightDilation, xiShiftedMomentHankelMatrix,
    finiteHankelMatrix, Matrix.smul_apply, smul_eq_mul]
  simp [Matrix.mul_apply, star, Matrix.conjTranspose, pow_add]
  field_simp [hlog, hw0]
  ring

/-- The mass-dilation matrix is invertible away from mass zero. -/
theorem xiShiftedFarRightDilation_isUnit {w : ℝ} (hw : w ≠ 0) (n : ℕ) :
    IsUnit (xiShiftedFarRightDilation w n) := by
  rw [xiShiftedFarRightDilation, Matrix.isUnit_diagonal, Pi.isUnit_iff]
  intro i
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ hw)

/-- **Fixed-block Xi positivity recession.** Every fixed shifted reciprocal Xi Hankel block is
strictly positive definite for all sufficiently large square-root masses. -/
theorem xiShiftedMomentHankelMatrix_squareParam_posDef_eventually (n : ℕ) :
    ∀ᶠ w : ℝ in atTop, (xiShiftedMomentHankelMatrix (w ^ 2) n).PosDef := by
  filter_upwards [xiShiftedFarRightNormalizedHankelMatrix_posDef_eventually n,
    eventually_gt_atTop (1 : ℝ)] with w hB hw
  let D := xiShiftedFarRightDilation w n
  let H := xiShiftedMomentHankelMatrix (w ^ 2) n
  let c : ℝ := 2 * w / Real.log w
  have hc : 0 < c := div_pos (mul_pos (by norm_num) (lt_trans zero_lt_one hw))
    (Real.log_pos hw)
  have hfactor : xiShiftedFarRightNormalizedHankelMatrix w n = c • (star D * H * D) := by
    exact xiShiftedFarRightNormalizedHankelMatrix_eq_congruence hw n
  rw [hfactor] at hB
  have hconjScaled := hB.smul (inv_pos.mpr hc)
  have hconj : (star D * H * D).PosDef := by
    simpa [smul_smul, inv_mul_cancel₀ hc.ne'] using hconjScaled
  exact (xiShiftedFarRightDilation_isUnit
    (ne_of_gt (lt_trans zero_lt_one hw)) n).posDef_star_left_conjugate_iff.mp hconj

/-- Every finite family of shifted-Xi Hankel blocks is eventually simultaneously positive
definite.  Equivalently, the least failing polynomial degree tends cofinally to infinity. -/
theorem xiShiftedMomentHankelMatrix_squareParam_posDef_eventually_forall_le (d : ℕ) :
    ∀ᶠ w : ℝ in atTop, ∀ k ≤ d,
      (xiShiftedMomentHankelMatrix (w ^ 2) (k + 1)).PosDef := by
  have hstep : ∀ k ∈ Finset.Iic d, ∀ᶠ w : ℝ in atTop,
      (xiShiftedMomentHankelMatrix (w ^ 2) (k + 1)).PosDef :=
    fun k _ => xiShiftedMomentHankelMatrix_squareParam_posDef_eventually (k + 1)
  filter_upwards [(eventually_all_finset (Finset.Iic d)).mpr hstep] with w hw
  intro k hk
  exact hw k (Finset.mem_Iic.mpr hk)

/-- Eventual strict positivity of every fixed shifted-Xi Hankel determinant. -/
theorem xiShiftedMomentHankelMatrix_squareParam_det_pos_eventually (n : ℕ) :
    ∀ᶠ w : ℝ in atTop, 0 < (xiShiftedMomentHankelMatrix (w ^ 2) n).det := by
  filter_upwards [xiShiftedMomentHankelMatrix_squareParam_posDef_eventually n] with w hw
  exact hw.det_pos

end

end RHTower
