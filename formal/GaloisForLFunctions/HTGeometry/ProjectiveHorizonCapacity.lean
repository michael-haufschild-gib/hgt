import GaloisForLFunctions.HTGeometry.ProjectiveHorizonPageTransition
import GaloisForLFunctions.HTGeometry.JacobianAlgebraicIndependence
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Higher-rank projective horizon capacity

This module assembles the longitudinal weighted-Pascal block and all transverse unweighted-Pascal
blocks into the full projective-chart linearization minor.  It proves the exact determinant and
the dimension-extensive Page balance in every projective dimension.
-/

open Matrix
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- The chart-linearization block in one projective channel: channel zero is longitudinal and all
remaining channels are transverse. -/
def projectiveCapacityChannelBlock (n r d : ℕ) (c : Fin d) :
    Matrix (Fin r) (Fin r) ℤ :=
  if (c : ℕ) = 0 then projectiveLongitudinalLinearizationMinor n r
  else shiftedPascalMatrix n r

/-- The complete block-diagonal projective-chart linearization minor. -/
def projectiveCapacityLinearizationMinor (n r d : ℕ) :
    Matrix (Fin r × Fin d) (Fin r × Fin d) ℤ :=
  Matrix.blockDiagonal (projectiveCapacityChannelBlock n r d)

/-- The complete `d`-channel minor has the same nontrivial determinant as its unique longitudinal
block; every transverse Pascal block is unimodular. -/
theorem projectiveCapacityLinearizationMinor_det {n r d : ℕ} (hd : 0 < d) :
    (projectiveCapacityLinearizationMinor n r d).det =
      (-1 : ℤ) ^ r * 2 ^ (r * n) := by
  classical
  rw [projectiveCapacityLinearizationMinor, Matrix.det_blockDiagonal]
  simp only [projectiveCapacityChannelBlock]
  let c0 : Fin d := ⟨0, hd⟩
  rw [← Finset.mul_prod_erase Finset.univ
    (fun c : Fin d => (if (c : ℕ) = 0 then
      projectiveLongitudinalLinearizationMinor n r else shiftedPascalMatrix n r).det)
    (Finset.mem_univ c0)]
  rw [show (if (c0 : ℕ) = 0 then
      projectiveLongitudinalLinearizationMinor n r else shiftedPascalMatrix n r).det =
      (-1 : ℤ) ^ r * 2 ^ (r * n) by
    simp [c0, projectiveLongitudinalLinearizationMinor_det]]
  suffices (∏ c ∈ Finset.univ.erase c0,
      (if (c : ℕ) = 0 then projectiveLongitudinalLinearizationMinor n r
        else shiftedPascalMatrix n r).det) = 1 by simp [this]
  apply Finset.prod_eq_one
  intro c hc
  have hcne : c ≠ c0 := Finset.ne_of_mem_erase hc
  have hcval : (c : ℕ) ≠ 0 := by
    intro hz
    apply hcne
    apply Fin.ext
    simpa [c0] using hz
  simp [hcval, shiftedPascalMatrix_det]

/-- The full projective capacity minor is nonsingular in every positive projective dimension. -/
theorem projectiveCapacityLinearizationMinor_det_ne_zero {n r d : ℕ} (hd : 0 < d) :
    (projectiveCapacityLinearizationMinor n r d).det ≠ 0 := by
  rw [projectiveCapacityLinearizationMinor_det hd]
  exact mul_ne_zero (pow_ne_zero r (by norm_num)) (pow_ne_zero (r * n) (by norm_num))

/-- Ambient coefficient count for a `d`-channel jet through resolution `N`. -/
def projectiveFiniteJetAmbientCount (d N : ℕ) : ℕ :=
  d * finiteJetAmbientCount N

/-- Displayed coefficient count for one depth packet in `d` channels. -/
def projectiveFiniteHorizonObservableCount (d N m : ℕ) : ℕ :=
  d * finiteHorizonObservableCount N m

/-- Observation rank in `d` independent projective channels. -/
def projectiveFiniteHorizonObservationRank (d m n N : ℕ) : ℕ :=
  d * finiteHorizonObservationRank m n N

/-- Hidden-source dimension in `d` independent projective channels. -/
def projectiveFiniteHorizonHiddenCount (d m n N : ℕ) : ℕ :=
  d * finiteHorizonHiddenCount m n N

/-- Compatibility-relation dimension in `d` independent projective channels. -/
def projectiveFiniteHorizonRelationCount (d m n N : ℕ) : ℕ :=
  d * finiteHorizonRelationCount m n N

/-- Exact higher-rank observation capacity: projective dimension multiplies the scalar rank but
does not move the Page resolution. -/
theorem projectiveFiniteHorizonObservationRank_eq_min {d m n N : ℕ}
    (hm : m ≤ N + 1) (hn : n ≤ N + 1) :
    projectiveFiniteHorizonObservationRank d m n N =
      d * min (finiteJetAmbientCount N)
        (finiteHorizonObservableCount N m + finiteHorizonObservableCount N n) := by
  rw [projectiveFiniteHorizonObservationRank, finiteHorizonObservationRank_eq_min hm hn]

/-- Exact higher-rank hidden dimension. -/
theorem projectiveFiniteJetAmbientCount_sub_observationRank_eq_hidden {d m n N : ℕ}
    (hm : m ≤ N + 1) (hn : n ≤ N + 1) :
    projectiveFiniteJetAmbientCount d N -
        projectiveFiniteHorizonObservationRank d m n N =
      projectiveFiniteHorizonHiddenCount d m n N := by
  simp only [projectiveFiniteJetAmbientCount, projectiveFiniteHorizonObservationRank,
    projectiveFiniteHorizonHiddenCount]
  rw [← Nat.mul_sub_left_distrib,
    finiteJetAmbientCount_sub_observationRank_eq_hidden hm hn]

/-- Exact higher-rank relation dimension. -/
theorem projectiveFiniteHorizonObservableCount_sub_rank_eq_relations {d m n N : ℕ}
    (hm : m ≤ N + 1) (hn : n ≤ N + 1) :
    projectiveFiniteHorizonObservableCount d N m +
          projectiveFiniteHorizonObservableCount d N n -
        projectiveFiniteHorizonObservationRank d m n N =
      projectiveFiniteHorizonRelationCount d m n N := by
  simp only [projectiveFiniteHorizonObservableCount,
    projectiveFiniteHorizonObservationRank, projectiveFiniteHorizonRelationCount]
  rw [← Nat.mul_add, ← Nat.mul_sub_left_distrib,
    finiteHorizonObservableCount_sub_rank_eq_relations hm hn]

/-- The higher-rank Page balance. -/
theorem projectiveFiniteHorizon_page_balance {d m n N : ℕ}
    (hm : m ≤ N + 1) (hn : n ≤ N + 1) :
    projectiveFiniteHorizonObservableCount d N m +
        projectiveFiniteHorizonObservableCount d N n +
        projectiveFiniteHorizonHiddenCount d m n N =
      projectiveFiniteJetAmbientCount d N +
        projectiveFiniteHorizonRelationCount d m n N := by
  simp only [projectiveFiniteHorizonObservableCount,
    projectiveFiniteHorizonHiddenCount, projectiveFiniteJetAmbientCount,
    projectiveFiniteHorizonRelationCount]
  rw [← Nat.mul_add, ← Nat.mul_add, ← Nat.mul_add,
    finiteHorizon_page_balance hm hn]

/-- Both higher-rank defects vanish at the same scalar Page resolution. -/
theorem projectiveFiniteHorizon_at_page (d m n : ℕ) (h : 0 < m + n) :
    projectiveFiniteHorizonHiddenCount d m n (m + n - 1) = 0 ∧
      projectiveFiniteHorizonRelationCount d m n (m + n - 1) = 0 := by
  constructor
  · simp [projectiveFiniteHorizonHiddenCount, finiteHorizonHiddenCount_at_page]
  · simp [projectiveFiniteHorizonRelationCount,
      finiteHorizonRelationCount_at_page m n h]

end GaloisForLFunctions.HTGeometry

