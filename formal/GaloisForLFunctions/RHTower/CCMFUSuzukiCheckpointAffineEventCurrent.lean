import GaloisForLFunctions.RHTower.CCMFUSuzukiCheckpointAffineReduction

/-!
# Discrete event laws for the CCM-FU Suzuki affine current
-/

noncomputable section

namespace RHTower

open Set
open GaloisForLFunctions.RHTower

/-- Signed slope of the floor-selected affine source on event cell `N`. -/
def suzukiCheckpointAffineSlope (N : ℕ) : ℝ :=
  suzukiCheckpointReservoirDeriv (Real.log (N : ℝ)) - suzukiCheckpointMass N

/-- Positive curvature packet accumulated across the entire `N`th event cell. -/
def suzukiCheckpointEventCurvatureJump (N : ℕ) : ℝ :=
  suzukiCheckpointBregman (Real.log ((N + 1 : ℕ) : ℝ)) (Real.log (N : ℝ))

/-- Cumulative Mangoldt slope changes by exactly the newly exposed integer weight. -/
theorem suzukiCheckpointMass_succ {N : ℕ} (hN : 2 ≤ N) :
    suzukiCheckpointMass (N + 1) =
      suzukiCheckpointMass N + screwPrimeWeight (N + 1) := by
  unfold suzukiCheckpointMass
  rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ N + 1)]

/-- Exact prime--archimedean slope update. This is the signed local datum left after bounded
within-cell curvature is removed. -/
theorem suzukiCheckpointAffineSlope_succ_sub
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiCheckpointAffineSlope (N + 1) - suzukiCheckpointAffineSlope N =
      (suzukiCheckpointReservoirDeriv (Real.log ((N + 1 : ℕ) : ℝ)) -
        suzukiCheckpointReservoirDeriv (Real.log (N : ℝ))) -
      screwPrimeWeight (N + 1) := by
  rw [suzukiCheckpointAffineSlope, suzukiCheckpointAffineSlope,
    suzukiCheckpointMass_succ hN]
  ring

/-- Full-cell curvature packet is positive and at most one. -/
theorem suzukiCheckpointEventCurvatureJump_mem_unitInterval
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiCheckpointEventCurvatureJump N ∈ Set.Icc 0 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNp1pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hNle : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ N
  have hlog : Real.log (N : ℝ) ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
    (Real.log_le_log_iff hNpos hNp1pos).mpr hNle
  unfold suzukiCheckpointEventCurvatureJump
  exact suzukiCheckpointBregman_mem_unitInterval hN
    (show Real.log ((N + 1 : ℕ) : ℝ) ∈ suzukiCheckpointCell N from ⟨hlog, le_rfl⟩)
    (show Real.log (N : ℝ) ∈ suzukiCheckpointCell N from ⟨le_rfl, hlog⟩)

/-- Exact endpoint dynamics of the reduced source: signed affine slope transport plus one positive
unit-bounded curvature packet. -/
theorem suzukiCheckpoint_endpoint_recurrence_affineSlope_curvature
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiPsi (Real.log ((N + 1 : ℕ) : ℝ)) =
      suzukiPsi (Real.log (N : ℝ)) +
        suzukiCheckpointAffineSlope N *
          (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)) +
        suzukiCheckpointEventCurvatureJump N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNp1pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hNle : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ N
  have hlog : Real.log (N : ℝ) ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
    (Real.log_le_log_iff hNpos hNp1pos).mpr hNle
  have hsplit := suzukiPsi_eq_checkpointAffineJet_add_bregman hN
    (show Real.log ((N + 1 : ℕ) : ℝ) ∈ suzukiCheckpointCell N from ⟨hlog, le_rfl⟩)
    (show Real.log (N : ℝ) ∈ suzukiCheckpointCell N from ⟨le_rfl, hlog⟩)
  simpa [suzukiCheckpointAffineSlope, suzukiCheckpointEventCurvatureJump] using hsplit

/-- The reduced affine current has an upward event reset exactly equal to the discarded curvature
packet: its right value is the true source endpoint, while the preceding affine cell undershoots by
the positive unit-bounded jump. -/
theorem suzukiPsi_sub_leftAffineJet_terminal_eq_curvatureJump
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiPsi (Real.log ((N + 1 : ℕ) : ℝ)) -
        suzukiCheckpointLeftAffineJet N (Real.log ((N + 1 : ℕ) : ℝ)) =
      suzukiCheckpointEventCurvatureJump N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNp1pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hNle : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ N
  have hlog : Real.log (N : ℝ) ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
    (Real.log_le_log_iff hNpos hNp1pos).mpr hNle
  have hsplit := suzukiPsi_eq_leftAffineJet_add_unitBregman hN
    (show Real.log ((N + 1 : ℕ) : ℝ) ∈ suzukiCheckpointCell N from ⟨hlog, le_rfl⟩)
  unfold suzukiCheckpointEventCurvatureJump
  linarith [hsplit.1]

end RHTower
