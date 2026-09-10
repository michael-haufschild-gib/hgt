import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsSpikeRescaledSource
import GaloisForLFunctions.HTGeometry.MatrixRankSubadditive

/-! # Rank collapse and the rank-two rescaled positive survivor -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter

def egbFixedChargeAGibbsSpikeBoundaryHankel (d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => hausdorffMoment egbFixedChargeAGibbsSpikeBoundarySource ((i : ℕ) + (j : ℕ))

def egbFixedChargeAGibbsSpikeRescaledHankel (o d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => hausdorffMoment (egbFixedChargeAGibbsSpikeRescaledSource o) ((i : ℕ) + (j : ℕ))

/-- The limiting full-history matrix is the Gram matrix of one endpoint power column. -/
theorem egbFixedChargeAGibbsSpike_boundary_hankel_gram (d : ℕ) :
    egbFixedChargeAGibbsSpikeBoundaryHankel d =
      Matrix.vecMulVec (fun i : Fin d => (0 : ℝ) ^ (i : ℕ) / 2)
        (fun i : Fin d => (0 : ℝ) ^ (i : ℕ) / 2) := by
  ext i j
  change hausdorffMoment egbFixedChargeAGibbsSpikeBoundarySource ((i : ℕ) + (j : ℕ)) = _
  rw [egbFixedChargeAGibbsSpikeBoundarySource_moment, pow_add]
  change (0 : ℝ) ^ (i : ℕ) * (0 : ℝ) ^ (j : ℕ) / 4 =
    ((0 : ℝ) ^ (i : ℕ) / 2) * ((0 : ℝ) ^ (j : ℕ) / 2)
  ring

/-- Every nonempty boundary Hankel section has exactly rank one. -/
theorem egbFixedChargeAGibbsSpike_boundary_hankel_rank (d : ℕ) :
    (egbFixedChargeAGibbsSpikeBoundaryHankel (d + 1)).rank = 1 := by
  have hu : (egbFixedChargeAGibbsSpikeBoundaryHankel (d + 1)).rank ≤ 1 := by
    rw [egbFixedChargeAGibbsSpike_boundary_hankel_gram]
    exact Matrix.rank_vecMulVec_le _ _
  let e : Fin 1 → Fin (d + 1) := fun _ => 0
  let K := (egbFixedChargeAGibbsSpikeBoundaryHankel (d + 1)).submatrix e e
  have hd : K.det = (1 / 4 : ℝ) := by
    rw [Matrix.det_fin_one]
    change hausdorffMoment egbFixedChargeAGibbsSpikeBoundarySource (0 + 0) = _
    rw [egbFixedChargeAGibbsSpikeBoundarySource_moment]
    norm_num
  have hk : K.rank = 1 := by
    have hi := (Matrix.isUnit_iff_isUnit_det K).mpr
      (isUnit_iff_ne_zero.mpr (by rw [hd]; norm_num))
    simpa only [Fintype.card_fin] using Matrix.rank_of_isUnit K hi
  have hl := Matrix.rank_submatrix_le (egbFixedChargeAGibbsSpikeBoundaryHankel (d + 1)) e e
  change K.rank ≤ _ at hl
  rw [hk] at hl
  exact le_antisymm hu hl

/-- All entries of the actual full-history Hankel matrices converge together to the boundary source matrix. -/
theorem egbFixedChargeAGibbsSpike_full_hankel_tendsto_boundary (d : ℕ) :
    Tendsto (fun n : ℕ => egbFixedChargeAGibbsFullCollisionHankelMatrix n d 1
      (egbFixedChargeAGibbsSpikeEnergy n)) atTop (nhds (egbFixedChargeAGibbsSpikeBoundaryHankel d)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  change Tendsto (fun n : ℕ => egbFixedChargeAGibbsCollisionExcess n ((i : ℕ) + (j : ℕ)) 1
    (egbFixedChargeAGibbsSpikeEnergy n)) atTop
    (nhds (hausdorffMoment egbFixedChargeAGibbsSpikeBoundarySource ((i : ℕ) + (j : ℕ))))
  simpa only [egbFixedChargeAGibbsFullCollisionHausdorffSource_moment] using
    egbFixedChargeAGibbsSpike_source_moments_tendsto_boundary ((i : ℕ) + (j : ℕ))

/-- Every positive-time Hankel matrix converges to the zero matrix as dimension grows. -/
theorem egbFixedChargeAGibbsSpike_positive_hankel_tendsto_zero (o d : ℕ) :
    Tendsto (fun n : ℕ => egbFixedChargeAGibbsCollisionHankelMatrix n o d 1
      (egbFixedChargeAGibbsSpikeEnergy n)) atTop (nhds 0) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact egbFixedChargeAGibbsSpike_positive_collision_tendsto_zero ((i : ℕ) + (j : ℕ) + o)

/-- A closed family of rank-three full-history matrices converges to a rank-one matrix. -/
theorem egbFixedChargeAGibbsSpike_full_hankel_rank_collapse (k : ℕ) :
    (∀ n : ℕ, (egbFixedChargeAGibbsFullCollisionHankelMatrix n (k + 3) 1
      (egbFixedChargeAGibbsSpikeEnergy n)).rank = 3) ∧
    Tendsto (fun n : ℕ => egbFixedChargeAGibbsFullCollisionHankelMatrix n (k + 3) 1
      (egbFixedChargeAGibbsSpikeEnergy n)) atTop (nhds (egbFixedChargeAGibbsSpikeBoundaryHankel (k + 3))) ∧
    (egbFixedChargeAGibbsSpikeBoundaryHankel (k + 3)).rank = 1 := by
  exact ⟨fun n => (egbFixedChargeAGibbsSpike_hankel_rank_drop n 0 k).1,
    egbFixedChargeAGibbsSpike_full_hankel_tendsto_boundary (k + 3),
    egbFixedChargeAGibbsSpike_boundary_hankel_rank (k + 2)⟩

/-- A closed family of rank-two positive-time matrices converges to rank zero. -/
theorem egbFixedChargeAGibbsSpike_positive_hankel_rank_collapse (o k : ℕ) :
    (∀ n : ℕ, (egbFixedChargeAGibbsCollisionHankelMatrix n o (k + 3) 1
      (egbFixedChargeAGibbsSpikeEnergy n)).rank = 2) ∧
    Tendsto (fun n : ℕ => egbFixedChargeAGibbsCollisionHankelMatrix n o (k + 3) 1
      (egbFixedChargeAGibbsSpikeEnergy n)) atTop (nhds 0) ∧
    (0 : Matrix (Fin (k + 3)) (Fin (k + 3)) ℝ).rank = 0 := by
  exact ⟨fun n => (egbFixedChargeAGibbsSpike_hankel_rank_drop n o k).2,
    egbFixedChargeAGibbsSpike_positive_hankel_tendsto_zero o (k + 3), Matrix.rank_zero⟩

/-- Rescaling recovers the exact Hankel matrix of the positive surviving measure. -/
theorem egbFixedChargeAGibbsSpike_rescaled_hankel_eq (n o d : ℕ) :
    (2 : ℝ) ^ (n + 3) • egbFixedChargeAGibbsCollisionHankelMatrix n o d 1
      (egbFixedChargeAGibbsSpikeEnergy n) = egbFixedChargeAGibbsSpikeRescaledHankel o d := by
  ext i j
  exact (egbFixedChargeAGibbsSpike_rescaled_source_moment n o ((i : ℕ) + (j : ℕ))).symm

/-- The measure recovered by rescaling retains the entire rank-two geometry. -/
theorem egbFixedChargeAGibbsSpike_rescaled_hankel_rank (o k : ℕ) :
    (egbFixedChargeAGibbsSpikeRescaledHankel o (k + 3)).rank = 2 := by
  rw [← egbFixedChargeAGibbsSpike_rescaled_hankel_eq 0 o (k + 3),
    rank_smul_eq (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))]
  exact (egbFixedChargeAGibbsSpike_hankel_rank_drop 0 o k).2

end
end GaloisForLFunctions.HTGeometry
