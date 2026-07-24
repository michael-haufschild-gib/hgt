import GaloisForLFunctions.RHTower.HermiteSecularQuasiFreePhaseFusionUniversalityLaw
import GaloisForLFunctions.RHTower.GaussianMetricHermiteStableRankFractureUniversalityLaw

/-!
# Hermite secular contrast activates the stable Gaussian rank phase

The same constrained-prolate occupations govern the unique limiting secular root, exact
next-rank quasi-free increments, and the canonical Gaussian/Hermite rank fracture.  This file
joins those terminal descriptions and exposes strict activation of the next rank.
-/

open Filter

namespace RHTower

noncomputable section

/-- The complete secular-root, quasi-free increment, and stable-rank activation package. -/
def HermiteSecularContrastStableRankActivationCertificate
    (k : ℕ) (t : ℝ) : Prop :=
  let E := hermiteContrastSecularEnergyCoordinate k
  let Q := constrainedProlateHermiteWeightSum (k + 1)
  let d : ℝ := 4 * (k + 1)
  E ∈ Set.Ioo (0 : ℝ) 1 ∧
    (∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 →
      (ladderLimitSecular (constrainedProlateHermiteWeightSum k)
        (constrainedProlateHermiteWeight (k + 1)) x = 0 ↔ x = E)) ∧
    (∀ (A : ℕ → ℝ), (∀ j, 0 < A j) →
      Tendsto (fun lam : ℝ =>
          (ladderTwoModeRoot A (k + 1) lam / ladderTwoModeRoot A k lam) / lam ^ 8)
        atTop (nhds
          ((hermiteContrastSecularEnergyCoordinate (k + 1) / E) *
            (A (k + 2) / A (k + 1))))) ∧
    constrainedProlateHermiteQuasiFreeMean (k + 2) -
        constrainedProlateHermiteQuasiFreeMean (k + 1) = Q * (1 - E) * d ∧
    constrainedProlateHermiteQuasiFreeVariance (k + 2) -
        constrainedProlateHermiteQuasiFreeVariance (k + 1) =
      Q * (1 - E) * (1 - Q * (1 - E)) * d ^ 2 ∧
    constrainedProlateHermiteQuasiFreeFanoMargin (k + 2) -
        constrainedProlateHermiteQuasiFreeFanoMargin (k + 1) =
      Q * (1 - E) * (d - (1 - Q * (1 - E)) * d ^ 2) ∧
    0 < constrainedProlateHermiteQuasiFreeMean (k + 2) -
        constrainedProlateHermiteQuasiFreeMean (k + 1) ∧
    0 < constrainedProlateHermiteQuasiFreeVariance (k + 2) -
        constrainedProlateHermiteQuasiFreeVariance (k + 1) ∧
    HermiteEvenGaussianSlaterPluckerStrictPhase (k + 2) t

/-- **Hermite secular-contrast stable-rank activation.**  Every secular contrast coordinate
strictly activates the next-rank mean and variance and places the enlarged Hermite block in the
complete stable strict phase at every nonnegative Gaussian scale. -/
theorem hermiteSecularContrast_stableRankActivationUniversality
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    HermiteSecularContrastStableRankActivationCertificate k t := by
  dsimp only [HermiteSecularContrastStableRankActivationCertificate]
  have hfusion :=
    hermiteContrastSecularEnergy_quasiFreePhaseFusionUniversality k
  dsimp only at hfusion
  rcases hfusion with ⟨hE, hroot, hratio, hmean, hvariance, hfano⟩
  have hweight :
      0 < constrainedProlateHermiteWeight (k + 1) :=
    constrainedProlateHermiteWeight_pos (k + 1)
  have hweightLt :
      constrainedProlateHermiteWeight (k + 1) < 1 :=
    constrainedProlateHermiteWeight_lt_one_of_pos (Nat.succ_pos k)
  have hdegree : 0 < (4 : ℝ) * ((k + 1 : ℕ) : ℝ) := by
    positivity
  have hmeanPos :
      0 < constrainedProlateHermiteQuasiFreeMean (k + 2) -
        constrainedProlateHermiteQuasiFreeMean (k + 1) := by
    rw [show k + 2 = (k + 1) + 1 by omega,
      constrainedProlateHermiteQuasiFreeMean_succ_sub]
    exact mul_pos hweight hdegree
  have hvariancePos :
      0 < constrainedProlateHermiteQuasiFreeVariance (k + 2) -
        constrainedProlateHermiteQuasiFreeVariance (k + 1) := by
    rw [show k + 2 = (k + 1) + 1 by omega,
      constrainedProlateHermiteQuasiFreeVariance_succ_sub]
    exact mul_pos (mul_pos hweight (sub_pos.mpr hweightLt)) (sq_pos_of_pos hdegree)
  have hstrict :
      HermiteEvenGaussianSlaterPluckerStrictPhase (k + 2) t :=
    (gaussianMetricHermiteStableRankFractureUniversality.2.1
      (k + 2) t ht).2 (by omega)
  exact ⟨hE, hroot, hratio, hmean, hvariance, hfano,
    hmeanPos, hvariancePos, hstrict⟩

end

end RHTower
