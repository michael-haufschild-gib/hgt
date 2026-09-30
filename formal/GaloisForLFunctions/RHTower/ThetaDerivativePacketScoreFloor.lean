import GaloisForLFunctions.RHTower.PrimeArchThetaFullScoreSlack
import GaloisForLFunctions.RHTower.ThetaDerivativePacketScoreTail
import GaloisForLFunctions.RHTower.ThetaScoreFloorCompactTailStability
import GaloisForLFunctions.RHTower.ThetaDerivativePacketSpectralBoundary
/-!
# Complete score-floor compatibility of actual theta derivative packets

Strict actual source slack and the eventual positive packet score combine with
compact/tail stability. The resulting parameters also retain every property of
the existing dark-divisor packet, including literal low moments and off-axis zeros.
-/

open Filter Topology MeasureTheory
namespace RHTower
noncomputable section

/-- All sufficiently small nonnegative packets strictly retain the complete fixed score floor. -/
theorem exists_thetaDerivativePacket_score_gt_firstAtomSquare (m : ℕ) (hm : 0 < m) :
    ∃ ε > 0, ∀ t : ℝ, 0 ≤ t → t < ε → ∀ x : ℝ, 0 ≤ x →
      Real.pi * thetaCuspBornWittenAmplitude 1 x ^ 2 * (x - 1) ^ 2 <
        thetaScoreFloorOperator (thetaDerivativePacket m t) x := by
  let H : ℝ → ℝ := fun x =>
    (1 - 303 * x ^ 2) * iteratedDeriv (4 * m) thetaCuspFullSource x -
      16 * x * iteratedDeriv (4 * m + 1) thetaCuspFullSource x
  have htail : ∀ᶠ x in atTop, 0 ≤ H x :=
    (eventually_thetaDerivativePacketScorePerturbation_pos m hm).mono fun _ hx => hx.le
  obtain ⟨ε, hε, hglobal⟩ := thetaScoreFloor_compactTail_stable
    continuous_thetaCuspFullScoreSlack (continuous_thetaDerivativePacketScorePerturbation m)
    (fun x hx => thetaCuspFullScoreSlack_pos hx) htail
  refine ⟨ε, hε, fun t ht htε x hx => ?_⟩
  have h := hglobal t ht htε x hx
  have hk : Differentiable ℝ thetaCuspFullSource :=
    contDiff_thetaCuspFullSource.differentiable (by simp)
  have hh : Differentiable ℝ (iteratedDeriv (4*m) thetaCuspFullSource) :=
    (contDiff_iteratedDeriv_thetaCuspFullSource (4*m)).differentiable (by simp)
  have hlin : thetaScoreFloorOperator (thetaDerivativePacket m t) x =
      thetaScoreFloorOperator thetaCuspFullSource x +
        t * thetaScoreFloorOperator (iteratedDeriv (4*m) thetaCuspFullSource) x :=
    thetaScoreFloorOperator_add_const_mul hk hh t x
  have hd := (hasDerivAt_iteratedDeriv_thetaCuspFullSource (4*m) x).deriv
  dsimp only [thetaCuspFullScoreSlack, H] at h
  rw [hlin]
  simp only [thetaScoreFloorOperator, hd]
  linarith

/-- The complete score floor survives at the same parameters as the literal dark-divisor packet. -/
theorem thetaDerivativePacket_dark_divisor_with_score_floor (m : ℕ) (hm : 0 < m) :
    ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
      (∀ x : ℝ, 0 ≤ x →
        Real.pi * thetaCuspBornWittenAmplitude 1 x ^ 2 * (x - 1) ^ 2 <
          thetaScoreFloorOperator (thetaDerivativePacket m t) x) ∧
      (∀ x, 0 < thetaDerivativePacket m t x) ∧
      (∀ x, thetaDerivativePacket m t (-x) = thetaDerivativePacket m t x) ∧
      (∃ δ > 0, ∀ x, iteratedDeriv 2 (fun y => Real.log (thetaDerivativePacket m t y)) x ≤ -δ) ∧
      (∀ c : ℝ, Integrable (fun x => Real.exp (c * |x|) * |thetaDerivativePacket m t x|)) ∧
      (∀ j < 4 * m, ∫ x : ℝ, x ^ j * thetaDerivativePacket m t x =
        ∫ x : ℝ, x ^ j * thetaCuspFullSource x) ∧
      (∀ z : ℂ, sourceTransform (thetaDerivativePacketC m t) z = XiC z * (1 + t * z ^ (4 * m))) ∧
      (∀ x : ℝ, analyticOrderAt (sourceTransform (thetaDerivativePacketC m t)) (x : ℂ) =
        analyticOrderAt XiC x) ∧
      (∀ j < 4 * m, sourceTransform (thetaDerivativePacketC m t) (thetaPacketRoot m t j) = 0 ∧
        analyticOrderAt (sourceTransform (thetaDerivativePacketC m t)) (thetaPacketRoot m t j) =
          analyticOrderAt XiC (thetaPacketRoot m t j) + 1 ∧
        (thetaPacketRoot m t j).re ≠ 0 ∧ (thetaPacketRoot m t j).im ≠ 0) := by
  obtain ⟨δ, hδ, hpacket⟩ := thetaDerivativePacket_dark_divisor m hm
  obtain ⟨ε, hε, hfloor⟩ := exists_thetaDerivativePacket_score_gt_firstAtomSquare m hm
  refine ⟨min δ ε, lt_min hδ hε, fun t ht htmin => ?_⟩
  exact ⟨hfloor t ht.le (htmin.trans_le (min_le_right _ _)),
    hpacket t ht (htmin.trans_le (min_le_left _ _))⟩

end
end RHTower
