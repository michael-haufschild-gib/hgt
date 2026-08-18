import GaloisForLFunctions.RHTower.SourceHorizontalSecondCartierOrbitCoercivity
import GaloisForLFunctions.HTGeometry.PureSingularCarrierTrichotomy

open Complex Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry

attribute [local instance]
  GaloisForLFunctions.HTGeometry.instMeasurableSpaceCircle_galoisForLFunctions

namespace RHTower

noncomputable section

theorem circleMeasureMomentZ_bilateralModerate
    (mu : Measure Circle) [IsFiniteMeasure mu] :
    bilateralModerate (circleMeasureMomentZ mu) := by
  refine ⟨mu.real Set.univ, 0, fun e => ?_⟩
  simp only [pow_zero, mul_one]
  unfold circleMeasureMomentZ
  calc
    ‖∫ z : Circle, (z : ℂ) ^ (-e) ∂mu‖ ≤
        1 * mu.real Set.univ :=
      norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall fun z => by simp [norm_zpow])
    _ = mu.real Set.univ := one_mul _

def SourceHorizontalActualXiEndpointCompactCircleRepresentation
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ)
    (p : Nat.Primes) : Prop :=
  ∃ mu : Measure Circle, IsFiniteMeasure mu ∧
    ∀ e : ℤ,
      circleMeasureMomentZ mu e =
        (sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N p
          sourceHorizontalBilateralSecondJetGhost) e

theorem not_sourceHorizontalActualXiEndpointCompactCircleRepresentation
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0)
    (N : ℕ) (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N)
    (p : Nat.Primes) :
    ¬ SourceHorizontalActualXiEndpointCompactCircleRepresentation x u q r N p := by
  rintro ⟨mu, hmu, heq⟩
  letI : IsFiniteMeasure mu := hmu
  apply not_bilateralModerate_sourceHorizontalActualXiEndpointSecondJetHardyDescent_ghost
    q hkappa hr N hjet p
  have hfun : circleMeasureMomentZ mu =
      sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N p
        sourceHorizontalBilateralSecondJetGhost := funext heq
  rw [← hfun]
  exact circleMeasureMomentZ_bilateralModerate mu

end

end RHTower
