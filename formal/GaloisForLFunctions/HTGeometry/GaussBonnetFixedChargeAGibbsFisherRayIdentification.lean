import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFisherPositiveCone
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsTunableFisherHistory

/-! # Complete two-observation classification for arbitrary Gibbs energies -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The first two Fisher observations of every Gibbs state are exactly the two successive positive-cone shapes. -/
theorem egbFixedChargeAGibbsCollisionFisherValue_pair_shape (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeAGibbsCollisionFisherValue n m β E,
      egbFixedChargeAGibbsCollisionFisherValue n (m + 1) β E) =
      (egbFixedChargeAGibbsCollisionFisherShape
        (egbFixedChargeAGibbsCollisionSlowSourceMass n m β E)
        (egbFixedChargeAGibbsCollisionFastSourceMass n m β E),
      egbFixedChargeAGibbsCollisionFisherShape
        ((4 / 9 : ℝ) * (egbFixedChargeAGibbsCollisionSlowSourceMass n m β E : ℝ))
        ((1 / 36 : ℝ) * (egbFixedChargeAGibbsCollisionFastSourceMass n m β E : ℝ))) := by
  rw [egbFixedChargeAGibbsCollisionFisherValue_two_mass,
    egbFixedChargeAGibbsCollisionFisherValue_two_mass,
    egbFixedChargeAGibbsCollisionSlowSourceMass_offset,
    egbFixedChargeAGibbsCollisionFastSourceMass_offset]
  simp only [pow_one]

/-- Across arbitrary Gibbs states, grids, temperatures, and offsets, two readings classify mixed source rays exactly and collect all pure sources into the zero stratum. -/
theorem egbFixedChargeAGibbsCollisionFisherValue_pair_eq_iff (n m p o : ℕ) (β γ : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (F : Fin (2 ^ (p + 3)) → ℝ) :
    let x : ℝ := egbFixedChargeAGibbsCollisionSlowSourceMass n m β E
    let y : ℝ := egbFixedChargeAGibbsCollisionFastSourceMass n m β E
    let u : ℝ := egbFixedChargeAGibbsCollisionSlowSourceMass p o γ F
    let v : ℝ := egbFixedChargeAGibbsCollisionFastSourceMass p o γ F
    (egbFixedChargeAGibbsCollisionFisherValue n m β E,
      egbFixedChargeAGibbsCollisionFisherValue n (m + 1) β E) =
        (egbFixedChargeAGibbsCollisionFisherValue p o γ F,
          egbFixedChargeAGibbsCollisionFisherValue p (o + 1) γ F) ↔
      (x * y = 0 ∧ u * v = 0) ∨ (x * y ≠ 0 ∧ u * v ≠ 0 ∧ x * v = y * u) := by
  dsimp only
  rw [egbFixedChargeAGibbsCollisionFisherValue_pair_shape,
    egbFixedChargeAGibbsCollisionFisherValue_pair_shape]
  rw [Prod.mk.injEq]
  exact egbFixedChargeAGibbsCollisionFisherShape_nonnegative_pair_fibers
      (egbFixedChargeAGibbsCollisionSlowSourceMass n m β E)
      (egbFixedChargeAGibbsCollisionFastSourceMass n m β E)
      (egbFixedChargeAGibbsCollisionSlowSourceMass p o γ F)
      (egbFixedChargeAGibbsCollisionFastSourceMass p o γ F)

end
end GaloisForLFunctions.HTGeometry
