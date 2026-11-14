import GaloisForLFunctions.HTGeometry.Probability.BlockSphereBetaLaw
import GaloisForLFunctions.HTGeometry.ThetaPrimeBetaGammaRecovery

/-!
# Spherical realization of theta–prime history

Split Euclidean nine-space into orthogonal blocks of dimensions three and six. The squared
radius of the first block on the unit eight-sphere has law `Beta(3/2,3)`. Its moments are the
prime-history tails and the normalized theta Mellin-six holonomies. Power weighting realizes
the history's survival conditioning geometrically; the mean complementary radius is its hazard.
-/

open MeasureTheory ProbabilityTheory

noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Squared three-dimensional projection of a uniform vector on the unit eight-sphere. -/
def thetaPrimeSphereLaw : Measure ℝ :=
  blockCoordinateLaw (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 6))

/-- The spherical projection realizes the theta–prime beta distribution. -/
theorem thetaPrimeSphereLaw_eq_beta : thetaPrimeSphereLaw = betaMeasure (3 / 2) 3 := by
  unfold thetaPrimeSphereLaw
  convert blockCoordinateLaw_eq_beta
    (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 6)) using 1 <;> norm_num

/-- Prime-history tails are actual spherical projection moments. -/
theorem integral_thetaPrimeSphereLaw_pow (k : ℕ) :
    (∫ u : ℝ, u ^ k ∂thetaPrimeSphereLaw) = PrimeHodgeHistory.m k := by
  rw [thetaPrimeSphereLaw_eq_beta, integral_pow_betaMeasure_threeHalves_three]

/-- The block Mellin moment is the rational history tail. -/
theorem thetaPrimeSphereMellin_eq (k : ℕ) :
    blockSphereMellin (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 6)) k =
      105 / ((2 * (k : ℝ) + 3) * (2 * k + 5) * (2 * k + 7)) := by
  rw [← integral_blockCoordinateLaw_pow]
  simpa [thetaPrimeSphereLaw, PrimeHodgeHistory.m] using integral_thetaPrimeSphereLaw_pow k

/-- Theta Mellin-six holonomy is a moment of the three-block projection on `S⁸`. -/
theorem thetaCuspMellinSixHolonomy_eq_sphereMoment (k : ℕ) :
    _root_.RHTower.thetaCuspMellinSixHolonomy k =
      ((∫ u : ℝ, u ^ k ∂thetaPrimeSphereLaw : ℝ) : ℂ) := by
  rw [_root_.RHTower.thetaCuspMellinSixHolonomy_eq_primeHodgeHistory_m,
    integral_thetaPrimeSphereLaw_pow]

/-- Power conditioning of the spherical block agrees with survival conditioning. -/
theorem thetaPrimeSphereTilt_eq_beta (k : ℕ) :
    blockCoordinateTilt (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 6)) k =
      betaMeasure ((k : ℝ) + 3 / 2) 3 := by
  have h := blockCoordinateTilt_eq_beta
    (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 6)) k
  norm_num at h
  simpa only [add_comm (3 / 2 : ℝ) (k : ℝ)] using h

/-- The prime-history exit hazard is the complementary squared block radius after conditioning. -/
theorem exitHazard_eq_sphereTransverseMean (k : ℕ) :
    PrimeHodgeHistory.exitHazard k =
      ∫ u : ℝ, 1 - u
        ∂blockCoordinateTilt (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 6)) k := by
  rw [thetaPrimeSphereTilt_eq_beta, exitHazard_eq_tiltMean]

end GaloisForLFunctions.HTGeometry
