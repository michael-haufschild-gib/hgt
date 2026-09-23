import GaloisForLFunctions.HTGeometry.ConstitutiveThetaHasseKMSExecutionBalance

/-!
# Supercritical sharpness mechanisms in the Hasse/KMS packet

The Hasse/KMS layer masses give an exact geometric realization of repeated-touch retention and
sprinkling.  Half recovery retains one half per layer; quarter recovery is its exponentially tilted
law, and its tail is the square of the half-recovery tail.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- After `t` extra depths, the half-recovery Hasse/KMS layer retains exactly `(1/2)^t` mass. -/
theorem geometricLayerMass_half_add (n t : ℕ) :
    geometricLayerMass (1 / 2 : ℝ) (n + t) =
      (1 / 2 : ℝ) ^ t * geometricLayerMass (1 / 2 : ℝ) n := by
  simp only [geometricLayerMass, pow_add]
  ring

/-- Total half-recovery mass remaining from depth `N` onward is exactly `(1/2)^N`. -/
theorem tsum_geometricLayerMass_half_shift (N : ℕ) :
    ∑' k : ℕ, geometricLayerMass (1 / 2 : ℝ) (N + k) = (1 / 2 : ℝ) ^ N := by
  have hfun :
      (fun k : ℕ ↦ geometricLayerMass (1 / 2 : ℝ) (N + k)) =
        fun k : ℕ ↦ (1 / 2 : ℝ) ^ N * geometricLayerMass (1 / 2 : ℝ) k := by
    funext k
    simp only [geometricLayerMass, pow_add]
    ring
  rw [hfun, tsum_mul_left, tsum_geometricLayerMass_eq_one (by norm_num) (by norm_num), mul_one]

/-- Quarter recovery is the half-recovery packet tilted by one further half-factor per depth. -/
theorem geometricLayerMass_quarter_eq_sprinkled_half (n : ℕ) :
    geometricLayerMass (1 / 4 : ℝ) n =
      (3 / 2 : ℝ) * (1 / 2 : ℝ) ^ n * geometricLayerMass (1 / 2 : ℝ) n := by
  simp only [geometricLayerMass]
  rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) * (1 / 2 : ℝ) by norm_num, mul_pow]
  ring

/-- Quarter-recovery tail is exactly the square of the half-recovery tail at every depth. -/
theorem tsum_geometricLayerMass_quarter_shift_eq_sq_half_shift (N : ℕ) :
    (∑' k : ℕ, geometricLayerMass (1 / 4 : ℝ) (N + k)) =
      (∑' k : ℕ, geometricLayerMass (1 / 2 : ℝ) (N + k)) ^ (2 : ℕ) := by
  have hfun :
      (fun k : ℕ ↦ geometricLayerMass (1 / 4 : ℝ) (N + k)) =
        fun k : ℕ ↦ (1 / 4 : ℝ) ^ N * geometricLayerMass (1 / 4 : ℝ) k := by
    funext k
    simp only [geometricLayerMass, pow_add]
    ring
  rw [hfun, tsum_mul_left,
    tsum_geometricLayerMass_eq_one (q := (1 / 4 : ℝ)) (by norm_num) (by norm_num), mul_one]
  rw [tsum_geometricLayerMass_half_shift]
  rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ (2 : ℕ) by norm_num]
  rw [← pow_mul, ← pow_mul]
  congr 1
  omega

end GaloisForLFunctions.HTGeometry
