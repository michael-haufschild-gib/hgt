import GaloisForLFunctions.BiarithmeticGeometry.HorizonAffineActions
import Mathlib.Tactic.NormNum

/-!
# The affine relation does not choose a dilation normalization

Every multiplicative scalar character twists the finite-horizon affine action. Composition and
the ring relation survive exactly. The origin matrix coefficient recovers the character, so the
freedom is visible and cannot be removed by the relation alone.
-/

noncomputable section

namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Multiplicative changes of dilation normalization leave translations unchanged. -/
def twistedHorizonAffine (N : ℕ) (w : ℕ+ →* ℝ) (a : ℕ+) (b : ℕ) :
    HorizonSpace N →ₗ[ℝ] HorizonSpace N := w a • horizonAffine N a b

theorem twistedHorizonAffine_comp (N : ℕ) (w : ℕ+ →* ℝ) (a c : ℕ+) (b d : ℕ) :
    (twistedHorizonAffine N w a b).comp (twistedHorizonAffine N w c d) =
      twistedHorizonAffine N w (a * c) (a * d + b) := by
  apply LinearMap.ext
  intro v
  change w a • horizonAffine N a b (w c • horizonAffine N c d v) =
    w (a * c) • horizonAffine N (a * c) (a * d + b) v
  rw [map_smul, smul_smul, map_mul]
  exact congrArg (fun z : HorizonSpace N => (w a * w c) • z)
    (congrArg (fun L : HorizonSpace N →ₗ[ℝ] HorizonSpace N => L v)
      (horizonAffine_comp N a c b d))

/-- The ring relation holds for every multiplicative scalar normalization. -/
theorem twisted_horizon_ring_relation (N : ℕ) (w : ℕ+ →* ℝ) (a : ℕ+) :
    (twistedHorizonAffine N w a 0).comp (twistedHorizonAffine N w 1 1) =
      (twistedHorizonAffine N w 1 a).comp (twistedHorizonAffine N w a 0) := by
  simp only [twistedHorizonAffine_comp, mul_one, one_mul, mul_zero, add_zero, zero_add]

/-- The origin coefficient reads the chosen dilation character exactly. -/
theorem twisted_origin_coefficient (N : ℕ) (w : ℕ+ →* ℝ) (a : ℕ+) :
    twistedHorizonAffine N w a 0 (horizonCell N 0) 0 = w a := by
  simp only [twistedHorizonAffine, LinearMap.smul_apply, horizonAffine_cell_nat,
    mul_zero, add_zero, Pi.smul_apply, smul_eq_mul, horizonCell, Fin.val_zero, if_true, mul_one]

/-- Distinct scalar characters give distinct dilation operators at every horizon. -/
theorem twisted_dilation_eq_iff (N : ℕ) (w z : ℕ+ →* ℝ) (a : ℕ+) :
    twistedHorizonAffine N w a 0 = twistedHorizonAffine N z a 0 ↔ w a = z a := by
  constructor
  · intro h
    have h0 := congrArg (fun L : HorizonSpace N →ₗ[ℝ] HorizonSpace N =>
      L (horizonCell N 0) 0) h
    simpa only [twisted_origin_coefficient] using h0
  · intro h
    simp only [twistedHorizonAffine, h]

/-- Integer inverse-power characters provide explicit contracting scalar twists. -/
def inversePowerCharacter (r : ℕ) : ℕ+ →* ℝ where
  toFun a := ((a : ℝ) ^ r)⁻¹
  map_one' := by simp
  map_mul' a b := by simp only [PNat.mul_coe, Nat.cast_mul, mul_pow, mul_inv_rev]; ring

/-- Even the identity and inverse-linear normalizations give different operators with the same
affine covariance, at every horizon including the origin-only horizon. -/
theorem twisted_dilation_two_distinct (N : ℕ) :
    twistedHorizonAffine N (inversePowerCharacter 0) 2 0 ≠
      twistedHorizonAffine N (inversePowerCharacter 1) 2 0 := by
  rw [ne_eq, twisted_dilation_eq_iff]
  norm_num [inversePowerCharacter]

end GaloisForLFunctions.BiarithmeticGeometry
