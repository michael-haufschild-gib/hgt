import GaloisForLFunctions.RHTower.XiAperturePoissonValuationClockShuttle
import GaloisForLFunctions.RHTower.XiMobiusContinuousApertureSzegoMetric
import GaloisForLFunctions.RHTower.PhysicalPrimeEndpointMeshCoercivity
import GaloisForLFunctions.RHTower.EulerFisherCurvature

/-!
# Unit--double fused response and physical endpoint renormalization

Complete valuation fusion between the distinguished apertures `1` and `2` produces the signed
prime response `-1 / (p + 1)`.  This is exactly the negative Möbius damping already present in
the true-aperture Hilbert feature.  After multiplication by the prime clock, the physical endpoint
weight `log p / p` differs from the negative fused response current by the positive, summable
remainder `log p / (p * (p + 1))`.

Thus the positive true-aperture metric is the quadratic compression of a canonical signed response
current, while the physical endpoint carrier is its trace-class renormalization.  This module does
not assert the still-open global response-cancellation estimate.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

private theorem xiPrimeValuationGeometricNode_one_eq_inv
    (p : Nat.Primes) :
    xiPrimeValuationGeometricNode 1 p = ((p : ℝ))⁻¹ := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  rw [xiPrimeValuationGeometricNode]
  rw [show -(1 : ℝ) * Real.log (p : ℝ) = -Real.log (p : ℝ) by ring]
  rw [Real.exp_neg, Real.exp_log hp]

private theorem xiPrimeValuationGeometricNode_two_eq_inv_sq
    (p : Nat.Primes) :
    xiPrimeValuationGeometricNode 2 p = ((p : ℝ))⁻¹ ^ 2 := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  rw [xiPrimeValuationGeometricNode]
  rw [show -(2 : ℝ) * Real.log (p : ℝ) =
      -Real.log (p : ℝ) + -Real.log (p : ℝ) by ring,
    Real.exp_add, Real.exp_neg, Real.exp_log hp]
  ring

/-- The completely valuation-fused unit-aperture density has its elementary prime form. -/
theorem poissonPrimeValuationFusedHalfDensity_one_eq
    (p : Nat.Primes) :
    poissonPrimeValuationFusedHalfDensity 1 p =
      1 / ((p : ℝ) - 1) := by
  let P : ℝ := p
  have hP1 : 1 < P := by
    dsimp [P]
    exact_mod_cast p.prop.one_lt
  have hP0 : P ≠ 0 := by positivity
  have hPm1 : P - 1 ≠ 0 := by linarith
  rw [poissonPrimeValuationFusedHalfDensity_eq_geometric (by norm_num),
    xiPrimeValuationGeometricNode_one_eq_inv]
  change 1 * P⁻¹ * (1 - P⁻¹)⁻¹ = 1 / (P - 1)
  field_simp [hP0, hPm1]

/-- The completely valuation-fused double-aperture density has its elementary prime form. -/
theorem poissonPrimeValuationFusedHalfDensity_two_eq
    (p : Nat.Primes) :
    poissonPrimeValuationFusedHalfDensity 2 p =
      2 / ((p : ℝ) ^ 2 - 1) := by
  let P : ℝ := p
  have hP1 : 1 < P := by
    dsimp [P]
    exact_mod_cast p.prop.one_lt
  have hP0 : P ≠ 0 := by positivity
  have hPsq : P ^ 2 - 1 ≠ 0 := by nlinarith
  rw [poissonPrimeValuationFusedHalfDensity_eq_geometric (by norm_num),
    xiPrimeValuationGeometricNode_two_eq_inv_sq]
  change 2 * (P⁻¹ ^ 2) * (1 - P⁻¹ ^ 2)⁻¹ = 2 / (P ^ 2 - 1)
  field_simp [hP0, hPsq]

/-- **Unit--double fusion law.**  Complete valuation fusion between the distinguished apertures
`1` and `2` is exactly the negative critical Möbius damping. -/
theorem poissonPrimeValuationFusedScaleShuttle_one_two_eq
    (p : Nat.Primes) :
    poissonPrimeValuationFusedScaleShuttle 1 2 p =
      -1 / ((p : ℝ) + 1) := by
  let P : ℝ := p
  have hP1 : 1 < P := by
    dsimp [P]
    exact_mod_cast p.prop.one_lt
  have hPm1 : P - 1 ≠ 0 := by linarith
  have hPp1 : P + 1 ≠ 0 := by linarith
  have hPsq : P ^ 2 - 1 ≠ 0 := by nlinarith
  rw [poissonPrimeValuationFusedScaleShuttle,
    poissonPrimeValuationFusedHalfDensity_two_eq,
    poissonPrimeValuationFusedHalfDensity_one_eq]
  change 2 / (P ^ 2 - 1) - 1 / (P - 1) = -1 / (P + 1)
  field_simp [hPm1, hPp1, hPsq]
  ring

/-- Equivalent source form: the unit--double response current is the negative of the exact
critical Möbius coefficient used by the true-aperture frame. -/
theorem poissonPrimeValuationFusedScaleShuttle_one_two_eq_neg_mobiusDamping
    (p : Nat.Primes) :
    poissonPrimeValuationFusedScaleShuttle 1 2 p =
      -(xiTransversePrimeApertureDiskNode 1 p /
        (1 + xiTransversePrimeApertureDiskNode 1 p)) := by
  let P : ℝ := p
  have hP0 : P ≠ 0 := by
    dsimp [P]
    exact_mod_cast p.prop.ne_zero
  have hPp1 : P + 1 ≠ 0 := by positivity
  rw [poissonPrimeValuationFusedScaleShuttle_one_two_eq,
    xiTransversePrimeApertureDiskNode_one_eq_inv]
  change -1 / (P + 1) = -(P⁻¹ / (1 + P⁻¹))
  field_simp [hP0, hPp1]

/-- Every continuous true-aperture depth feature is the signed unit--double response current
dressed by its normalized geometric depth wavelet. -/
theorem xiMobiusPrimeSchurContinuousForwardDifference_eq_neg_fusedShuttle
    (a : ℝ) (p : Nat.Primes) (e : ℕ) :
    xiMobiusPrimeSchurContinuousForwardDifference a p e =
      -poissonPrimeValuationFusedScaleShuttle 1 2 p *
        (1 - xiMobiusContinuousApertureDiskNode a p) *
          xiMobiusContinuousApertureDiskNode a p ^ e := by
  rw [xiMobiusPrimeSchurContinuousForwardDifference_eq_geometric,
    poissonPrimeValuationFusedScaleShuttle_one_two_eq_neg_mobiusDamping]
  ring

/-- The local true-aperture Szegő metric is the quadratic compression of the signed unit--double
response current. -/
theorem xiMobiusPrimeContinuousApertureSzegoMetric_eq_fusedShuttle_sq
    (a b : ℝ) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureSzegoMetric a b p =
      poissonPrimeValuationFusedScaleShuttle 1 2 p ^ 2 *
        (1 - xiMobiusContinuousApertureDiskNode a p) *
        (1 - xiMobiusContinuousApertureDiskNode b p) /
        (1 - xiMobiusContinuousApertureDiskNode a p *
          xiMobiusContinuousApertureDiskNode b p) := by
  rw [xiMobiusPrimeContinuousApertureSzegoMetric,
    poissonPrimeValuationFusedScaleShuttle_one_two_eq_neg_mobiusDamping]
  ring

/-- The clocked signed response current produced by unit--double valuation fusion. -/
def xiUnitDoubleFusedPrimeResponseCurrent (p : Nat.Primes) : ℝ :=
  Real.log (p : ℝ) * poissonPrimeValuationFusedScaleShuttle 1 2 p

/-- The trace-class correction from the clocked fused response weight to the physical endpoint
weight. -/
def xiPhysicalEndpointResponseWeightRemainder (p : Nat.Primes) : ℝ :=
  Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) + 1))

theorem xiUnitDoubleFusedPrimeResponseCurrent_eq
    (p : Nat.Primes) :
    xiUnitDoubleFusedPrimeResponseCurrent p =
      -Real.log (p : ℝ) / ((p : ℝ) + 1) := by
  rw [xiUnitDoubleFusedPrimeResponseCurrent,
    poissonPrimeValuationFusedScaleShuttle_one_two_eq]
  ring

/-- **Physical response renormalization.**  The ordinary-prime endpoint weight is the negative
clocked unit--double response current plus an inverse-square correction. -/
theorem physicalPrimeEndpointWeight_eq_neg_fusedResponse_add_remainder
    (p : Nat.Primes) :
    physicalPrimeEndpointWeight p =
      -xiUnitDoubleFusedPrimeResponseCurrent p +
        xiPhysicalEndpointResponseWeightRemainder p := by
  let P : ℝ := p
  have hP0 : P ≠ 0 := by
    dsimp [P]
    exact_mod_cast p.prop.ne_zero
  have hPp1 : P + 1 ≠ 0 := by positivity
  rw [physicalPrimeEndpointWeight,
    xiUnitDoubleFusedPrimeResponseCurrent_eq,
    xiPhysicalEndpointResponseWeightRemainder]
  change Real.log P / P = -(-Real.log P / (P + 1)) +
    Real.log P / (P * (P + 1))
  field_simp [hP0, hPp1]

theorem xiPhysicalEndpointResponseWeightRemainder_pos
    (p : Nat.Primes) :
    0 < xiPhysicalEndpointResponseWeightRemainder p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
  exact div_pos (Real.log_pos hp1) (mul_pos (by positivity) (by positivity))

theorem xiPhysicalEndpointResponseWeightRemainder_le_log_div_sq
    (p : Nat.Primes) :
    xiPhysicalEndpointResponseWeightRemainder p <=
      Real.log (p : ℝ) / (p : ℝ) ^ 2 := by
  let P : ℝ := p
  have hP1 : 1 < P := by
    dsimp [P]
    exact_mod_cast p.prop.one_lt
  have hlog : 0 <= Real.log P := (Real.log_pos hP1).le
  have hleft : 0 < P * (P + 1) := by positivity
  have hright : 0 < P ^ 2 := by positivity
  rw [xiPhysicalEndpointResponseWeightRemainder]
  change Real.log P / (P * (P + 1)) <= Real.log P / P ^ 2
  rw [div_le_div_iff₀ hleft hright]
  nlinarith

private theorem summable_log_nat_div_sq :
    Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ 2) := by
  have h := RHTower.summable_abs_log_natCast_pow_mul_rpow_neg 1 2 (by norm_num)
  apply h.congr
  intro n
  rcases n with _ | n
  · simp
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlog : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by norm_num)
  rw [abs_of_nonneg hlog, pow_one, Real.rpow_neg hn.le]
  rw [show ((n + 1 : ℕ) : ℝ) ^ (2 : ℝ) =
      ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) by
    exact Real.rpow_natCast _ 2]
  field_simp

/-- The correction from the fused response current to the physical endpoint weight is trace
class over all ordinary primes. -/
theorem summable_xiPhysicalEndpointResponseWeightRemainder :
    Summable xiPhysicalEndpointResponseWeightRemainder := by
  have hprime : Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) / (p : ℝ) ^ 2) :=
    summable_log_nat_div_sq.comp_injective Subtype.val_injective
  exact Summable.of_nonneg_of_le
    (fun p => (xiPhysicalEndpointResponseWeightRemainder_pos p).le)
    xiPhysicalEndpointResponseWeightRemainder_le_log_div_sq hprime

end

end RHTower
