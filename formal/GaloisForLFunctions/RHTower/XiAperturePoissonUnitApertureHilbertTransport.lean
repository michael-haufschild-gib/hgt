import GaloisForLFunctions.RHTower.XiAperturePoissonValuationClockShuttle
import GaloisForLFunctions.RHTower.XiMobiusContinuousApertureSzegoMetric

/-!
# Unit-aperture Hilbert transport for the valuation-fused Xi--Poisson response

Complete valuation fusion turns the actual Xi prime clock into a signed Poisson response current.
This module compares its unit-aperture coefficient directly with the diagonal of the true incoming
Möbius--Szegő aperture metric.  The exact squared gain at prime `p`, with `q=p⁻¹`, is

`((1+q)/(1-q))^(3 : ℕ)`.

It is bounded sharply by `27`, with equality at `p=2`.  Consequently the complete fused response
at the minimal positive integral aperture is an all-prime Hilbert vector.  This is a raywise
source-to-response energy theorem; it does not construct the still-missing completed
prime--Gamma response operator and does not imply RH.
-/

namespace RHTower

noncomputable section

/-- Raywise squared gain from the true aperture-one Szegő source metric to the fully fused
Poisson response. -/
def xiApertureOnePrimeFusedResponseGainSq (p : Nat.Primes) : ℝ :=
  let q := xiTransversePrimeApertureDiskNode 1 p
  ((1 + q) / (1 - q)) ^ (3 : ℕ)

theorem xiApertureOnePrimeFusedResponseGainSq_pos (p : Nat.Primes) :
    0 < xiApertureOnePrimeFusedResponseGainSq p := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hq1 : q < 1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  exact pow_pos (div_pos (by linarith) (by linarith)) _

/-- The prime-two channel gives the sharp global gain bound. -/
theorem xiApertureOnePrimeFusedResponseGainSq_le_twentySeven (p : Nat.Primes) :
    xiApertureOnePrimeFusedResponseGainSq p ≤ 27 := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hq1 : q < 1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
  have hqhalf : q ≤ 1 / 2 := by
    rw [show q = ((p : ℝ))⁻¹ by
      exact xiTransversePrimeApertureDiskNode_one_eq_inv p]
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2)
  have hratio0 : 0 ≤ (1 + q) / (1 - q) :=
    div_nonneg (by linarith) (by linarith)
  have hratio3 : (1 + q) / (1 - q) ≤ 3 := by
    rw [div_le_iff₀ (by linarith : 0 < 1 - q)]
    linarith
  rw [xiApertureOnePrimeFusedResponseGainSq]
  change ((1 + q) / (1 - q)) ^ (3 : ℕ) ≤ 27
  calc
    ((1 + q) / (1 - q)) ^ (3 : ℕ) ≤ 3 ^ (3 : ℕ) := by gcongr
    _ = 27 := by norm_num

theorem xiApertureOnePrimeFusedResponseGainSq_primeTwo :
    xiApertureOnePrimeFusedResponseGainSq
      (⟨2, by norm_num⟩ : Nat.Primes) = 27 := by
  rw [xiApertureOnePrimeFusedResponseGainSq,
    xiTransversePrimeApertureDiskNode_one_eq_inv]
  norm_num

private theorem xiPrimeValuationGeometricNode_one_eq_transverse
    (p : Nat.Primes) :
    xiPrimeValuationGeometricNode 1 p =
      xiTransversePrimeApertureDiskNode 1 p := by
  unfold xiPrimeValuationGeometricNode xiTransversePrimeApertureDiskNode
  norm_num

private theorem xiMobiusContinuousApertureDiskNode_one_eq_transverse
    (p : Nat.Primes) :
    xiMobiusContinuousApertureDiskNode 1 p =
      xiTransversePrimeApertureDiskNode 1 p := by
  unfold xiMobiusContinuousApertureDiskNode xiTransversePrimeApertureDiskNode
  norm_num

/-- Exact local energy identity between the fully valuation-fused Poisson response and the actual
true aperture-one Szegő source ray. -/
theorem poissonPrimeValuationFusedHalfDensity_one_sq_eq_gain_mul_trueApertureMetric
    (p : Nat.Primes) :
    poissonPrimeValuationFusedHalfDensity 1 p ^ (2 : ℕ) =
      xiApertureOnePrimeFusedResponseGainSq p *
        xiMobiusPrimeContinuousApertureSzegoMetric 1 1 p := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hq1 : q < 1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  have hminus : 1 - q ≠ 0 := by linarith
  have hplus : 1 + q ≠ 0 := by linarith
  rw [poissonPrimeValuationFusedHalfDensity_eq_geometric (by norm_num),
    xiMobiusPrimeContinuousApertureSzegoMetric_self (by norm_num)]
  rw [xiPrimeValuationGeometricNode_one_eq_transverse,
    xiMobiusContinuousApertureDiskNode_one_eq_transverse]
  change (1 * q * (1 - q)⁻¹) ^ (2 : ℕ) =
    ((1 + q) / (1 - q)) ^ (3 : ℕ) *
      ((q / (1 + q)) ^ (2 : ℕ) * ((1 - q) / (1 + q)))
  field_simp [hminus, hplus]

/-- The complete aperture-one response energy is pointwise controlled by the actual true-aperture
source metric with sharp universal squared gain `27`. -/
theorem poissonPrimeValuationFusedHalfDensity_one_sq_le_trueApertureMetric
    (p : Nat.Primes) :
    poissonPrimeValuationFusedHalfDensity 1 p ^ (2 : ℕ) ≤
      27 * xiMobiusPrimeContinuousApertureSzegoMetric 1 1 p := by
  rw [poissonPrimeValuationFusedHalfDensity_one_sq_eq_gain_mul_trueApertureMetric]
  exact mul_le_mul_of_nonneg_right
    (xiApertureOnePrimeFusedResponseGainSq_le_twentySeven p)
    (xiMobiusPrimeContinuousApertureSzegoMetric_self_nonneg (by norm_num) p)

/-- The valuation-fused aperture-one Poisson response is an all-prime Hilbert vector. -/
theorem summable_poissonPrimeValuationFusedHalfDensity_one_sq :
    Summable (fun p : Nat.Primes =>
      poissonPrimeValuationFusedHalfDensity 1 p ^ (2 : ℕ)) := by
  have hmetric : Summable (fun p : Nat.Primes =>
      xiMobiusPrimeContinuousApertureSzegoMetric 1 1 p) :=
    summable_xiMobiusPrimeContinuousApertureSzegoMetric_self (by norm_num)
  exact Summable.of_nonneg_of_le
    (fun p => sq_nonneg _)
    poissonPrimeValuationFusedHalfDensity_one_sq_le_trueApertureMetric
    (Summable.mul_left 27 hmetric)

end

end RHTower
