import GaloisForLFunctions.RHTower.HedenmalmThetaMobiusPoleUnitPrimeCellThermalCascade
import GaloisForLFunctions.RHTower.PrimeValuationKakutaniRadialPurity

/-!
# Wall freezing of the Route-P prime-cell cascade

For interior two-sided apertures, P-G45 proves that every prime Hellinger defect has one finite
thermal peak and then returns to vacuum.  This module classifies the singular aperture wall.

At eccentricity `r = 1`, the peak escapes to infinity.  The cell defect becomes strictly
increasing and freezes at its base prime odds `q`.  On the literal prime path `q = 1/p`, this
frozen residue is exactly the principal `1/p` class behind Route P's quantized harmonic escape.
The existing physical Hellinger gap is the unprojectivized numerator of the same wall cell.

This is an unconditional phase-transition theorem, not an RH proof.  It identifies the Route-P
obstruction as a boundary-frozen Euler defect rather than an independent endpoint anomaly.
-/

open Filter Set Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- At the singular aperture wall the thermal balance loses its turning term and becomes a
strictly positive constant. -/
theorem thermalBernoulliPeakBalance_one (q : ℝ) {T : ℝ} (hT : T ≠ 0) :
    thermalBernoulliPeakBalance q 1 T = 2 * (1 + q) := by
  rw [thermalBernoulliPeakBalance, thermalBernoulliMidpointMass]
  simp only [one_add_one_eq_two, sub_self, zero_mul,
    Real.rpow_neg_one]
  field_simp
  ring

/-- Closed wall formula for the projective prime-cell defect odds. -/
theorem thermalBernoulliMidpointDefectOdds_one
    {q T : ℝ} (hT : T ≠ 0) :
    thermalBernoulliMidpointDefectOdds q 1 T =
      q * (T - 1) ^ 2 / (T + q) ^ 2 := by
  rw [thermalBernoulliMidpointDefectOdds, bernoulliMidpointDefectOdds,
    thermalBernoulliMidpointMass, Real.rpow_neg_one]
  field_simp [hT]

/-- Wall defect has no interior peak: it increases strictly at every finite positive thermal
ratio. -/
theorem deriv_thermalBernoulliMidpointDefectOdds_one_pos
    {q T : ℝ} (hq : 0 < q) (hT : 1 < T) :
    0 < deriv (thermalBernoulliMidpointDefectOdds q 1) T := by
  rw [(hasDerivAt_thermalBernoulliMidpointDefectOdds hq hT).deriv,
    thermalBernoulliPeakBalance_one q (lt_trans zero_lt_one hT).ne']
  have hmass : 0 < thermalBernoulliMidpointMass q 1 T :=
    mul_pos hq (Real.rpow_pos_of_pos (lt_trans zero_lt_one hT) _)
  have hodds : 0 < thermalBernoulliMidpointDefectOdds q 1 T := by
    rw [thermalBernoulliMidpointDefectOdds_one (lt_trans zero_lt_one hT).ne']
    positivity
  have hbalance : 0 < 2 * (1 + q) := by positivity
  have hden : 0 < T * (T - 1) * (1 + thermalBernoulliMidpointMass q 1 T) := by
    positivity
  exact div_pos (mul_pos hodds hbalance) hden

/-- The wall defect freezes at its base odds instead of returning to the vacuum. -/
theorem tendsto_thermalBernoulliMidpointDefectOdds_one_atTop (q : ℝ) :
    Tendsto (thermalBernoulliMidpointDefectOdds q 1) atTop (𝓝 q) := by
  have hinv : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hratio : Tendsto (fun T : ℝ => (T - 1) / (T + q)) atTop (𝓝 1) := by
    have hrew : (fun T : ℝ => (T - 1) / (T + q)) =ᶠ[atTop]
        fun T => (1 - T⁻¹) / (1 + q * T⁻¹) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      field_simp [hT.ne']
    apply Tendsto.congr' hrew.symm
    have hnum : Tendsto (fun T : ℝ => 1 - T⁻¹) atTop (nhds 1) := by
      simpa using (tendsto_const_nhds.sub hinv :
        Tendsto (fun T : ℝ => 1 - T⁻¹) atTop (nhds (1 - 0)))
    have hden : Tendsto (fun T : ℝ => 1 + q * T⁻¹) atTop (nhds 1) := by
      simpa using (tendsto_const_nhds.add (hinv.const_mul q) :
        Tendsto (fun T : ℝ => 1 + q * T⁻¹) atTop (nhds (1 + q * 0)))
    have hquot : Tendsto
        ((fun T : ℝ => 1 - T⁻¹) / (fun T : ℝ => 1 + q * T⁻¹))
        atTop (nhds 1) := by
      convert hnum.div hden one_ne_zero using 1
      all_goals norm_num
    exact hquot.congr' (Eventually.of_forall fun _ => rfl)
  have hformula : (thermalBernoulliMidpointDefectOdds q 1) =ᶠ[atTop]
      fun T => q * ((T - 1) / (T + q)) ^ 2 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [thermalBernoulliMidpointDefectOdds_one hT.ne']
    field_simp
  apply Tendsto.congr' hformula.symm
  simpa using hratio.pow 2 |>.const_mul q

/-- For an interior aperture, every peak lies beyond the diverging wall scale `2/(r-1)`. -/
theorem two_div_sub_one_lt_thermalBernoulliPeak
    {q r Tstar : ℝ} (hr : 1 < r)
    (hstar : (r + 1) / (r - 1) < Tstar ∧
      thermalBernoulliPeakBalance q r Tstar = 0) :
    2 / (r - 1) < Tstar := by
  have hrm : 0 < r - 1 := sub_pos.mpr hr
  calc
    2 / (r - 1) < (r + 1) / (r - 1) :=
      div_lt_div_of_pos_right (by linarith) hrm
    _ < Tstar := hstar.1

/-- The wall cell is exactly the projectivization of Route P's physical prime-valuation
Hellinger gap. -/
theorem thermalBernoulliMidpointDefectOdds_prime_eq_hellingerGap
    (p : Nat.Primes) {d : ℝ} (_hd : 0 < d) :
    thermalBernoulliMidpointDefectOdds ((p : ℝ) ^ (-1 : ℝ)) 1
        ((p : ℝ) ^ d) =
      RHTower.primeValuationHellingerGap (-d) p /
        (1 + (p : ℝ) ^ (-(1 + d))) ^ 2 := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hT : (p : ℝ) ^ d ≠ 0 := (Real.rpow_pos_of_pos hp d).ne'
  rw [thermalBernoulliMidpointDefectOdds_one hT,
    RHTower.primeValuationHellingerGap]
  have hhalf :
      (p : ℝ) ^ (-(1 / 2 : ℝ)) - (p : ℝ) ^ (-(1 / 2 - -d)) =
        (p : ℝ) ^ (-(1 / 2 : ℝ)) * (1 - (p : ℝ) ^ (-d)) := by
    rw [mul_sub, mul_one, ← Real.rpow_add hp]
    congr 1
    ring
  have hrootSq : ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 =
      (p : ℝ) ^ (-1 : ℝ) := by
    rw [pow_two, ← Real.rpow_add hp]
    congr 1
    ring
  have hnumScale : (p : ℝ) ^ d - 1 =
      (p : ℝ) ^ d * (1 - (p : ℝ) ^ (-d)) := by
    rw [mul_sub, mul_one, ← Real.rpow_add hp]
    norm_num
  have hdenScale : (p : ℝ) ^ d + (p : ℝ) ^ (-1 : ℝ) =
      (p : ℝ) ^ d * (1 + (p : ℝ) ^ (-(1 + d))) := by
    rw [mul_add, mul_one, ← Real.rpow_add hp]
    congr 2
    ring
  rw [hhalf, mul_pow, hrootSq, hnumScale, hdenScale, mul_pow]
  field_simp [hT]

/-- Literal frozen residue at prime `p`. -/
theorem tendsto_thermalBernoulliMidpointDefectOdds_prime_wall_atTop
    (p : Nat.Primes) :
    Tendsto
      (thermalBernoulliMidpointDefectOdds ((p : ℝ) ^ (-1 : ℝ)) 1)
      atTop (𝓝 ((p : ℝ) ^ (-1 : ℝ))) :=
  tendsto_thermalBernoulliMidpointDefectOdds_one_atTop _

end

end RHTower.HedenmalmThetaSource
