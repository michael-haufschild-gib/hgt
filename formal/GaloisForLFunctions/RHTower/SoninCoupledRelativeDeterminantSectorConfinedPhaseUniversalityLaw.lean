import GaloisForLFunctions.RHTower.PrimeArchBernsteinSectorConfinedPhase
import GaloisForLFunctions.RHTower.SoninCoupledNormalizedDeterminantCollar

/-!
# Sector-confined coupled-Sonin relative-determinant phase

The exact two-sided Bernstein comparison transports the narrow endpoint phase chamber to every
nondegenerate coupled-Sonin aperture.  The logarithmic-derivative energy of each concrete relative
determinant decays above the same source-derived ceiling; if RH fails, it has a surviving exponent
strictly between one and that ceiling.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- An affine two-sided energy comparison cannot hide exponential survival at a fixed base. -/
theorem tendsto_div_pow_of_le_two_add_two
    {E D : ℕ → ℝ} {r : ℝ} (hr : 1 < r)
    (hE : ∀ n, 0 ≤ E n) (hED : ∀ n, E n ≤ 2 + 2 * D n)
    (hD : Tendsto (fun n : ℕ => D n / r ^ n) atTop (nhds 0)) :
    Tendsto (fun n : ℕ => E n / r ^ n) atTop (nhds 0) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hq0 : 0 ≤ 1 / r := by positivity
  have hq1 : 1 / r < 1 := (div_lt_one hr0).2 hr
  have hpow : Tendsto (fun n : ℕ => (1 / r) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hupper : Tendsto
      (fun n : ℕ => 2 * (1 / r) ^ n + 2 * (D n / r ^ n))
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hpow).add (tendsto_const_nhds.mul hD)
  apply squeeze_zero
    (fun n => div_nonneg (hE n) (pow_nonneg hr0.le n))
    (fun n => ?_) hupper
  calc
    E n / r ^ n ≤ (2 + 2 * D n) / r ^ n :=
      div_le_div_of_nonneg_right (hED n) (pow_nonneg hr0.le n)
    _ = 2 * (1 / r) ^ n + 2 * (D n / r ^ n) := by
      rw [div_pow]
      ring

/-- Failure of fixed-base decay transfers against the direction of an affine energy bound. -/
theorem not_tendsto_div_pow_of_le_two_add_two
    {E D : ℕ → ℝ} {r : ℝ} (hr : 1 < r)
    (hE : ∀ n, 0 ≤ E n) (hED : ∀ n, E n ≤ 2 + 2 * D n)
    (hnot : ¬ Tendsto (fun n : ℕ => E n / r ^ n) atTop (nhds 0)) :
    ¬ Tendsto (fun n : ℕ => D n / r ^ n) atTop (nhds 0) := by
  exact fun hD => hnot (tendsto_div_pow_of_le_two_add_two hr hE hED hD)

/-- Every concrete coupled-Sonin relative determinant has the same sharp source-derived phase
ceiling as the endpoint prime--Gamma energy. -/
structure SoninCoupledRelativeDeterminantSectorConfinedPhaseUniversalCertificate
    (a : SoninCoupledNondegenerateAperture) : Prop where
  exactCeiling : xiSectorConfinedBernsteinAmplitudeBase ^ 2 = 251001 / 250000
  decayAboveCeiling :
    ∀ r : ℝ, xiSectorConfinedBernsteinAmplitudeBase ^ 2 < r →
      Tendsto (fun n : ℕ =>
        bernsteinCoefficientPurity
            (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment a) n /
          r ^ n) atTop (nhds 0)
  falseRHSurvivingPhase :
    ¬ RiemannHypothesis →
      ∃ r : ℝ,
        1 < r ∧ r < xiSectorConfinedBernsteinAmplitudeBase ^ 2 ∧
          ¬ Tendsto (fun n : ℕ =>
            bernsteinCoefficientPurity
                (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment a) n /
              r ^ n) atTop (nhds 0)

/-- **Sector-confined coupled-Sonin relative-determinant phase law.**  Every nondegenerate aperture
obeys the same exact `251001/250000` exponential ceiling.  Above it determinant-defect energy
always decays; failure of RH forces a surviving determinant exponent strictly below it. -/
theorem soninCoupledRelativeDeterminant_sectorConfinedPhaseUniversalCertificate
    (a : SoninCoupledNondegenerateAperture) :
    SoninCoupledRelativeDeterminantSectorConfinedPhaseUniversalCertificate a := by
  refine {
    exactCeiling := xiSectorConfinedBernsteinAmplitudeBase_sq_eq
    decayAboveCeiling := ?_
    falseRHSurvivingPhase := ?_ }
  · intro r hr
    have hone : 1 < xiSectorConfinedBernsteinAmplitudeBase ^ 2 := by
      have hbase := one_lt_xiSectorConfinedBernsteinAmplitudeBase
      nlinarith
    apply tendsto_div_pow_of_le_two_add_two
      (hone.trans hr)
      (fun n => bernsteinCoefficientPurity_nonneg _ n)
  · intro n
    rw [← soninCoupledEndpointBernsteinMismatch_eq_relativeDeterminantPurity a n]
    exact
      soninCoupledEndpointBernsteinMismatch_le_two_add_two_primeArchEndpointPurity_quantum a n
  · exact tendsto_primeArchEndpointBernsteinPurity_div_pow_of_sectorBase_sq_lt hr
  · intro hRH
    obtain ⟨r, hr, hrbase, hnot⟩ :=
      exists_strict_sectorConfined_primeArchEndpointBernsteinPurity_phase_of_not_riemannHypothesis
        hRH
    refine ⟨r, hr, hrbase, ?_⟩
    apply not_tendsto_div_pow_of_le_two_add_two hr
      (fun n => bernsteinCoefficientPurity_nonneg _ n)
      (fun n => primeArchEndpointBernsteinPurity_le_two_add_two_relativeDeterminantPurity a n)
      hnot

end

end RHTower
