import GaloisForLFunctions.RHTower.SoninCoupledBernsteinCollarQuantumDischarge
import GaloisForLFunctions.RHTower.PrimeArchBernsteinLoschmidtPurity

/-!
# Coupled-Sonin Bernstein mismatch criterion for RH

Complete Hausdorff positivity of the actual coupled-Sonin replica sequence removes the auxiliary
positivity premise from the collar comparison.  What remains is one concrete source estimate:
zero exponential density of the endpoint/coupled Bernstein mismatch.  This file records the
direct implication from that estimate to RH.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- A nonnegative sequence with arbitrarily thin exponential envelopes has zero exponential
rate in the limit formulation used by the endpoint Bernstein criterion. -/
theorem subexponentialSquareEnergyAtNatInfinity_of_unitCollarExponentialEnvelope
    {E : ℕ → ℝ} (hE : ∀ n, 0 ≤ E n)
    (h : UnitCollarExponentialEnvelope E) :
    SubexponentialSquareEnergyAtNatInfinity E := by
  intro r hr
  let ε : ℝ := (r - 1) / 2
  let s : ℝ := 1 + ε
  have hε : 0 < ε := by dsimp only [ε]; linarith
  have hs0 : 0 < s := by dsimp only [s, ε]; linarith
  have hsr : s < r := by dsimp only [s, ε]; linarith
  obtain ⟨C, hC, hbound⟩ := h ε hε
  have hratio0 : 0 ≤ s / r := div_nonneg hs0.le (by linarith)
  have hratio1 : s / r < 1 := (div_lt_one (by linarith)).2 hsr
  have hupper : Tendsto (fun n : ℕ => C * (s / r) ^ n) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hratio0 hratio1)
  apply squeeze_zero
    (fun n => div_nonneg (hE n) (pow_nonneg (by linarith) n))
    (fun n => ?_) hupper
  calc
    E n / r ^ n ≤ (C * s ^ n) / r ^ n :=
      div_le_div_of_nonneg_right (by simpa only [s] using hbound n)
        (pow_nonneg (by linarith) n)
    _ = C * (s / r) ^ n := by
      rw [div_pow]
      ring

/-- **Concrete coupled-Sonin source criterion.**  If the exact Bernstein packet mismatch between
one nondegenerate coupled-Sonin aperture and the endpoint prime--Gamma source has arbitrarily
thin exponential envelopes, then RH follows.  No Hausdorff, spectral-measure, or zero-location
hypothesis remains. -/
theorem riemannHypothesis_of_soninCoupledEndpointBernsteinMismatch_unitCollarEnvelope
    (a : SoninCoupledNondegenerateAperture)
    (h : UnitCollarExponentialEnvelope
      (soninCoupledEndpointBernsteinMismatch a)) :
    RiemannHypothesis := by
  apply riemannHypothesis_iff_primeArchEndpointBernsteinPurity_subexponential.mpr
  apply subexponentialSquareEnergyAtNatInfinity_of_unitCollarExponentialEnvelope
    (fun n => bernsteinCoefficientPurity_nonneg _ n)
  exact
    (primeArchEndpoint_unitCollarEnvelope_iff_soninCoupledMismatch_quantum a).mpr h

end

end RHTower
