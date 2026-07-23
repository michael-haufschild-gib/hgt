import GaloisForLFunctions.RHTower.HeatApertureEchoHankel
import GaloisForLFunctions.RHTower.EulerFisherLowTemperature

/-!
# Mixed heat-echo/Euler cold-end ground selection

Heat-aperture depth multiplies the Euler prime-power carrier by powers of the reciprocal integer,
while the Fisher hierarchy multiplies the same carrier by powers of logarithmic energy.  These are
one mixed moment hierarchy.  Along integer heat depth, every logarithmic order has the same exact
prime-two ground-state limit after the natural dyadic normalization.
-/

namespace GaloisForLFunctions

open Filter Topology

noncomputable section

/-- Mixed reciprocal-node/log-energy moment of the heat-aperture prime-power carrier. -/
def heatApertureEulerMixedMoment (sigma : ℝ) (q k m : ℕ) : ℝ :=
  ∑' z : Nat.Primes × ℕ,
    heatAperturePrimePowerBaseWeight sigma q z *
      heatAperturePrimePowerNode z ^ k *
        RHTower.eulerPrimePowerEnergy z ^ m

/-- Integer heat depth is exactly translation of inverse temperature in every Euler Fisher
logarithmic moment. -/
theorem heatApertureEulerMixedMoment_eq_eulerFisherMoment
    (sigma : ℝ) (q k m : ℕ) :
    heatApertureEulerMixedMoment sigma q k m =
      RHTower.fisherWeightedTsumMoment
        (RHTower.eulerPrimePowerWeight
          (1 - sigma + (q : ℝ) + (k : ℝ)))
        RHTower.eulerPrimePowerEnergy m := by
  rw [heatApertureEulerMixedMoment, RHTower.fisherWeightedTsumMoment]
  apply tsum_congr
  intro z
  have hN : 0 < (RHTower.eulerPrimePowerNat z : ℝ) := by
    exact_mod_cast (show 0 < RHTower.eulerPrimePowerNat z by
      dsimp [RHTower.eulerPrimePowerNat]
      exact pow_pos z.1.property.pos _)
  rw [heatAperturePrimePowerBaseWeight, heatAperturePrimePowerNode,
    RHTower.eulerPrimePowerWeight]
  have hexp : -(1 - sigma + (q : ℝ) + (k : ℝ)) =
      -(1 - sigma + (q : ℝ)) + -(k : ℝ) := by ring
  rw [RHTower.eulerPrimePowerWeight]
  rw [hexp, Real.rpow_add hN]
  have hkpow : (RHTower.eulerPrimePowerNat z : ℝ) ^ (-(k : ℝ)) =
      (RHTower.eulerPrimePowerNat z : ℝ)⁻¹ ^ k := by
    rw [Real.rpow_neg hN.le, Real.rpow_natCast, inv_pow]
  rw [hkpow]
  ring

/-- The zeroth logarithmic member is exactly the real heat-aperture log echo. -/
theorem heatApertureEulerMixedMoment_zero_eq_realLogEcho
    {sigma : ℝ} {q : ℕ} (hbeta : 1 < 1 - sigma + q) (k : ℕ) :
    heatApertureEulerMixedMoment sigma q k 0 =
      heatApertureRealLogEchoValue sigma (q + k) := by
  rw [heatApertureRealLogEchoValue_add_eq_moment hbeta]
  simp [heatApertureEulerMixedMoment]

/-- **Mixed cold-end universality law.**  For every logarithmic moment order, integer heat depth
selects the prime-two mode with exact normalized limit `(log 2)^m`. -/
theorem tendsto_heatApertureEulerMixedMoment_dyadicScaled
    (sigma : ℝ) (q m : ℕ) :
    Tendsto (fun k : ℕ =>
      (2 : ℝ) ^ (1 - sigma + (q : ℝ) + (k : ℝ)) *
        heatApertureEulerMixedMoment sigma q k m)
      atTop (𝓝 ((Real.log 2) ^ m)) := by
  have hshift : Tendsto
      (fun k : ℕ => 1 - sigma + (q : ℝ) + (k : ℝ)) atTop atTop := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds :
        Tendsto (fun k : ℕ => (k : ℝ) + (1 - sigma + (q : ℝ))) atTop atTop)
  have h := (RHTower.eulerPrimePowerMoment_scaled_tendsto m).comp hshift
  refine h.congr' ?_
  filter_upwards with k
  rw [heatApertureEulerMixedMoment_eq_eulerFisherMoment]
  rfl

/-- In particular, the raw real heat echo has exact prime-two ground normalization. -/
theorem tendsto_heatApertureRealLogEchoValue_dyadicScaled
    {sigma : ℝ} {q : ℕ} (hbeta : 1 < 1 - sigma + q) :
    Tendsto (fun k : ℕ =>
      (2 : ℝ) ^ (1 - sigma + (q : ℝ) + (k : ℝ)) *
        heatApertureRealLogEchoValue sigma (q + k))
      atTop (𝓝 1) := by
  have h := tendsto_heatApertureEulerMixedMoment_dyadicScaled sigma q 0
  refine h.congr' ?_
  filter_upwards with k
  rw [heatApertureEulerMixedMoment_zero_eq_realLogEcho hbeta]

end

end GaloisForLFunctions
