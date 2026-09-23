import GaloisForLFunctions.RHTower.HedenmalmThetaCompletedResponseMarginalGaugeNoGo
import GaloisForLFunctions.RHTower.PrimeLogTripleCluster

/-!
# Route P physical-endpoint logarithmic boundary law

The physical endpoint marginal `log p / p` forces a much larger normalization than the original
Möbius half-density.  After this normalization its square has the exact closed form

`log(p) * φ_p(q)^(2 : ℕ) = (1 - p^(-|a(q)|))^(2 : ℕ)`.

Thus every nonneutral divisor copy has the universal logarithmic boundary profile
`φ_p(q)^(2 : ℕ) ~ 1 / log p`.  This is not an `ℓ²` source vector: square summability is equivalent to
neutrality, and global `ℓ²` admission is equivalent to RH.  The corrected endpoint coupling must
therefore act as a singular response form on finite packets; it cannot be justified by first
placing the normalized profile in an ordinary prime Hilbert space.
-/

open Filter
open scoped BigOperators RealInnerProductSpace Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Exact logarithmic profile forced by the physical endpoint marginal. -/
theorem log_mul_thetaPhysicalEndpointNormalizedHalfDensity_sq
    (p : Nat.Primes) (q : XiZeroCopy) :
    Real.log (p : ℝ) * thetaPhysicalEndpointNormalizedHalfDensity p q ^ 2 =
      (1 - (p : ℝ) ^ (-|primeDepthBVWoldXiCenteredRate q.1|)) ^ 2 := by
  let a : ℝ := primeDepthBVWoldXiCenteredRate q.1
  let P : ℝ := p
  have hP : 0 < P := by
    dsimp [P]
    exact_mod_cast p.2.pos
  have hP0 : P ≠ 0 := hP.ne'
  have hhalf :
      thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q ^ 2 =
        primeValuationHellingerGap (-|a|) p := by
    rw [thetaMobiusPrimeNormalProfileHalfDensityAmplitude_eq_channelGap,
      primeValuationHellingerGap_neg_abs_eq_routeNCriticalAmplitudeGap]
    split <;> ring
  have hmarg := physicalPrimeEndpointWeight_mul_normalizedHalfDensity_sq p q
  rw [physicalPrimeEndpointWeight, hhalf, primeValuationHellingerGap] at hmarg
  change Real.log P / P * thetaPhysicalEndpointNormalizedHalfDensity p q ^ 2 =
      (P ^ (-(1 / 2 : ℝ)) - P ^ (-(1 / 2 - -|a|))) ^ 2 at hmarg
  have hfactor :
      P ^ (-(1 / 2 - -|a|)) =
        P ^ (-(1 / 2 : ℝ)) * P ^ (-|a|) := by
    rw [← Real.rpow_add hP]
    congr 1
    ring
  have hsqrt : (P ^ (-(1 / 2 : ℝ))) ^ 2 = P⁻¹ := by
    rw [pow_two, ← Real.rpow_add hP]
    rw [show -(1 / 2 : ℝ) + -(1 / 2 : ℝ) = -1 by ring,
      Real.rpow_neg_one]
  rw [hfactor] at hmarg
  have hrhs :
      (P ^ (-(1 / 2 : ℝ)) -
          P ^ (-(1 / 2 : ℝ)) * P ^ (-|a|)) ^ 2 =
        P⁻¹ * (1 - P ^ (-|a|)) ^ 2 := by
    rw [← hsqrt]
    ring
  rw [hrhs] at hmarg
  field_simp [hP0] at hmarg ⊢
  simpa [P, a, mul_comm] using hmarg

/-- Off center, the logarithmically rescaled normalized profile converges to one along the actual
prime sequence. -/
theorem tendsto_log_mul_thetaPhysicalEndpointNormalizedHalfDensity_sq_of_boundaryFlux_ne_zero
    (q : XiZeroCopy) (hflux : thetaXiRankTwoBoundaryFlux q ≠ 0) :
    Tendsto
      (fun n : ℕ => Real.log (nthPrimeSubtype n : ℝ) *
        thetaPhysicalEndpointNormalizedHalfDensity (nthPrimeSubtype n) q ^ 2)
      atTop (𝓝 1) := by
  have hrate : primeDepthBVWoldXiCenteredRate q.1 ≠ 0 := by
    intro hzero
    apply hflux
    rw [thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate, hzero]
    ring
  have hprime :
      Tendsto (fun n : ℕ => (nthPrimeSubtype n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp nthPrimeSubtype_strictMono.tendsto_atTop
  have hpow :
      Tendsto
        (fun n : ℕ => (nthPrimeSubtype n : ℝ) ^
          (-|primeDepthBVWoldXiCenteredRate q.1|))
        atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (abs_pos.mpr hrate)).comp hprime
  have hlimit :
      Tendsto
        (fun n : ℕ =>
          ((1 : ℝ) - (nthPrimeSubtype n : ℝ) ^
            (-|primeDepthBVWoldXiCenteredRate q.1|)) ^ 2)
        atTop (𝓝 (((1 : ℝ) - 0) ^ 2)) :=
    (tendsto_const_nhds.sub hpow).pow 2
  rw [show (fun n : ℕ => Real.log (nthPrimeSubtype n : ℝ) *
      thetaPhysicalEndpointNormalizedHalfDensity (nthPrimeSubtype n) q ^ 2) =
      fun n : ℕ =>
        (1 - (nthPrimeSubtype n : ℝ) ^
          (-|primeDepthBVWoldXiCenteredRate q.1|)) ^ 2 by
    funext n
    exact log_mul_thetaPhysicalEndpointNormalizedHalfDensity_sq
      (nthPrimeSubtype n) q]
  simpa using hlimit

/-- At a neutral copy the logarithmic boundary trace is identically zero. -/
theorem tendsto_log_mul_thetaPhysicalEndpointNormalizedHalfDensity_sq_of_boundaryFlux_zero
    (q : XiZeroCopy) (hflux : thetaXiRankTwoBoundaryFlux q = 0) :
    Tendsto
      (fun n : ℕ => Real.log (nthPrimeSubtype n : ℝ) *
        thetaPhysicalEndpointNormalizedHalfDensity (nthPrimeSubtype n) q ^ 2)
      atTop (𝓝 0) := by
  rw [show (fun n : ℕ => Real.log (nthPrimeSubtype n : ℝ) *
      thetaPhysicalEndpointNormalizedHalfDensity (nthPrimeSubtype n) q ^ 2) =
      fun _ : ℕ => 0 by
    funext n
    rw [thetaPhysicalEndpointNormalizedHalfDensity,
      thetaMobiusPrimeNormalProfileHalfDensityAmplitude,
      (thetaMobiusPrimeNormalReflectionProfile_eq_zero_iff_boundaryFlux_zero
        (nthPrimeSubtype n) q).2 hflux]
    ring]
  exact tendsto_const_nhds

/-- The logarithmic boundary trace has the quantized value zero exactly on a neutral copy. -/
theorem tendsto_log_mul_thetaPhysicalEndpointNormalizedHalfDensity_sq_zero_iff_boundaryFlux_zero
    (q : XiZeroCopy) :
    Tendsto
      (fun n : ℕ => Real.log (nthPrimeSubtype n : ℝ) *
        thetaPhysicalEndpointNormalizedHalfDensity (nthPrimeSubtype n) q ^ 2)
      atTop (𝓝 0) ↔ thetaXiRankTwoBoundaryFlux q = 0 := by
  constructor
  · intro hzero
    by_contra hflux
    have hone :=
      tendsto_log_mul_thetaPhysicalEndpointNormalizedHalfDensity_sq_of_boundaryFlux_ne_zero
        q hflux
    have : (0 : ℝ) = 1 := tendsto_nhds_unique hzero hone
    norm_num at this
  · exact tendsto_log_mul_thetaPhysicalEndpointNormalizedHalfDensity_sq_of_boundaryFlux_zero q

/-- Dually, every nonneutral copy has quantized logarithmic boundary trace one. -/
theorem tendsto_log_mul_thetaPhysicalEndpointNormalizedHalfDensity_sq_one_iff_boundaryFlux_ne_zero
    (q : XiZeroCopy) :
    Tendsto
      (fun n : ℕ => Real.log (nthPrimeSubtype n : ℝ) *
        thetaPhysicalEndpointNormalizedHalfDensity (nthPrimeSubtype n) q ^ 2)
      atTop (𝓝 1) ↔ thetaXiRankTwoBoundaryFlux q ≠ 0 := by
  constructor
  · intro hone hflux
    have hzero :=
      tendsto_log_mul_thetaPhysicalEndpointNormalizedHalfDensity_sq_of_boundaryFlux_zero
        q hflux
    have : (1 : ℝ) = 0 := tendsto_nhds_unique hone hzero
    norm_num at this
  · exact tendsto_log_mul_thetaPhysicalEndpointNormalizedHalfDensity_sq_of_boundaryFlux_ne_zero q

theorem physicalPrimeEndpointWeight_le_one (p : Nat.Primes) :
    physicalPrimeEndpointWeight p ≤ 1 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hlog := Real.log_le_sub_one_of_pos hp
  rw [physicalPrimeEndpointWeight]
  apply (div_le_one hp).2
  linarith

/-- The normalized physical endpoint profile is square summable only on a neutral divisor copy. -/
theorem summable_sq_thetaPhysicalEndpointNormalizedHalfDensity_iff_boundaryFlux_zero
    (q : XiZeroCopy) :
    Summable (fun p : Nat.Primes =>
      thetaPhysicalEndpointNormalizedHalfDensity p q ^ 2) ↔
      thetaXiRankTwoBoundaryFlux q = 0 := by
  constructor
  · intro hphi
    have hhalf : Summable (fun p : Nat.Primes =>
        thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q ^ 2) := by
      apply Summable.of_nonneg_of_le
        (f := fun p : Nat.Primes =>
          thetaPhysicalEndpointNormalizedHalfDensity p q ^ 2)
      · exact fun p => sq_nonneg _
      · intro p
        rw [← physicalPrimeEndpointWeight_mul_normalizedHalfDensity_sq]
        have hweight0 := (physicalPrimeEndpointWeight_pos p).le
        have hweight1 := physicalPrimeEndpointWeight_le_one p
        have hsquare := sq_nonneg
          (thetaPhysicalEndpointNormalizedHalfDensity p q)
        nlinarith [mul_nonneg (sub_nonneg.mpr hweight1) hsquare]
      · exact hphi
    have henergy : Summable (fun p : Nat.Primes =>
        thetaMobiusPrimeNormalProfilePositiveGauge p q *
          thetaMobiusPrimeNormalReflectionProfile p q ^ 2) :=
      hhalf.congr (fun p =>
        thetaMobiusPrimeNormalProfileHalfDensityAmplitude_sq p q)
    have hnode :=
      (thetaXiReciprocalEigenvalue_sq_positiveReal_iff_summable_mobiusPrimeNormalProfileEnergy
        q).2 henergy
    exact (thetaXiReciprocalEigenvalue_sq_positiveReal_iff_boundaryFlux_zero q).1 hnode
  · intro hflux
    rw [show (fun p : Nat.Primes =>
        thetaPhysicalEndpointNormalizedHalfDensity p q ^ 2) =
      fun _ : Nat.Primes => 0 by
        funext p
        rw [thetaPhysicalEndpointNormalizedHalfDensity,
          thetaMobiusPrimeNormalProfileHalfDensityAmplitude,
          (thetaMobiusPrimeNormalReflectionProfile_eq_zero_iff_boundaryFlux_zero p q).2 hflux]
        ring]
    exact summable_zero

/-- Global ordinary `ℓ²` admission of the endpoint-normalized physical profile is equivalent to
RH, so it cannot serve as an unconditional construction step. -/
theorem all_summable_sq_thetaPhysicalEndpointNormalizedHalfDensity_iff_riemannHypothesis :
    (∀ q : XiZeroCopy, Summable (fun p : Nat.Primes =>
      thetaPhysicalEndpointNormalizedHalfDensity p q ^ 2)) ↔
      RiemannHypothesis := by
  rw [← thetaGreenBoundaryNeutral_iff_riemannHypothesis]
  exact forall_congr'
    summable_sq_thetaPhysicalEndpointNormalizedHalfDensity_iff_boundaryFlux_zero

/-- RH is exactly global vanishing of the quantized physical-endpoint logarithmic boundary
trace. -/
theorem all_tendsto_log_mul_thetaPhysicalEndpointNormalizedHalfDensity_sq_zero_iff_riemannHypothesis :
    (∀ q : XiZeroCopy,
      Tendsto
        (fun n : ℕ => Real.log (nthPrimeSubtype n : ℝ) *
          thetaPhysicalEndpointNormalizedHalfDensity (nthPrimeSubtype n) q ^ 2)
        atTop (𝓝 0)) ↔ RiemannHypothesis := by
  rw [← thetaGreenBoundaryNeutral_iff_riemannHypothesis]
  exact forall_congr'
    tendsto_log_mul_thetaPhysicalEndpointNormalizedHalfDensity_sq_zero_iff_boundaryFlux_zero

end

end RHTower.HedenmalmThetaSource
