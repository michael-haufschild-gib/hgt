import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmStokesCompletedResponseCovariantRenormalization
import GaloisForLFunctions.RHTower.PrimeArchPolarSeamRemoval

/-!
# Oriented first-trace quantized jump and polar cancellation

P-G141's covariant Stokes energy is finite because it contains two centered-depth factors.
Before the final scalar multiplication, the label-faithful oriented current has prime term

`8 t log(p) p^(-1-2|t|)`.

It is summable for every fixed `t`, including `t = 0`, and changes sign under reflection.  But its
all-prime total does not approach its pointwise value at the neutral wall: the two one-sided limits
are `4` and `-4`.  Thus the missing orientation is a quantized residue jump, not a continuous Ward
vector waiting to be set to zero.

The completed prime--Gamma current supplies the exact opposite polar jump.  Their sum extends to
zero at the wall, while P-G141's positive energy is the oriented current multiplied by `t`.
Consequently the two prior finite-part branches are shadows of one residue law: scalarization
kills orientation by multiplying the jump by depth; polar completion preserves orientation by a
signed cancellation.  Neither operation supplies an unconditional vanishing theorem away from the
wall.

No RH premise, numerical estimate, or added axiom enters.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Label-faithful oriented valuation-one term before P-G141's last depth multiplication. -/
def gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm
    (t : ℝ) (p : Nat.Primes) : ℝ :=
  8 * t * xiMassPrimeSquareEulerWeight |t| p

/-- All-prime oriented first-trace current. -/
def gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent (t : ℝ) : ℝ :=
  ∑' p : Nat.Primes,
    gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm t p

/-- Every fibre has an ordinary `ℓ¹` oriented current.  At the wall this is termwise zero. -/
theorem summable_gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm
    (t : ℝ) :
    Summable (gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm t) := by
  by_cases ht : t = 0
  · subst t
    convert (summable_zero : Summable (fun _p : Nat.Primes => (0 : ℝ))) using 1
    funext p
    simp [gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm]
  · exact ((summable_xiMassPrimeSquareEulerWeight (abs_pos.mpr ht)).mul_left
      (8 * t)).congr (fun p => by
        simp [gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm])

/-- The total is depth times the previously formalized prime Hardy--Green energy. -/
theorem gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_eq
    (t : ℝ) :
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent t =
      t * HedenmalmThetaSource.thetaPhysicalEndpointPrimeHardyGreenEnergy |t| := by
  rw [gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent,
    HedenmalmThetaSource.thetaPhysicalEndpointPrimeHardyGreenEnergy]
  calc
    (∑' p : Nat.Primes,
        gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm t p) =
        ∑' p : Nat.Primes, t * (8 * xiMassPrimeSquareEulerWeight |t| p) := by
          apply tsum_congr
          intro p
          rw [gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm]
          ring
    _ = t * ∑' p : Nat.Primes, 8 * xiMassPrimeSquareEulerWeight |t| p :=
      tsum_mul_left
    _ = t * (8 * ∑' p : Nat.Primes, xiMassPrimeSquareEulerWeight |t| p) := by
      rw [tsum_mul_left]

/-- The horizontal sign convention times absolute depth is the signed centered rate, including at
the neutral wall. -/
theorem HedenmalmThetaSource.thetaWardHorizontalOrientation_mul_abs_centeredRate
    (q : XiZeroCopy) :
    thetaWardHorizontalOrientation q *
        |primeDepthBVWoldXiCenteredRate q.1| =
      primeDepthBVWoldXiCenteredRate q.1 := by
  rw [thetaWardHorizontalOrientation]
  split_ifs with h
  · simp [abs_of_nonneg h]
  · rw [abs_of_neg (lt_of_not_ge h)]
    ring

/-- The moving-horizon connection itself is signed; orientation is lost only after squaring. -/
theorem HedenmalmThetaSource.thetaMovingHorizonConnection_eq_centeredRate_mul
    (q : XiZeroCopy) (L : ℝ) :
    thetaMovingHorizonConnection (thetaWardContinuousHalfDensityProfile q) L =
      primeDepthBVWoldXiCenteredRate q.1 *
        Real.exp (-(1 / 2 + |primeDepthBVWoldXiCenteredRate q.1|) * L) := by
  rw [thetaMovingHorizonConnection_wardContinuousHalfDensityProfile,
    thetaWardHorizontalOrientation_mul_abs_centeredRate]

/-- Primewise form: the oriented first trace pairs the signed connection with the unsigned stable
Hardy channel before positive scalarization. -/
theorem gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm_eq_connection_pairing
    (q : XiZeroCopy) (p : Nat.Primes) :
    gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm
        (primeDepthBVWoldXiCenteredRate q.1) p =
      8 * Real.log (p : ℝ) *
        HedenmalmThetaSource.thetaMovingHorizonConnection
          (HedenmalmThetaSource.thetaWardContinuousHalfDensityProfile q)
          (Real.log (p : ℝ)) *
        routeNGammaSewnTwistedCriticalChannelAmplitude
          (primeDepthBVWoldXiCenteredRate q.1) p := by
  rw [HedenmalmThetaSource.thetaMovingHorizonConnection_wardContinuousHalfDensityProfile_prime,
    ← mul_assoc,
    HedenmalmThetaSource.thetaWardHorizontalOrientation_mul_abs_centeredRate,
    gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm,
    xiMassPrimeSquareEulerWeight_eq]
  have hamp :
      routeNGammaSewnTwistedCriticalChannelAmplitude
          (primeDepthBVWoldXiCenteredRate q.1) p *
        routeNGammaSewnTwistedCriticalChannelAmplitude
          (primeDepthBVWoldXiCenteredRate q.1) p =
        (p : ℝ) ^ (-(1 + 2 * |primeDepthBVWoldXiCenteredRate q.1|)) := by
    rw [← pow_two, routeNGammaSewnTwistedCriticalChannelAmplitude_sq,
      routeNGammaSewnTwistedCriticalChannelMass]
    congr 1
    ring
  rw [← hamp]
  ring

/-- P-G141's positive covariant moment is exactly signed depth times the oriented current term. -/
theorem gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment_eq_centeredRate_mul_oriented
    (q : XiZeroCopy) (p : Nat.Primes) :
    gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment
        |primeDepthBVWoldXiCenteredRate q.1| p =
      primeDepthBVWoldXiCenteredRate q.1 *
        gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm
          (primeDepthBVWoldXiCenteredRate q.1) p := by
  let t := primeDepthBVWoldXiCenteredRate q.1
  rw [gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment_eq
    |t| (abs_nonneg t) p,
    gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm,
    xiMassPrimeSquareEulerWeight_eq]
  dsimp only [t]
  rw [sq_abs]
  ring

/-- The whole P-G141 energy is signed centered depth times the oriented total current. -/
theorem tsum_gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment_eq_centeredRate_mul_oriented
    (q : XiZeroCopy) :
    (∑' p : Nat.Primes,
      gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment
        |primeDepthBVWoldXiCenteredRate q.1| p) =
      primeDepthBVWoldXiCenteredRate q.1 *
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
          (primeDepthBVWoldXiCenteredRate q.1) := by
  rw [gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent, ← tsum_mul_left]
  exact tsum_congr
    (gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment_eq_centeredRate_mul_oriented q)

/-- Reflection reverses the oriented current term coefficient by coefficient. -/
@[simp] theorem gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm_neg
    (t : ℝ) (p : Nat.Primes) :
    gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm (-t) p =
      -gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm t p := by
  simp [gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm]

/-- Reflection reverses the all-prime oriented current. -/
@[simp] theorem gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_neg
    (t : ℝ) :
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent (-t) =
      -gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent t := by
  rw [gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent,
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent, ← tsum_neg]
  exact tsum_congr (gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm_neg t)

/-- Right-hand quantization: termwise-zero wall is approached by total oriented charge `4`. -/
theorem tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsGT_zero :
    Tendsto gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
      (𝓝[>] (0 : ℝ)) (𝓝 4) := by
  refine HedenmalmThetaSource.tendsto_depth_mul_thetaPhysicalEndpointPrimeHardyGreenEnergy.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  rw [gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_eq, abs_of_pos ht]

/-- Left-hand quantization: reflection gives the opposite charge `-4`. -/
theorem tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsLT_zero :
    Tendsto gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
      (𝓝[<] (0 : ℝ)) (𝓝 (-4)) := by
  have hcomp :=
    tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsGT_zero.comp
      (show Tendsto (fun t : ℝ => -t) (𝓝[<] 0) (𝓝[>] 0) by
        simpa using (tendsto_neg_nhdsLT (a := (0 : ℝ))))
  have hneg := hcomp.neg
  refine hneg.congr' ?_
  filter_upwards with t
  simp

/-- The wall value is zero because the oriented family is termwise zero there. -/
@[simp] theorem gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_zero :
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent 0 = 0 := by
  simp [gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent,
    gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm]

/-- **Quantized-jump wall.** Fibrewise `ℓ¹` admission does not give continuity through neutral
depth. -/
theorem not_continuousAt_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_zero :
    ¬ContinuousAt gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent 0 := by
  intro hcontinuous
  have hzero : Tendsto gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  have heq : (0 : ℝ) = 4 := tendsto_nhds_unique hzero
    tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsGT_zero
  norm_num at heq

/-- The oriented total is faithful: it vanishes exactly at neutral depth. -/
theorem gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_eq_zero_iff
    (t : ℝ) :
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent t = 0 ↔ t = 0 := by
  constructor
  · intro hcurrent
    by_contra ht
    have hd : 0 < |t| := abs_pos.mpr ht
    have hsum : Summable (xiMassPrimeSquareEulerWeight |t|) :=
      summable_xiMassPrimeSquareEulerWeight hd
    have hprime : 0 < ∑' p : Nat.Primes, xiMassPrimeSquareEulerWeight |t| p := by
      refine hsum.tsum_pos (fun p => ?_) (⟨2, Nat.prime_two⟩ : Nat.Primes) ?_
      · rw [xiMassPrimeSquareEulerWeight_eq]
        positivity
      · rw [xiMassPrimeSquareEulerWeight_eq]
        positivity
    have henergy :
        0 < HedenmalmThetaSource.thetaPhysicalEndpointPrimeHardyGreenEnergy |t| := by
      rw [HedenmalmThetaSource.thetaPhysicalEndpointPrimeHardyGreenEnergy]
      positivity
    rw [gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_eq] at hcurrent
    exact (mul_ne_zero ht henergy.ne') hcurrent
  · rintro rfl
    exact gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_zero

/-- Actual multiplicity-resolved oriented current. -/
def gammaSewnMobiusApertureStokesOrientedFirstTraceCurrentAt
    (q : XiZeroCopy) : ℝ :=
  gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
    (primeDepthBVWoldXiCenteredRate q.1)

/-- Functional-equation reflection reverses the actual oriented current. -/
@[simp] theorem gammaSewnMobiusApertureStokesOrientedFirstTraceCurrentAt_lineConj
    (q : XiZeroCopy) :
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrentAt
        (xiZeroCopyLineConjEquiv q) =
      -gammaSewnMobiusApertureStokesOrientedFirstTraceCurrentAt q := by
  rw [gammaSewnMobiusApertureStokesOrientedFirstTraceCurrentAt,
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrentAt,
    HedenmalmThetaSource.primeDepthBVWoldXiCenteredRate_lineConj,
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_neg]

/-- Vanishing of actual oriented current is exactly theta boundary neutrality. -/
theorem gammaSewnMobiusApertureStokesOrientedFirstTraceCurrentAt_eq_zero_iff
    (q : XiZeroCopy) :
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrentAt q = 0 ↔
      thetaXiRankTwoBoundaryFlux q = 0 := by
  rw [gammaSewnMobiusApertureStokesOrientedFirstTraceCurrentAt,
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_eq_zero_iff,
    HedenmalmThetaSource.thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate]
  have hcoefficient :
      -(HedenmalmThetaSource.thetaSource.mass * thetaXiRootEnergy q) ≠ 0 :=
    neg_ne_zero.mpr
      (mul_pos HedenmalmThetaSource.thetaSource.mass_pos
        (thetaXiRootEnergy_pos q)).ne'
  constructor
  · intro hrate
    rw [hrate, mul_zero]
  · intro hflux
    exact (mul_eq_zero.mp hflux).resolve_left hcoefficient

/-- Global vanishing of the oriented current remains exactly RH; quantization identifies the
missing producer but does not provide it. -/
theorem all_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrentAt_eq_zero_iff_rh :
    (∀ q : XiZeroCopy,
      gammaSewnMobiusApertureStokesOrientedFirstTraceCurrentAt q = 0) ↔
      RiemannHypothesis := by
  rw [← HedenmalmThetaSource.thetaGreenBoundaryNeutral_iff_riemannHypothesis]
  exact forall_congr'
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrentAt_eq_zero_iff

/-- Completed signed current sampled on the stable right ray. -/
def gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent
    (t : ℝ) : ℝ :=
  8 * t *
    (completedPrimeGammaFlux (((1 + 2 * |t| : ℝ) : ℂ))).re

/-- Explicit higher-valuation plus archimedean countercurrent. -/
def gammaSewnMobiusApertureStokesOrientedPolarCountercurrent
    (t : ℝ) : ℝ :=
  8 * t *
    (xiPrimeLogHigherValuation (((1 + 2 * |t| : ℝ) : ℂ)) -
      logDeriv archFactor (((1 + 2 * |t| : ℝ) : ℂ))).re

/-- Exact completed-current decomposition away from the wall. -/
theorem gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent_eq_firstTrace_add_counter
    (t : ℝ) (ht : t ≠ 0) :
    gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent t =
      gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent t +
        gammaSewnMobiusApertureStokesOrientedPolarCountercurrent t := by
  let d := |t|
  have hd : 0 < d := abs_pos.mpr ht
  have hs : (1 : ℝ) < 1 + 2 * d := by linarith
  have hcontinuation :
      xiPrimeLogDirichletContinuation (((1 + 2 * d : ℝ) : ℂ)) =
        xiPrimeLogDirichlet (((1 + 2 * d : ℝ) : ℂ)) :=
    xiPrimeLogDirichletContinuation_eq (by simpa using hs)
  rw [gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent,
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_eq,
    HedenmalmThetaSource.thetaPhysicalEndpointPrimeHardyGreenEnergy_eq_primeLogDirichlet d hd,
    gammaSewnMobiusApertureStokesOrientedPolarCountercurrent,
    completedPrimeGammaFlux_eq_firstTrace_add_regular,
    squarefreeFirstTraceContinuedCurrent,
    hcontinuation]
  dsimp only [d]
  simp only [Complex.add_re, Complex.sub_re]
  ring

/-- Completed prime--Gamma current has zero scaled wall residue. -/
theorem tendsto_gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent_nhdsGT_zero :
    Tendsto gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hbase : Tendsto (fun t : ℝ => t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have hmapR : Tendsto (fun t : ℝ => 1 + 2 * t)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using tendsto_const_nhds.add (hbase.const_mul 2)
  have hmap : Tendsto (fun t : ℝ => ((1 + 2 * t : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hmapR
  have hseam : Tendsto (fun t : ℝ =>
      (seamFluxCochain (((1 + 2 * t : ℝ) : ℂ))).re)
      (𝓝[>] (0 : ℝ)) (𝓝 (seamFluxCochain 1).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp
      (analyticAt_seamFluxCochain_one.continuousAt.tendsto.comp hmap)
  have hzero : Tendsto (fun t : ℝ =>
      8 * t * (seamFluxCochain (((1 + 2 * t : ℝ) : ℂ))).re)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (hbase.const_mul 8).mul hseam
  refine hzero.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have hs : (1 : ℝ) < 1 + 2 * t := by linarith
  rw [gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent,
    abs_of_pos ht, completedPrimeGammaFlux,
    ← seamFluxCochain_eq_prime_add_archimedean_of_one_lt_re (by simpa using hs)]

/-- The completed current is reflection-odd as a function of signed depth. -/
@[simp] theorem gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent_neg
    (t : ℝ) :
    gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent (-t) =
      -gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent t := by
  simp [gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent]

/-- The explicit polar countercurrent is also reflection-odd. -/
@[simp] theorem gammaSewnMobiusApertureStokesOrientedPolarCountercurrent_neg
    (t : ℝ) :
    gammaSewnMobiusApertureStokesOrientedPolarCountercurrent (-t) =
      -gammaSewnMobiusApertureStokesOrientedPolarCountercurrent t := by
  simp [gammaSewnMobiusApertureStokesOrientedPolarCountercurrent]

/-- Polar/Gamma countercurrent carries exactly the opposite right-hand residue. -/
theorem tendsto_gammaSewnMobiusApertureStokesOrientedPolarCountercurrent_nhdsGT_zero :
    Tendsto gammaSewnMobiusApertureStokesOrientedPolarCountercurrent
      (𝓝[>] (0 : ℝ)) (𝓝 (-4)) := by
  have hsub : Tendsto (fun t : ℝ =>
      gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent t -
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent t)
      (𝓝[>] (0 : ℝ)) (𝓝 (-4)) := by
    simpa using
    tendsto_gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent_nhdsGT_zero.sub
      tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsGT_zero
  refine hsub.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have ht0 : t ≠ 0 := ht.ne'
  rw [gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent_eq_firstTrace_add_counter
    t ht0]
  ring

/-- The countercurrent has opposite left residue `4`. -/
theorem tendsto_gammaSewnMobiusApertureStokesOrientedPolarCountercurrent_nhdsLT_zero :
    Tendsto gammaSewnMobiusApertureStokesOrientedPolarCountercurrent
      (𝓝[<] (0 : ℝ)) (𝓝 4) := by
  have hcomp :=
    tendsto_gammaSewnMobiusApertureStokesOrientedPolarCountercurrent_nhdsGT_zero.comp
      (show Tendsto (fun t : ℝ => -t) (𝓝[<] 0) (𝓝[>] 0) by
        simpa using (tendsto_neg_nhdsLT (a := (0 : ℝ))))
  have hneg : Tendsto (fun t : ℝ =>
      -gammaSewnMobiusApertureStokesOrientedPolarCountercurrent (-t))
      (𝓝[<] (0 : ℝ)) (𝓝 4) := by
    simpa using hcomp.neg
  refine hneg.congr' ?_
  filter_upwards with t
  simp

/-- At the neutral wall the completed current is also termwise scaled to zero. -/
@[simp] theorem gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent_zero :
    gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent 0 = 0 := by
  simp [gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent]

/-- The polar completion removes the jump continuously from the right. -/
theorem continuousWithinAt_gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent_zero :
    ContinuousWithinAt gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent
      (Set.Ioi 0) 0 := by
  change Tendsto gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent
    (𝓝[>] (0 : ℝ))
    (𝓝 (gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent 0))
  simpa using
    tendsto_gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent_nhdsGT_zero

/-- Polar cancellation removes the jump on both sides: completed oriented current is continuous
at neutral depth. -/
theorem continuousAt_gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent_zero :
    ContinuousAt gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent 0 := by
  have hbase : Tendsto (fun t : ℝ => t) (𝓝 (0 : ℝ)) (𝓝 0) := tendsto_id
  have habs : Tendsto (fun t : ℝ => |t|) (𝓝 (0 : ℝ)) (𝓝 0) := by
    have habs0 : ContinuousAt (fun t : ℝ => |t|) 0 := continuous_abs.continuousAt
    simpa only [abs_zero] using habs0.tendsto
  have hmapR : Tendsto (fun t : ℝ => 1 + 2 * |t|)
      (𝓝 (0 : ℝ)) (𝓝 1) := by
    simpa using tendsto_const_nhds.add (habs.const_mul 2)
  have hmap : Tendsto (fun t : ℝ => ((1 + 2 * |t| : ℝ) : ℂ))
      (𝓝 (0 : ℝ)) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hmapR
  have hseam : Tendsto (fun t : ℝ =>
      (seamFluxCochain (((1 + 2 * |t| : ℝ) : ℂ))).re)
      (𝓝 (0 : ℝ)) (𝓝 (seamFluxCochain 1).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp
      (analyticAt_seamFluxCochain_one.continuousAt.tendsto.comp hmap)
  have hzero : Tendsto (fun t : ℝ =>
      8 * t * (seamFluxCochain (((1 + 2 * |t| : ℝ) : ℂ))).re)
      (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa using (hbase.const_mul 8).mul hseam
  change Tendsto gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent
    (𝓝 (0 : ℝ))
    (𝓝 (gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent 0))
  rw [gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent_zero]
  refine hzero.congr' ?_
  filter_upwards with t
  by_cases ht : t = 0
  · subst t
    simp
  · have hd : 0 < |t| := abs_pos.mpr ht
    have hs : (1 : ℝ) < 1 + 2 * |t| := by linarith
    rw [gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent,
      completedPrimeGammaFlux,
      ← seamFluxCochain_eq_prime_add_archimedean_of_one_lt_re (by simpa using hs)]

end

end RHTower
