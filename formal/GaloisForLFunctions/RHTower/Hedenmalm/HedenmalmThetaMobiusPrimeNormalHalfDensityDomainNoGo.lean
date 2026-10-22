import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusPrimeNormalProfileBridge
import GaloisForLFunctions.RHTower.MobiusThetaAdaptivePrimeNormalCodiagonal

/-!
# Möbius prime-normal half-density domain no-go

The exact physical profile bridge has a canonical half-density normalization.  It is the signed
difference between Route N's universal `p⁻¹ᐟ²` amplitude and its twisted amplitude.  Its square is
the Route P Hellinger defect.

This exposes a sharp domain obstruction.  The adaptive prime-normal codiagonal is closed and
bounded below on `ℓ¹` prime coefficients, but the physical half-density belongs to that domain
exactly on a neutral divisor copy.  Thus transporting this vector through the existing `ℓ¹`
codiagonal cannot prove neutrality: its domain admission is already equivalent to the desired
pointwise Route P conclusion.  A surviving source law must extend to the weak-`ℓ²` boundary class
or act quadratically on finite packets before completion.
-/

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Canonical signed half-density of the literal Möbius prime-normal reflection profile. -/
def thetaMobiusPrimeNormalProfileHalfDensityAmplitude
    (p : Nat.Primes) (q : XiZeroCopy) : ℝ :=
  routeNGammaSewnUniversalCriticalChannelAmplitude p /
      (1 + (p : ℝ) ^ |primeDepthBVWoldXiCenteredRate q.1|) *
    thetaMobiusPrimeNormalReflectionProfile p q

/-- The physical half-density is the oriented universal-minus-twisted channel gap. -/
theorem thetaMobiusPrimeNormalProfileHalfDensityAmplitude_eq_channelGap
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q =
      if 0 ≤ primeDepthBVWoldXiCenteredRate q.1 then
        routeNGammaSewnUniversalCriticalChannelAmplitude p -
          routeNGammaSewnTwistedCriticalChannelAmplitude
            (primeDepthBVWoldXiCenteredRate q.1) p
      else
        -(routeNGammaSewnUniversalCriticalChannelAmplitude p -
          routeNGammaSewnTwistedCriticalChannelAmplitude
            (primeDepthBVWoldXiCenteredRate q.1) p) := by
  let a : ℝ := primeDepthBVWoldXiCenteredRate q.1
  let P : ℝ := p
  have hP : 0 < P := by
    dsimp [P]
    exact_mod_cast p.2.pos
  have hPa : 0 < P ^ a := Real.rpow_pos_of_pos hP _
  have hPna : 0 < P ^ (-a) := Real.rpow_pos_of_pos hP _
  rw [thetaMobiusPrimeNormalProfileHalfDensityAmplitude,
    thetaMobiusPrimeNormalReflectionProfile_eq,
    routeNGammaSewnUniversalCriticalChannelAmplitude,
    routeNGammaSewnTwistedCriticalChannelAmplitude]
  change P ^ (-(1 / 2 : ℝ)) / (1 + P ^ |a|) *
      (P ^ a - P ^ (-a)) = if 0 ≤ a then
        P ^ (-(1 / 2 : ℝ)) - P ^ (-(1 / 2 : ℝ) - |a|)
      else -(P ^ (-(1 / 2 : ℝ)) - P ^ (-(1 / 2 : ℝ) - |a|))
  by_cases ha : 0 ≤ a
  · rw [if_pos ha, abs_of_nonneg ha]
    rw [show P ^ (-(1 / 2 : ℝ) - a) =
        P ^ (-(1 / 2 : ℝ)) * P ^ (-a) by
      rw [← Real.rpow_add hP]
      ring_nf]
    have hprod : P ^ a * P ^ (-a) = 1 := by
      rw [← Real.rpow_add hP]
      norm_num
    rw [Real.rpow_neg hP.le]
    field_simp [hPa.ne']
    nlinarith [hprod]
  · have ha' : a ≤ 0 := le_of_not_ge ha
    rw [if_neg ha, abs_of_nonpos ha']
    rw [show P ^ (-(1 / 2 : ℝ) - -a) =
        P ^ (-(1 / 2 : ℝ)) * P ^ a by
      rw [← Real.rpow_add hP]
      ring_nf]
    have hprod : P ^ a * P ^ (-a) = 1 := by
      rw [← Real.rpow_add hP]
      norm_num
    rw [Real.rpow_neg hP.le]
    field_simp [hPa.ne', hPna.ne']
    nlinarith [hprod]

/-- Squared physical half-density is exactly Route P's local source-profile energy. -/
theorem thetaMobiusPrimeNormalProfileHalfDensityAmplitude_sq
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q ^ 2 =
      thetaMobiusPrimeNormalProfilePositiveGauge p q *
        thetaMobiusPrimeNormalReflectionProfile p q ^ 2 := by
  rw [← primeValuationHellingerGap_eq_mobiusPrimeNormalProfile_sq,
    primeValuationHellingerGap_neg_abs_eq_routeNCriticalAmplitudeGap,
    thetaMobiusPrimeNormalProfileHalfDensityAmplitude_eq_channelGap]
  split <;> ring

theorem abs_thetaMobiusPrimeNormalProfileHalfDensityAmplitude_le_one
    (p : Nat.Primes) (q : XiZeroCopy) :
    |thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q| ≤ 1 := by
  let a : ℝ := primeDepthBVWoldXiCenteredRate q.1
  let u : ℝ := routeNGammaSewnUniversalCriticalChannelAmplitude p
  let v : ℝ := routeNGammaSewnTwistedCriticalChannelAmplitude a p
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast p.2.one_lt.le
  have hu0 : 0 < u := Real.rpow_pos_of_pos hp0 _
  have hu1 : u ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hp1 (by norm_num)
  have hc1 : (p : ℝ) ^ (-|a|) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hp1 (neg_nonpos.mpr (abs_nonneg a))
  have hv0 : 0 < v := Real.rpow_pos_of_pos hp0 _
  have hvu : v ≤ u := by
    change routeNGammaSewnTwistedCriticalChannelAmplitude a p ≤
      routeNGammaSewnUniversalCriticalChannelAmplitude p
    rw [routeNGammaSewnTwistedCriticalChannelAmplitude_eq_universal_mul_sqrtCocycle]
    exact mul_le_of_le_one_right hu0.le hc1
  have hgap0 : 0 ≤ u - v := sub_nonneg.mpr hvu
  have hgap1 : u - v ≤ 1 := (sub_le_self u hv0.le).trans hu1
  rw [thetaMobiusPrimeNormalProfileHalfDensityAmplitude_eq_channelGap]
  change |if 0 ≤ a then u - v else -(u - v)| ≤ 1
  by_cases ha : 0 ≤ a
  · rw [if_pos ha, abs_of_nonneg hgap0]
    exact hgap1
  · rw [if_neg ha, abs_neg, abs_of_nonneg hgap0]
    exact hgap1

/-- Absolute summability of the physical half-density is already same-fibre neutrality. -/
theorem summable_abs_thetaMobiusPrimeNormalProfileHalfDensityAmplitude_iff_boundaryFlux_zero
    (q : XiZeroCopy) :
    Summable (fun p : Nat.Primes =>
      |thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q|) ↔
      thetaXiRankTwoBoundaryFlux q = 0 := by
  constructor
  · intro habs
    have hsq : Summable (fun p : Nat.Primes =>
        thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q ^ 2) :=
      Summable.of_nonneg_of_le
        (fun p => sq_nonneg _)
        (fun p => by
          have h0 := abs_nonneg
            (thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q)
          have h1 := abs_thetaMobiusPrimeNormalProfileHalfDensityAmplitude_le_one p q
          rw [← sq_abs]
          nlinarith)
        habs
    have henergy : Summable (fun p : Nat.Primes =>
        thetaMobiusPrimeNormalProfilePositiveGauge p q *
          thetaMobiusPrimeNormalReflectionProfile p q ^ 2) :=
      hsq.congr (fun p => thetaMobiusPrimeNormalProfileHalfDensityAmplitude_sq p q)
    have hnode :=
      (thetaXiReciprocalEigenvalue_sq_positiveReal_iff_summable_mobiusPrimeNormalProfileEnergy
        q).2 henergy
    exact (thetaXiReciprocalEigenvalue_sq_positiveReal_iff_boundaryFlux_zero q).1 hnode
  · intro hflux
    rw [show (fun p : Nat.Primes =>
        |thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q|) =
        fun _ : Nat.Primes => 0 by
      funext p
      rw [thetaMobiusPrimeNormalProfileHalfDensityAmplitude,
        (thetaMobiusPrimeNormalReflectionProfile_eq_zero_iff_boundaryFlux_zero p q).2 hflux]
      simp]
    exact summable_zero

/-- Exact domain classification for the existing adaptive prime-normal `ℓ¹` codiagonal. -/
theorem exists_adaptivePrimeL1_physicalHalfDensity_iff_boundaryFlux_zero
    (q : XiZeroCopy) :
    (∃ x : AdaptivePrimeL1, ∀ p : Nat.Primes,
      x p = (thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q : ℂ)) ↔
      thetaXiRankTwoBoundaryFlux q = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    have hxsum : Summable (fun p : Nat.Primes => ‖x p‖) := by
      simpa using
        (lp.hasSum_norm (by norm_num : 0 < (1 : ENNReal).toReal) x).summable
    apply (summable_abs_thetaMobiusPrimeNormalProfileHalfDensityAmplitude_iff_boundaryFlux_zero
      q).1
    exact hxsum.congr (fun p => by rw [hx p]; simp [Real.norm_eq_abs])
  · intro hflux
    refine ⟨0, fun p => ?_⟩
    change (0 : ℂ) = (thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q : ℂ)
    rw [thetaMobiusPrimeNormalProfileHalfDensityAmplitude,
      (thetaMobiusPrimeNormalReflectionProfile_eq_zero_iff_boundaryFlux_zero p q).2 hflux]
    norm_num

/-- Global `ℓ¹` admission of the literal physical half-density is itself equivalent to RH. -/
theorem all_exists_adaptivePrimeL1_physicalHalfDensity_iff_riemannHypothesis :
    (∀ q : XiZeroCopy, ∃ x : AdaptivePrimeL1, ∀ p : Nat.Primes,
      x p = (thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q : ℂ)) ↔
      RiemannHypothesis := by
  rw [← thetaGreenBoundaryNeutral_iff_riemannHypothesis]
  exact forall_congr' exists_adaptivePrimeL1_physicalHalfDensity_iff_boundaryFlux_zero

end

end RHTower.HedenmalmThetaSource
