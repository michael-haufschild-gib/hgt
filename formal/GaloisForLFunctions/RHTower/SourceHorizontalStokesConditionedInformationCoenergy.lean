import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesReflectedCompactCarrier
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaRoutePInformationWoldGaussVirialBridge
import GaloisForLFunctions.HTGeometry.HyperbolicBounds

/-!
# Source-horizontal Stokes-conditioned information coenergy

The unconditioned Route-P geometric information virial diverges at every positive horizontal
depth.  The source-native reflected Stokes carrier supplies a coefficient-faithful inverse-gap
weight on the same prime-power label.  At the functional-equation complementary coordinate
`t=(1-s)/2`, their product has the exact two-clock majorant

`4(1-s) p⁻² (p⁻ˢ)^(2e) / (e+1)²`.

Thus one reflected source subtraction converts the divergent information observable into a
strictly positive, absolutely summable coenergy without averaging prime labels or valuation
multiplicity.  The outer `p⁻²` exponent is independent of horizontal position `s`.

This theorem is unconditional and source-pure.  It does not identify the coenergy with a completed
prime--Gamma seam invariant and does not prove RH.
-/

open Real Set Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower.HedenmalmThetaSource

/-- Elementary exponential upper bound for the information holonomy virial on the positive ray. -/
theorem sourceHorizontalHolonomyVirial_le_mul_exp {u : ℝ} (hu : 0 ≤ u) :
    sourceHorizontalHolonomyVirial u ≤ u * Real.exp u := by
  rw [sourceHorizontalHolonomyVirial]
  calc
    u * Real.cosh u - Real.sinh u ≤ u * Real.cosh u := by
      have hs : 0 ≤ Real.sinh u := Real.sinh_nonneg_iff.mpr hu
      linarith
    _ ≤ u * Real.exp u := by
      exact mul_le_mul_of_nonneg_left
        (HTGeometry.cosh_le_exp_of_nonneg hu) hu

/-- Exact source formula for the reflected Stokes weight.  The denominator exposes the two
valuation clocks and the prime-log clock which the information virial later cancels. -/
theorem gammaSewnMobiusApertureStokesReflectedWeight_eq_source
    {s : ℝ} (hs : 0 < s) (p : Nat.Primes) (e : ℕ) :
    RHTower.gammaSewnMobiusApertureStokesReflectedWeight s (p, e) =
      RHTower.gammaSewnMobiusValuationContractionMultiplier s p ^ 2 *
          (RHTower.xiTransversePrimeApertureDiskNode 1 p /
            (1 + RHTower.xiTransversePrimeApertureDiskNode 1 p)) ^ 2 *
          (1 - RHTower.xiMobiusContinuousApertureDiskNode s p) ^ 2 *
          RHTower.xiMobiusContinuousApertureDiskNode s p ^ e /
        (((e + 1 : ℕ) : ℝ) ^ 2 * Real.log (p : ℝ) *
          RHTower.xiMobiusContinuousApertureDiskNode s p) := by
  have hc : RHTower.gammaSewnMobiusValuationContractionMultiplier s p ≠ 0 :=
    (RHTower.gammaSewnMobiusValuationContractionMultiplier_pos s p).ne'
  have hq0 : 0 < RHTower.xiTransversePrimeApertureDiskNode 1 p :=
    RHTower.xiTransversePrimeApertureDiskNode_pos 1 p
  have hq : RHTower.xiTransversePrimeApertureDiskNode 1 p ≠ 0 := hq0.ne'
  have hqden : 1 + RHTower.xiTransversePrimeApertureDiskNode 1 p ≠ 0 := by
    linarith
  have hr : RHTower.xiMobiusContinuousApertureDiskNode s p ≠ 0 :=
    (RHTower.xiMobiusContinuousApertureDiskNode_pos s p).ne'
  have hr1 : 1 - RHTower.xiMobiusContinuousApertureDiskNode s p ≠ 0 :=
    sub_ne_zero.mpr
      (RHTower.xiMobiusContinuousApertureDiskNode_lt_one hs p).ne'
  have hL : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.2.one_lt)).ne'
  have hk : (((e + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [RHTower.gammaSewnMobiusApertureStokesReflectedWeight,
    RHTower.gammaSewnMobiusApertureStokesDualFeatureCoefficient,
    RHTower.gammaSewnMobiusApertureStokesGap,
    RHTower.gammaSewnMobiusApertureStokesInverseTilt,
    RHTower.gammaSewnMobiusContinuousApertureFeature,
    RHTower.xiMobiusPrimeSchurContinuousForwardDifference_eq_geometric]
  field_simp [hc, hq, hqden, hr, hr1, hL, hk]
  push_cast
  ring

/-- The exact reflected Stokes weight is bounded by its two-clock source monomial. -/
theorem gammaSewnMobiusApertureStokesReflectedWeight_le_twoClock
    {s : ℝ} (hs : 0 < s) (p : Nat.Primes) (e : ℕ) :
    RHTower.gammaSewnMobiusApertureStokesReflectedWeight s (p, e) ≤
      RHTower.xiTransversePrimeApertureDiskNode 1 p ^ 2 *
          RHTower.xiMobiusContinuousApertureDiskNode s p ^ e /
        (((e + 1 : ℕ) : ℝ) ^ 2 * Real.log (p : ℝ) *
          RHTower.xiMobiusContinuousApertureDiskNode s p) := by
  let c := RHTower.gammaSewnMobiusValuationContractionMultiplier s p
  let q := RHTower.xiTransversePrimeApertureDiskNode 1 p
  let r := RHTower.xiMobiusContinuousApertureDiskNode s p
  let A := q / (1 + q)
  have hc0 : 0 ≤ c :=
    (RHTower.gammaSewnMobiusValuationContractionMultiplier_pos s p).le
  have hc1 : c ≤ 1 :=
    (RHTower.gammaSewnMobiusValuationContractionMultiplier_lt_one hs p).le
  have hq0 : 0 ≤ q := (RHTower.xiTransversePrimeApertureDiskNode_pos 1 p).le
  have hr0 : 0 ≤ r := (RHTower.xiMobiusContinuousApertureDiskNode_pos s p).le
  have hr1 : r ≤ 1 :=
    (RHTower.xiMobiusContinuousApertureDiskNode_lt_one hs p).le
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hAq : A ≤ q := by
    dsimp only [A]
    rw [div_le_iff₀ (by linarith : 0 < 1 + q)]
    nlinarith [sq_nonneg q]
  have hone0 : 0 ≤ 1 - r := sub_nonneg.mpr hr1
  have hone1 : 1 - r ≤ 1 := by linarith
  have hnum : c ^ 2 * A ^ 2 * (1 - r) ^ 2 * r ^ e ≤ q ^ 2 * r ^ e := by
    calc
      c ^ 2 * A ^ 2 * (1 - r) ^ 2 * r ^ e ≤
          1 ^ 2 * q ^ 2 * 1 ^ 2 * r ^ e := by gcongr
      _ = q ^ 2 * r ^ e := by ring
  rw [gammaSewnMobiusApertureStokesReflectedWeight_eq_source hs]
  change c ^ 2 * A ^ 2 * (1 - r) ^ 2 * r ^ e /
      (((e + 1 : ℕ) : ℝ) ^ 2 * Real.log (p : ℝ) * r) ≤ _
  gcongr

/-- Complementary-coordinate information virial after Stokes conditioning. -/
def sourceHorizontalStokesConditionedInformationTerm
    (s : ℝ) (pk : Nat.Primes × ℕ) : ℝ :=
  sourceHorizontalPrimeGeometricKLScaleTerm pk.1 pk.2 ((1 - s) / 2) *
    RHTower.gammaSewnMobiusApertureStokesReflectedWeight s pk

/-- Exact coefficient-faithful two-clock majorant. -/
def sourceHorizontalStokesConditionedInformationMajorant
    (s : ℝ) (pk : Nat.Primes × ℕ) : ℝ :=
  4 * (1 - s) * RHTower.xiTransversePrimeApertureDiskNode 1 pk.1 ^ 2 *
    RHTower.xiMobiusContinuousApertureDiskNode s pk.1 ^ (2 * pk.2) /
      ((pk.2 + 1 : ℝ) ^ 2)

/-- Universal product envelope used only to discharge all-prime/all-valuation summability. -/
def sourceHorizontalStokesConditionedInformationEnvelope
    (s : ℝ) (pk : Nat.Primes × ℕ) : ℝ :=
  4 * (1 - s) * (pk.1 : ℝ) ^ (-2 : ℝ) *
    (Real.exp (-s * Real.log 2) ^ 2) ^ pk.2

/-- Off-wall information virial has the complementary exponential bound. -/
theorem sourceHorizontalPrimeGeometricKLScaleTerm_complementary_le
    {s : ℝ} (hs1 : s < 1) (p : Nat.Primes) (e : ℕ) :
    sourceHorizontalPrimeGeometricKLScaleTerm p e ((1 - s) / 2) ≤
      4 * (1 - s) * Real.log (p : ℝ) *
        Real.exp (-s * Real.log (p : ℝ) * (e + 1)) := by
  let L := Real.log (p : ℝ)
  let k : ℝ := e + 1
  let u := (1 - s) * k * L
  have hL : 0 < L := Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hk : 0 < k := by positivity
  have hu : 0 ≤ u := by
    dsimp only [u]
    positivity
  have harg : 2 * (e + 1) * L * ((1 - s) / 2) = u := by
    dsimp only [u, k]
    ring
  have hexp : Real.exp (-L * (e + 1)) * Real.exp u =
      Real.exp (-s * L * (e + 1)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [u, k]
    ring
  rw [sourceHorizontalPrimeGeometricKLScaleTerm,
    sourceHorizontalPrimePowerHolonomy_scaleVirial, harg]
  calc
    2 * Real.exp (-L * (e + 1)) / (e + 1) *
          (2 * sourceHorizontalHolonomyVirial u) ≤
        2 * Real.exp (-L * (e + 1)) / (e + 1) *
          (2 * (u * Real.exp u)) := by
      gcongr
      exact sourceHorizontalHolonomyVirial_le_mul_exp hu
    _ = 4 * u / k *
          (Real.exp (-L * (e + 1)) * Real.exp u) := by ring
    _ = 4 * (1 - s) * L * Real.exp (-s * L * (e + 1)) := by
      rw [hexp]
      dsimp only [u]
      field_simp [hk.ne']

/-- Every literal information factor is strictly positive at complementary strip coordinate. -/
theorem sourceHorizontalPrimeGeometricKLScaleTerm_complementary_pos
    {s : ℝ} (hs1 : s < 1) (p : Nat.Primes) (e : ℕ) :
    0 < sourceHorizontalPrimeGeometricKLScaleTerm p e ((1 - s) / 2) := by
  rw [sourceHorizontalPrimeGeometricKLScaleTerm]
  exact mul_pos (by positivity)
    (sourceHorizontalPrimePowerHolonomy_scaleVirial_pos p e (by linarith))

/-- Stokes-conditioned information retains strict sign on every prime-power label. -/
theorem sourceHorizontalStokesConditionedInformationTerm_pos
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (pk : Nat.Primes × ℕ) :
    0 < sourceHorizontalStokesConditionedInformationTerm s pk := by
  exact mul_pos
    (sourceHorizontalPrimeGeometricKLScaleTerm_complementary_pos hs1 pk.1 pk.2)
    (RHTower.gammaSewnMobiusApertureStokesReflectedWeight_pos hs pk)

/-- **Two-clock cancellation.**  Complementary horizontal growth and the source reflected Stokes
weight cancel exactly to a quadratic prime envelope while retaining valuation multiplicity. -/
theorem sourceHorizontalStokesConditionedInformationTerm_le_majorant
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (p : Nat.Primes) (e : ℕ) :
    sourceHorizontalStokesConditionedInformationTerm s (p, e) ≤
      sourceHorizontalStokesConditionedInformationMajorant s (p, e) := by
  let L := Real.log (p : ℝ)
  let q := RHTower.xiTransversePrimeApertureDiskNode 1 p
  let r := RHTower.xiMobiusContinuousApertureDiskNode s p
  let k : ℝ := e + 1
  have hL : 0 < L := Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hr : 0 < r := RHTower.xiMobiusContinuousApertureDiskNode_pos s p
  have hk : 0 < k := by positivity
  have hkl := sourceHorizontalPrimeGeometricKLScaleTerm_complementary_le hs1 p e
  have hw := gammaSewnMobiusApertureStokesReflectedWeight_le_twoClock hs p e
  have hw0 : 0 ≤ RHTower.gammaSewnMobiusApertureStokesReflectedWeight s (p, e) :=
    (RHTower.gammaSewnMobiusApertureStokesReflectedWeight_pos hs (p, e)).le
  have hklM0 : 0 ≤ 4 * (1 - s) * L * Real.exp (-s * L * (e + 1)) := by
    positivity
  have hexp : Real.exp (-s * L * (e + 1)) = r ^ (e + 1) := by
    rw [RHTower.xiMobiusContinuousApertureDiskNode_pow]
    congr 1
    dsimp only [L]
    push_cast
    ring
  have hw' : RHTower.gammaSewnMobiusApertureStokesReflectedWeight s (p, e) ≤
      q ^ 2 * r ^ e / (k ^ 2 * L * r) := by
    simpa only [q, r, k, L, Nat.cast_add, Nat.cast_one] using hw
  calc
    sourceHorizontalStokesConditionedInformationTerm s (p, e) ≤
        (4 * (1 - s) * L * Real.exp (-s * L * (e + 1))) *
          (q ^ 2 * r ^ e / (k ^ 2 * L * r)) := by
      exact mul_le_mul hkl hw' hw0 hklM0
    _ = sourceHorizontalStokesConditionedInformationMajorant s (p, e) := by
      rw [hexp, pow_succ]
      change 4 * (1 - s) * L * (r ^ e * r) *
          (q ^ 2 * r ^ e / (k ^ 2 * L * r)) =
        4 * (1 - s) * q ^ 2 * r ^ (2 * e) / k ^ 2
      rw [show 2 * e = e + e by omega, pow_add]
      field_simp [hL.ne', hr.ne', hk.ne']

/-- The two-clock majorant is bounded by a separated `p⁻²` times geometric envelope. -/
theorem sourceHorizontalStokesConditionedInformationMajorant_le_envelope
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (p : Nat.Primes) (e : ℕ) :
    sourceHorizontalStokesConditionedInformationMajorant s (p, e) ≤
      sourceHorizontalStokesConditionedInformationEnvelope s (p, e) := by
  let q := RHTower.xiTransversePrimeApertureDiskNode 1 p
  let r := RHTower.xiMobiusContinuousApertureDiskNode s p
  let R := Real.exp (-s * Real.log 2)
  let k : ℝ := e + 1
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hp0 : 0 < (p : ℝ) := lt_trans zero_lt_one hp
  have hq0 : 0 < q := RHTower.xiTransversePrimeApertureDiskNode_pos 1 p
  have hr0 : 0 < r := RHTower.xiMobiusContinuousApertureDiskNode_pos s p
  have hR0 : 0 < R := Real.exp_pos _
  have hk1 : 1 ≤ k := by dsimp only [k]; norm_num
  have hrR : r ≤ R := by
    dsimp only [r, R, RHTower.xiMobiusContinuousApertureDiskNode]
    apply Real.exp_le_exp.mpr
    have hlogle : Real.log 2 ≤ Real.log (p : ℝ) := by
      apply Real.log_le_log (by norm_num)
      exact_mod_cast p.2.two_le
    nlinarith
  have hq : q = (p : ℝ)⁻¹ := by
    dsimp only [q, RHTower.xiTransversePrimeApertureDiskNode]
    rw [← Real.rpow_neg_one, Real.rpow_def_of_pos hp0]
    congr 1
    ring
  have hqpow : q ^ 2 = (p : ℝ) ^ (-2 : ℝ) := by
    rw [hq, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg hp0.le, Real.rpow_natCast, ← inv_pow]
  have hrad : r ^ (2 * e) ≤ R ^ (2 * e) := by gcongr
  have hnum0 : 0 ≤ 4 * (1 - s) * q ^ 2 * r ^ (2 * e) := by positivity
  calc
    sourceHorizontalStokesConditionedInformationMajorant s (p, e) =
        4 * (1 - s) * q ^ 2 * r ^ (2 * e) / k ^ 2 := rfl
    _ ≤ 4 * (1 - s) * q ^ 2 * r ^ (2 * e) := by
      exact div_le_self hnum0 (by nlinarith [sq_nonneg k])
    _ ≤ 4 * (1 - s) * q ^ 2 * R ^ (2 * e) := by gcongr
    _ = sourceHorizontalStokesConditionedInformationEnvelope s (p, e) := by
      rw [hqpow, pow_mul]
      rfl

/-- Universal separated envelope is summable over every prime and valuation depth. -/
theorem summable_sourceHorizontalStokesConditionedInformationEnvelope
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    Summable (sourceHorizontalStokesConditionedInformationEnvelope s) := by
  let R := Real.exp (-s * Real.log 2)
  have hR0 : 0 ≤ R := (Real.exp_pos _).le
  have hR1 : R < 1 := by
    dsimp only [R]
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have he : Summable (fun e : ℕ => (R ^ 2) ^ e) :=
    summable_geometric_of_lt_one (sq_nonneg R) (by nlinarith [sq_nonneg R])
  have hp : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-2 : ℝ)) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  have hp' : Summable (fun p : Nat.Primes =>
      4 * (1 - s) * (p : ℝ) ^ (-2 : ℝ)) := hp.mul_left _
  have hprod := hp'.mul_of_nonneg he (fun p => by positivity) (fun e => by positivity)
  change Summable (fun pk : Nat.Primes × ℕ =>
    4 * (1 - s) * (pk.1 : ℝ) ^ (-2 : ℝ) *
      (Real.exp (-s * Real.log 2) ^ 2) ^ pk.2)
  simpa only [R] using hprod

/-- Exact source majorant is summable over the complete prime-power carrier. -/
theorem summable_sourceHorizontalStokesConditionedInformationMajorant
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    Summable (sourceHorizontalStokesConditionedInformationMajorant s) := by
  exact Summable.of_nonneg_of_le
    (fun pk => by
      simp only [sourceHorizontalStokesConditionedInformationMajorant]
      apply div_nonneg
      · exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (by positivity) (by linarith)) (sq_nonneg _))
          (pow_nonneg
            (RHTower.xiMobiusContinuousApertureDiskNode_pos s pk.1).le _)
      · exact sq_nonneg _)
    (fun pk =>
      sourceHorizontalStokesConditionedInformationMajorant_le_envelope
        hs hs1 pk.1 pk.2)
    (summable_sourceHorizontalStokesConditionedInformationEnvelope hs hs1)

/-- **Finite source coenergy.**  Literal Stokes-conditioned information terms are summable. -/
theorem summable_sourceHorizontalStokesConditionedInformationTerm
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    Summable (sourceHorizontalStokesConditionedInformationTerm s) := by
  exact Summable.of_nonneg_of_le
    (fun pk => (sourceHorizontalStokesConditionedInformationTerm_pos hs hs1 pk).le)
    (fun pk =>
      sourceHorizontalStokesConditionedInformationTerm_le_majorant hs hs1 pk.1 pk.2)
    (summable_sourceHorizontalStokesConditionedInformationMajorant hs hs1)

/-- Total source-horizontal Stokes-conditioned information coenergy. -/
def sourceHorizontalStokesConditionedInformationCoenergy (s : ℝ) : ℝ :=
  ∑' pk, sourceHorizontalStokesConditionedInformationTerm s pk

/-- Total coenergy remains strictly positive throughout the open physical strip. -/
theorem sourceHorizontalStokesConditionedInformationCoenergy_pos
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    0 < sourceHorizontalStokesConditionedInformationCoenergy s := by
  exact (summable_sourceHorizontalStokesConditionedInformationTerm hs hs1).tsum_pos
    (fun pk => (sourceHorizontalStokesConditionedInformationTerm_pos hs hs1 pk).le)
    (⟨2, Nat.prime_two⟩, 0)
    (sourceHorizontalStokesConditionedInformationTerm_pos hs hs1 _)

end RHTower.HedenmalmThetaSource
