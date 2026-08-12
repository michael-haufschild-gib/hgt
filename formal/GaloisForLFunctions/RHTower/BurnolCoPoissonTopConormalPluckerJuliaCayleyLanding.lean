import GaloisForLFunctions.RHTower.BurnolCoPoissonTopConormalPluckerHolonomyLanding
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceJuliaPythagoras

/-!
# Burnol top conormal as the Xi-Ward Julia normal cone

The actual Xi-zero Burnol holonomy landed in the multiplicity-complete Route-P top conormal, but
its relation to the source Ward geometry was still missing.  This module closes that algebraic
gap at every prime.

Put `A = p^(2 Re(q) - 1)` and use the canonical half-density aperture
`u = (A - 1) / 2`.  The literal Xi-Ward Cayley discrepancy against the critical aperture is

`C = (A - 1) / (A + 1)`.

The normalized Burnol holonomy is its exact Julia normal-cone rationalization

`H = A - A⁻¹ = 4 C / (1 - C²)`.

Therefore the multiplicity-complete co-Poisson top conormal and every admitted Route-P prime
coefficient are the negative Fisher multiple of this one Ward normal coordinate.  Hardy
contractivity only says `|C| < 1`; Route P needs the strictly stronger saturation `C = 0`, which
is exactly the critical-line condition.
-/

open Complex Real

noncomputable section
namespace RHTower.HedenmalmThetaSource

/-- Canonical half-density source aperture whose positive coordinate is the actual centered
prime character of an Xi divisor copy. -/
def burnolXiPrimeCayleyAperture (q : XiZeroCopy) (p : Nat.Primes) : ℝ :=
  ((p : ℝ) ^ primeDepthBVWoldXiCenteredRate q.1 - 1) / 2

theorem one_add_two_mul_burnolXiPrimeCayleyAperture
    (q : XiZeroCopy) (p : Nat.Primes) :
    1 + 2 * burnolXiPrimeCayleyAperture q p =
      (p : ℝ) ^ primeDepthBVWoldXiCenteredRate q.1 := by
  rw [burnolXiPrimeCayleyAperture]
  ring

/-- Canonical aperture always lies in the Hardy half-density domain. -/
theorem burnolXiPrimeCayleyAperture_gt_neg_half
    (q : XiZeroCopy) (p : Nat.Primes) :
    -(1 / 2 : ℝ) < burnolXiPrimeCayleyAperture q p := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  have hpow : 0 < (p : ℝ) ^ primeDepthBVWoldXiCenteredRate q.1 :=
    Real.rpow_pos_of_pos hp0 _
  rw [burnolXiPrimeCayleyAperture]
  linarith

/-- Actual primewise Xi-Ward projective coordinate against critical aperture `0`. -/
def burnolXiPrimeCayleyCoordinate (q : XiZeroCopy) (p : Nat.Primes) : ℝ :=
  mobiusCriticalTwoSidedCayleyDiscrepancy
    (burnolXiPrimeCayleyAperture q p) 0

theorem burnolXiPrimeCayleyCoordinate_eq_character_ratio
    (q : XiZeroCopy) (p : Nat.Primes) :
    burnolXiPrimeCayleyCoordinate q p =
      ((p : ℝ) ^ primeDepthBVWoldXiCenteredRate q.1 - 1) /
        ((p : ℝ) ^ primeDepthBVWoldXiCenteredRate q.1 + 1) := by
  rw [burnolXiPrimeCayleyCoordinate,
    mobiusCriticalTwoSidedCayleyDiscrepancy,
    one_add_two_mul_burnolXiPrimeCayleyAperture]
  norm_num

/-- The coordinate is literally the already-constructed Xi-Ward half-plane Cayley factor. -/
theorem xiWardHalfPlaneCayleyFactor_burnolXiPrimeAperture
    (q : XiZeroCopy) (p : Nat.Primes) :
    xiWardHalfPlaneCayleyFactor
        ((((1 + 2 * burnolXiPrimeCayleyAperture q p) / 2 : ℝ) : ℂ))
        ((((1 + 2 * burnolXiPrimeCayleyAperture q p) / 2 : ℝ) : ℂ))
        1 =
      (burnolXiPrimeCayleyCoordinate q p : ℂ) := by
  simpa [burnolXiPrimeCayleyCoordinate] using
    (xiWardHalfPlaneCayleyFactor_sourceApertures
      (burnolXiPrimeCayleyAperture q p) 0)

/-- Contractivity is automatic on every divisor fibre, including off-line fibres. -/
theorem burnolXiPrimeCayleyCoordinate_mem_Ioo
    (q : XiZeroCopy) (p : Nat.Primes) :
    burnolXiPrimeCayleyCoordinate q p ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  let A : ℝ := (p : ℝ) ^ primeDepthBVWoldXiCenteredRate q.1
  have hA : 0 < A := Real.rpow_pos_of_pos hp0 _
  rw [burnolXiPrimeCayleyCoordinate_eq_character_ratio]
  change -1 < (A - 1) / (A + 1) ∧ (A - 1) / (A + 1) < 1
  have hden : 0 < A + 1 := by linarith
  constructor
  · apply (lt_div_iff₀ hden).2
    linarith
  · apply (div_lt_iff₀ hden).2
    linarith

/-- Ward saturation, unlike contractivity, is exactly pointwise critical-line rigidity. -/
theorem burnolXiPrimeCayleyCoordinate_eq_zero_iff
    (q : XiZeroCopy) (p : Nat.Primes) :
    burnolXiPrimeCayleyCoordinate q p = 0 ↔ (q.1 : ℂ).re = 1 / 2 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  rw [burnolXiPrimeCayleyCoordinate_eq_character_ratio]
  have hden : (p : ℝ) ^ primeDepthBVWoldXiCenteredRate q.1 + 1 ≠ 0 := by
    have hpow := Real.rpow_pos_of_pos hp0 (primeDepthBVWoldXiCenteredRate q.1)
    linarith
  constructor
  · intro hzero
    have hpow : (p : ℝ) ^ primeDepthBVWoldXiCenteredRate q.1 = 1 := by
      exact sub_eq_zero.mp ((div_eq_zero_iff.mp hzero).resolve_right hden)
    have hrate : primeDepthBVWoldXiCenteredRate q.1 = 0 :=
      (Real.strictMono_rpow_of_base_gt_one hp1).injective (by simpa using hpow)
    exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).1 hrate
  · intro hline
    have hrate := (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2 hline
    rw [hrate]
    norm_num

theorem burnolXiPrimeCayleyAperture_eq_zero_iff
    (q : XiZeroCopy) (p : Nat.Primes) :
    burnolXiPrimeCayleyAperture q p = 0 ↔ (q.1 : ℂ).re = 1 / 2 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  rw [burnolXiPrimeCayleyAperture]
  constructor
  · intro hzero
    have hpow : (p : ℝ) ^ primeDepthBVWoldXiCenteredRate q.1 = 1 := by linarith
    have hrate : primeDepthBVWoldXiCenteredRate q.1 = 0 :=
      (Real.strictMono_rpow_of_base_gt_one hp1).injective (by simpa using hpow)
    exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).1 hrate
  · intro hline
    have hrate := (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2 hline
    rw [hrate]
    norm_num

/-- **P-G102 Julia normal-cone identity.**  On every actual right-half Xi-zero fibre, normalized
Burnol holonomy is the rational normal coordinate of the literal Xi-Ward Cayley cell. -/
theorem burnolCoPoissonNormalizedHolonomy_eq_four_mul_cayley_div_one_sub_sq
    (q : XiZeroCopy) (hq : 1 / 2 < (q.1 : ℂ).re)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (p : Nat.Primes) :
    burnolCoPoissonNormalizedHolonomy (w := (q.1 : ℂ)) (r := (p : ℝ))
        hq (xi_divisor_support_re_mem_open_unit q.1).2 ha
        (by exact_mod_cast p.2.one_lt) =
      4 * burnolXiPrimeCayleyCoordinate q p /
        (1 - burnolXiPrimeCayleyCoordinate q p ^ 2) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  let A : ℝ := (p : ℝ) ^ primeDepthBVWoldXiCenteredRate q.1
  have hA : 0 < A := Real.rpow_pos_of_pos hp0 _
  have hA0 : A ≠ 0 := hA.ne'
  rw [burnolCoPoissonNormalizedHolonomy_xiZeroCopy_eq_character q hq ha ha1,
    burnolXiPrimeCayleyCoordinate_eq_character_ratio]
  change A - (p : ℝ) ^ (-primeDepthBVWoldXiCenteredRate q.1) =
    4 * ((A - 1) / (A + 1)) / (1 - ((A - 1) / (A + 1)) ^ 2)
  rw [Real.rpow_neg hp0.le]
  change A - A⁻¹ = _
  field_simp [hA0, (by linarith : A + 1 ≠ 0)]
  have hden : (A + 1) ^ 2 - (A - 1) ^ 2 = 4 * A := by ring
  rw [hden]
  field_simp [hA0]
  ring

/-- Multiplicity-complete co-Poisson top conormal is the negative Fisher-weighted Ward normal
coordinate. -/
theorem burnolActualConormalMetricImbalance_eq_neg_four_fisher_mul_cayley_div_one_sub_sq
    (q : XiZeroCopy) (hq : 1 / 2 < (q.1 : ℂ).re)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (p : Nat.Primes) :
    burnolActualConormalMetricImbalance q p =
      -4 * primeActivationOccupancyFisherDensity p *
        burnolXiPrimeCayleyCoordinate q p /
          (1 - burnolXiPrimeCayleyCoordinate q p ^ 2) := by
  rw [burnolActualConormalMetricImbalance_eq_neg_fisher_mul_burnolHolonomy
      q hq ha ha1,
    burnolCoPoissonNormalizedHolonomy_eq_four_mul_cayley_div_one_sub_sq
      q hq ha ha1]
  ring

/-- The source Hardy overlap saturates precisely when Route P's multiplicity-complete top
conormal vanishes. -/
theorem unitHardyGram_burnolXiPrimeAperture_eq_one_iff_conormal_zero
    (q : XiZeroCopy) (p : Nat.Primes) :
    mobiusCriticalTwoSidedUnitHardyGram (burnolXiPrimeCayleyAperture q p) 0 = 1 ↔
      burnolActualConormalMetricImbalance q p = 0 := by
  rw [mobiusCriticalTwoSidedUnitHardyGram_eq_one_iff
      (burnolXiPrimeCayleyAperture_gt_neg_half q p) (by norm_num),
    burnolXiPrimeCayleyAperture_eq_zero_iff,
    burnolActualConormalMetricImbalance_eq_zero_iff]

end RHTower.HedenmalmThetaSource
