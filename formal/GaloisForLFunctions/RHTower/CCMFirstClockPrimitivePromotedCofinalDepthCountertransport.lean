import GaloisForLFunctions.RHTower.CCMFirstClockPrimitivePromotedTwoScaleDomination
import GaloisForLFunctions.RHTower.CCMFirstClockPrimitivePromotedPrimePowerCellGreenTransport

/-!
# Cofinal source-normal depth countertransport

The finite primitive-promoted Route-J current has a linear lower floor, so
it cannot itself be a uniformly bounded scalar capacity.  This module
constructs the source-normal carrier which retains that finite current while
moving it through actual Euler depths.

At a prime `p`, the unique critical deattenuation from depth `r` back to
depth zero is

`J₀(p,0) / J₀(p,r)`.

Spreading a depth-zero cell over

`ceil (log p)`

actual depths therefore retains its primitive landing and changes its
squared carrier cost from `log(p)^2 / p` to at most `log(p) / p`.
Applied on both legs of the two-scale current, the resulting depth rectangle
has an aperture-independent capacity.  Reversing both finite depth intervals
and exchanging the exterior legs fixes the landed profile, which is the
reflected Hodge intertwining law.

The singular depth codiagonal still has unbounded gain.  Thus this is the
required pretrace carrier and a quantitative anti-theatre boundary; it is not
the still-missing bounded post-Hodge Route-J residual.
-/

open Set Finset Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower
namespace PrimitivePromotedCofinalDepth

/-- Source-forced number of actual Euler depths used at a prime. -/
def primeDepthMultiplicity (p : ℕ) : ℕ :=
  Nat.ceil (Real.log (p : ℝ))

theorem primeDepthMultiplicity_pos
    {p : ℕ} (hp : 1 < p) :
    0 < primeDepthMultiplicity p := by
  rw [primeDepthMultiplicity, Nat.ceil_pos]
  exact Real.log_pos (by exact_mod_cast hp)

theorem log_le_primeDepthMultiplicity (p : ℕ) :
    Real.log (p : ℝ) ≤ (primeDepthMultiplicity p : ℝ) := by
  exact Nat.le_ceil _

/--
Unique critical source-normal deattenuation from the realized depth
`e + r` back to the recorded source depth `e`.
-/
def criticalDepthDeattenuation
    (pe : Nat.Primes × ℕ) (r : ℕ) : ℝ :=
  xiGammaEulerPrimitiveBoundaryAmplitude 0 pe /
    xiGammaEulerPrimitiveBoundaryAmplitude 0 (pe.1, pe.2 + r)

theorem criticalDepthDeattenuation_pos
    (pe : Nat.Primes × ℕ) (r : ℕ) :
    0 < criticalDepthDeattenuation pe r := by
  exact div_pos
    (xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 pe)
    (xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 (pe.1, pe.2 + r))

/-- Deattenuation followed by physical Gamma landing recovers the recorded
primitive cell exactly. -/
theorem criticalDepthDeattenuation_mul_landing
    (pe : Nat.Primes × ℕ) (r : ℕ) :
    criticalDepthDeattenuation pe r *
        xiGammaEulerPrimitiveBoundaryAmplitude 0 (pe.1, pe.2 + r) =
      xiGammaEulerPrimitiveBoundaryAmplitude 0 pe := by
  rw [criticalDepthDeattenuation, div_mul_cancel₀]
  exact
    (xiGammaEulerPrimitiveBoundaryAmplitude_pos
      0 (pe.1, pe.2 + r)).ne'

/-- The forced deattenuation has exactly the primitive gauge square `p^r`. -/
theorem criticalDepthDeattenuation_sq
    (pe : Nat.Primes × ℕ) (r : ℕ) :
    criticalDepthDeattenuation pe r ^ 2 = (pe.1 : ℝ) ^ r := by
  have hsource :=
    xiGammaEulerPrimitiveBoundaryAmplitude_sq 0 pe
  have hrealized :=
    xiGammaEulerPrimitiveBoundaryAmplitude_sq 0 (pe.1, pe.2 + r)
  have hpLog :
      Real.log (pe.1 : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast pe.1.property.one_lt)).ne'
  have hp0 : (pe.1 : ℝ) ≠ 0 := by
    exact_mod_cast pe.1.property.ne_zero
  have hvaluationSource :
      (xiGammaEulerValuationNat pe : ℝ) =
        (pe.1 : ℝ) ^ (pe.2 + 1) := by
    simp [xiGammaEulerValuationNat]
  have hvaluationRealized :
      (xiGammaEulerValuationNat (pe.1, pe.2 + r) : ℝ) =
        (pe.1 : ℝ) ^ (pe.2 + r + 1) := by
    simp [xiGammaEulerValuationNat]
  rw [criticalDepthDeattenuation, div_pow, hsource, hrealized,
    hvaluationSource, hvaluationRealized]
  norm_num
  field_simp [hpLog, hp0]
  rw [show pe.2 + r + 1 = (pe.2 + 1) + r by omega, pow_add]

/-- Squared critical depth-zero mass divided by the source-forced depth
multiplicity. -/
def depthNormalizedPrimeMass (p : ℕ) : ℝ :=
  xiGammaEulerPrimitiveDepthZeroAmplitude p ^ 2 /
    (primeDepthMultiplicity p : ℝ)

theorem depthNormalizedPrimeMass_nonneg
    {p : ℕ} (_hp : 1 < p) :
    0 ≤ depthNormalizedPrimeMass p := by
  exact div_nonneg (sq_nonneg _)
    (Nat.cast_nonneg (primeDepthMultiplicity p))

/-- Logarithmic depth removes exactly one source logarithm from the critical
prime cost. -/
theorem depthNormalizedPrimeMass_le_log_div
    {p : ℕ} (hp : 1 < p) :
    depthNormalizedPrimeMass p ≤ Real.log (p : ℝ) / p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (lt_trans Nat.zero_lt_one hp)
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    (Real.log_pos (by exact_mod_cast hp)).le
  have hK :
      (0 : ℝ) < primeDepthMultiplicity p := by
    exact_mod_cast primeDepthMultiplicity_pos hp
  have hlogK :
      Real.log (p : ℝ) / (primeDepthMultiplicity p : ℝ) ≤ 1 := by
    exact (div_le_one hK).2 (log_le_primeDepthMultiplicity p)
  calc
    depthNormalizedPrimeMass p =
        (Real.log (p : ℝ) / p) *
          (Real.log (p : ℝ) / (primeDepthMultiplicity p : ℝ)) := by
      rw [depthNormalizedPrimeMass,
        xiGammaEulerPrimitiveDepthZeroAmplitude_sq]
      field_simp [hpR.ne', hK.ne']
    _ ≤ (Real.log (p : ℝ) / p) * 1 := by
      exact mul_le_mul_of_nonneg_left hlogK (div_nonneg hlog hpR.le)
    _ = Real.log (p : ℝ) / p := by ring

/-- Source-normal mass of one moving fivefold prime block. -/
def depthNormalizedFivePrimeBlockMass (n : ℕ) : ℝ :=
  ∑ p ∈ suzukiMangoldtFivePrimeBlock n, depthNormalizedPrimeMass p

/-- Every moving fivefold block has uniformly bounded source-normal mass. -/
theorem depthNormalizedFivePrimeBlockMass_le_five
    {n : ℕ} (hn : 0 < n) :
    depthNormalizedFivePrimeBlockMass n ≤ 5 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    depthNormalizedFivePrimeBlockMass n ≤
        ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
          Real.log (p : ℝ) / p := by
      apply Finset.sum_le_sum
      intro p hp
      exact depthNormalizedPrimeMass_le_log_div
        (mem_suzukiMangoldtFivePrimeBlock.mp hp).1.one_lt
    _ ≤ ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
          Real.log (p : ℝ) / (2 * (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpPrime, hpLower, _hpUpper⟩ :=
        mem_suzukiMangoldtFivePrimeBlock.mp hp
      exact div_le_div_of_nonneg_left
        (Real.log_nonneg
          (by exact_mod_cast hpPrime.one_le : (1 : ℝ) ≤ (p : ℝ)))
        (by positivity)
        (by exact_mod_cast hpLower.le)
    _ = (∑ p ∈ suzukiMangoldtFivePrimeBlock n,
          Real.log (p : ℝ)) / (2 * (n : ℝ)) := by
      rw [Finset.sum_div]
    _ ≤ (10 * (n : ℝ)) / (2 * (n : ℝ)) := by
      exact div_le_div_of_nonneg_right
        (PrimitivePromotedTwoScale.fivePrimeBlock_logMass_upper hn)
        (by positivity)
    _ = 5 := by
      field_simp [hnR.ne']
      norm_num

/-- Landed coefficient on one actual depth rectangle of a low/high source
pair. -/
def landedDepthPairProfile
    (n p q : ℕ)
    (_r : Fin (primeDepthMultiplicity p))
    (_s : Fin (primeDepthMultiplicity q)) : ℝ :=
  2 * PrimitivePromotedTwoScale.anchoredCrossPair n p q /
    ((primeDepthMultiplicity p : ℝ) *
      (primeDepthMultiplicity q : ℝ))

/-- Exchange of source legs preserves the anchored Hermitian scalar. -/
theorem anchoredCrossPair_swap (n p q : ℕ) :
    PrimitivePromotedTwoScale.anchoredCrossPair n q p =
      PrimitivePromotedTwoScale.anchoredCrossPair n p q := by
  unfold PrimitivePromotedTwoScale.anchoredCrossPair
  rw [show
      PrimitivePromotedTwoScale.twoScalePhase *
          (PrimitivePromotedTwoScale.relativeHeight n p -
            PrimitivePromotedTwoScale.relativeHeight n q) =
        -(PrimitivePromotedTwoScale.twoScalePhase *
          (PrimitivePromotedTwoScale.relativeHeight n q -
            PrimitivePromotedTwoScale.relativeHeight n p)) by ring,
    Real.sin_neg]
  ring

/--
Reflected Hodge intertwining: exchange exterior legs and reverse both finite
depth intervals.  The landed source profile is fixed.  The exterior swap
sign is carried by the odd orientation local system before this scalar
profile is read.
-/
theorem landedDepthPairProfile_reflection
    (n p q : ℕ)
    (r : Fin (primeDepthMultiplicity p))
    (s : Fin (primeDepthMultiplicity q)) :
    landedDepthPairProfile n q p (Fin.rev s) (Fin.rev r) =
      landedDepthPairProfile n p q r s := by
  rw [landedDepthPairProfile, landedDepthPairProfile,
    anchoredCrossPair_swap]
  ring

/-- Landed depth profile for one ordered prime pair. -/
abbrev LandedDepthPairProfileSpace (p q : ℕ) :=
  Fin (primeDepthMultiplicity p) →
    Fin (primeDepthMultiplicity q) → ℝ

/--
Raw exterior reflection exchanges the two source legs, reverses both depth
intervals, and contributes the alternating exterior sign.
-/
def rawExteriorDepthReflection
    {p q : ℕ}
    (x : LandedDepthPairProfileSpace q p) :
    LandedDepthPairProfileSpace p q :=
  fun r s => -x (Fin.rev s) (Fin.rev r)

/-- Odd source orientation contributes the second sign. -/
def oddOrientationDepthTwist
    {p q : ℕ}
    (x : LandedDepthPairProfileSpace p q) :
    LandedDepthPairProfileSpace p q :=
  fun r s => -x r s

/-- Reflected Hodge exchange after the odd orientation twist. -/
def compensatedDepthReflection
    {p q : ℕ}
    (x : LandedDepthPairProfileSpace q p) :
    LandedDepthPairProfileSpace p q :=
  oddOrientationDepthTwist (rawExteriorDepthReflection x)

theorem compensatedDepthReflection_eq
    {p q : ℕ}
    (x : LandedDepthPairProfileSpace q p)
    (r : Fin (primeDepthMultiplicity p))
    (s : Fin (primeDepthMultiplicity q)) :
    compensatedDepthReflection x r s =
      x (Fin.rev s) (Fin.rev r) := by
  simp [compensatedDepthReflection, oddOrientationDepthTwist,
    rawExteriorDepthReflection]

theorem compensatedDepthReflection_involutive
    {p q : ℕ}
    (x : LandedDepthPairProfileSpace p q) :
    compensatedDepthReflection (compensatedDepthReflection x) = x := by
  funext r s
  simp [compensatedDepthReflection_eq]

/-- Both ordered orientations of one reflected depth rectangle. -/
abbrev DoubledLandedDepthPairProfileSpace (p q : ℕ) :=
  LandedDepthPairProfileSpace p q ×
    LandedDepthPairProfileSpace q p

/-- Total reflected Hodge involution on the doubled ordered-pair carrier. -/
def reflectedDepthHodge
    {p q : ℕ}
    (x : DoubledLandedDepthPairProfileSpace p q) :
    DoubledLandedDepthPairProfileSpace p q :=
  (compensatedDepthReflection x.2,
    compensatedDepthReflection x.1)

theorem reflectedDepthHodge_sq
    {p q : ℕ}
    (x : DoubledLandedDepthPairProfileSpace p q) :
    reflectedDepthHodge (reflectedDepthHodge x) = x := by
  rcases x with ⟨x, y⟩
  simp only [reflectedDepthHodge]
  rw [compensatedDepthReflection_involutive,
    compensatedDepthReflection_involutive]

/-- Concrete fixed reflected Hodge sector of the doubled carrier. -/
def reflectedDepthHodgeSector (p q : ℕ) :
    Set (DoubledLandedDepthPairProfileSpace p q) :=
  {x | reflectedDepthHodge x = x}

/-- The actual landed countertransport on both ordered orientations. -/
def doubledLandedDepthPairProfile (n p q : ℕ) :
    DoubledLandedDepthPairProfileSpace p q :=
  (landedDepthPairProfile n p q,
    landedDepthPairProfile n q p)

/--
The countertransport lies in the concrete reflected Hodge fixed sector.
This theorem includes both exterior and odd-orientation signs through
`compensatedDepthReflection`; it is stronger than scalar symmetry alone.
-/
theorem doubledLandedDepthPairProfile_mem_reflectedDepthHodgeSector
    (n p q : ℕ) :
    doubledLandedDepthPairProfile n p q ∈
      reflectedDepthHodgeSector p q := by
  change
    reflectedDepthHodge (doubledLandedDepthPairProfile n p q) =
      doubledLandedDepthPairProfile n p q
  apply Prod.ext
  · funext r s
    change
      compensatedDepthReflection
          (landedDepthPairProfile n q p) r s =
        landedDepthPairProfile n p q r s
    rw [compensatedDepthReflection_eq]
    exact landedDepthPairProfile_reflection n p q r s
  · funext s r
    change
      compensatedDepthReflection
          (landedDepthPairProfile n p q) s r =
        landedDepthPairProfile n q p s r
    rw [compensatedDepthReflection_eq]
    exact landedDepthPairProfile_reflection n q p s r

/-- Singular depth codiagonal on one rectangle recovers the finite source
pair exactly. -/
theorem sum_landedDepthPairProfile
    {n p q : ℕ}
    (hp : 1 < p) (hq : 1 < q) :
    ∑ r : Fin (primeDepthMultiplicity p),
      ∑ s : Fin (primeDepthMultiplicity q),
        landedDepthPairProfile n p q r s =
      2 * PrimitivePromotedTwoScale.anchoredCrossPair n p q := by
  have hKp : (primeDepthMultiplicity p : ℝ) ≠ 0 := by
    exact_mod_cast (primeDepthMultiplicity_pos hp).ne'
  have hKq : (primeDepthMultiplicity q : ℝ) ≠ 0 := by
    exact_mod_cast (primeDepthMultiplicity_pos hq).ne'
  simp only [landedDepthPairProfile, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hKp, hKq]

/-- Squared source-normal carrier capacity of one depth rectangle. -/
def landedDepthPairCapacity (n p q : ℕ) : ℝ :=
  ∑ r : Fin (primeDepthMultiplicity p),
    ∑ s : Fin (primeDepthMultiplicity q),
      landedDepthPairProfile n p q r s ^ 2

theorem landedDepthPairCapacity_eq
    {n p q : ℕ}
    (hp : 1 < p) (hq : 1 < q) :
    landedDepthPairCapacity n p q =
      4 * PrimitivePromotedTwoScale.anchoredCrossPair n p q ^ 2 /
        ((primeDepthMultiplicity p : ℝ) *
          (primeDepthMultiplicity q : ℝ)) := by
  have hKp : (primeDepthMultiplicity p : ℝ) ≠ 0 := by
    exact_mod_cast (primeDepthMultiplicity_pos hp).ne'
  have hKq : (primeDepthMultiplicity q : ℝ) ≠ 0 := by
    exact_mod_cast (primeDepthMultiplicity_pos hq).ne'
  rw [landedDepthPairCapacity]
  simp only [landedDepthPairProfile, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hKp, hKq]
  ring

/-- Uniform elementary upper bound for the source phase-height kernel on
the separated low/high blocks. -/
theorem anchoredCrossPair_upper
    {n p q : ℕ} (hn : 0 < n)
    (hp : p ∈ suzukiMangoldtFivePrimeBlock n)
    (hq : q ∈ suzukiMangoldtFivePrimeBlock
      (PrimitivePromotedTwoScale.sourceDilation * n)) :
    PrimitivePromotedTwoScale.anchoredCrossPair n p q ≤
      289 * xiGammaEulerPrimitiveDepthZeroAmplitude p *
        xiGammaEulerPrimitiveDepthZeroAmplitude q := by
  have hpPrime := (mem_suzukiMangoldtFivePrimeBlock.mp hp).1
  have hqPrime := (mem_suzukiMangoldtFivePrimeBlock.mp hq).1
  have hpRel := PrimitivePromotedTwoScale.low_relativeHeight_mem hn hp
  have hqRel := PrimitivePromotedTwoScale.high_relativeHeight_mem hn hq
  rcases hpRel with ⟨hpRelLower, hpRelUpper⟩
  rcases hqRel with ⟨hqRelLower, hqRelUpper⟩
  have hgap :
      |PrimitivePromotedTwoScale.relativeHeight n q ^ 2 -
          PrimitivePromotedTwoScale.relativeHeight n p ^ 2| ≤ 289 := by
    rw [abs_le]
    constructor
    · nlinarith [
        sq_nonneg (PrimitivePromotedTwoScale.relativeHeight n p),
        sq_nonneg (PrimitivePromotedTwoScale.relativeHeight n q)]
    · nlinarith [
        sq_nonneg (PrimitivePromotedTwoScale.relativeHeight n p),
        sq_nonneg
          (17 - PrimitivePromotedTwoScale.relativeHeight n q)]
  have hA :
      0 ≤ xiGammaEulerPrimitiveDepthZeroAmplitude p := by
    exact mul_nonneg
      (Real.log_nonneg
        (by exact_mod_cast hpPrime.one_le : (1 : ℝ) ≤ (p : ℝ)))
      (criticalPrimeTowerRadius_pos hpPrime.pos).le
  have hB :
      0 ≤ xiGammaEulerPrimitiveDepthZeroAmplitude q := by
    exact mul_nonneg
      (Real.log_nonneg
        (by exact_mod_cast hqPrime.one_le : (1 : ℝ) ≤ (q : ℝ)))
      (criticalPrimeTowerRadius_pos hqPrime.pos).le
  calc
    PrimitivePromotedTwoScale.anchoredCrossPair n p q ≤
        |PrimitivePromotedTwoScale.anchoredCrossPair n p q| :=
      le_abs_self _
    _ =
        xiGammaEulerPrimitiveDepthZeroAmplitude p *
          xiGammaEulerPrimitiveDepthZeroAmplitude q *
          |PrimitivePromotedTwoScale.relativeHeight n q ^ 2 -
            PrimitivePromotedTwoScale.relativeHeight n p ^ 2| *
          |Real.sin
            (PrimitivePromotedTwoScale.twoScalePhase *
              (PrimitivePromotedTwoScale.relativeHeight n q -
                PrimitivePromotedTwoScale.relativeHeight n p))| := by
      unfold PrimitivePromotedTwoScale.anchoredCrossPair
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hA, abs_of_nonneg hB]
    _ ≤
        (xiGammaEulerPrimitiveDepthZeroAmplitude p *
          xiGammaEulerPrimitiveDepthZeroAmplitude q * 289) * 1 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hgap (mul_nonneg hA hB))
        (Real.abs_sin_le_one _)
        (abs_nonneg _)
        (mul_nonneg (mul_nonneg hA hB) (by norm_num))
    _ = 289 * xiGammaEulerPrimitiveDepthZeroAmplitude p *
        xiGammaEulerPrimitiveDepthZeroAmplitude q := by ring

theorem anchoredCrossPair_sq_upper
    {n p q : ℕ} (hn : 0 < n)
    (hp : p ∈ suzukiMangoldtFivePrimeBlock n)
    (hq : q ∈ suzukiMangoldtFivePrimeBlock
      (PrimitivePromotedTwoScale.sourceDilation * n)) :
    PrimitivePromotedTwoScale.anchoredCrossPair n p q ^ 2 ≤
      289 ^ 2 *
        xiGammaEulerPrimitiveDepthZeroAmplitude p ^ 2 *
        xiGammaEulerPrimitiveDepthZeroAmplitude q ^ 2 := by
  have hpPrime := (mem_suzukiMangoldtFivePrimeBlock.mp hp).1
  have hqPrime := (mem_suzukiMangoldtFivePrimeBlock.mp hq).1
  have hA :
      0 ≤ xiGammaEulerPrimitiveDepthZeroAmplitude p := by
    exact mul_nonneg
      (Real.log_nonneg
        (by exact_mod_cast hpPrime.one_le : (1 : ℝ) ≤ (p : ℝ)))
      (criticalPrimeTowerRadius_pos hpPrime.pos).le
  have hB :
      0 ≤ xiGammaEulerPrimitiveDepthZeroAmplitude q := by
    exact mul_nonneg
      (Real.log_nonneg
        (by exact_mod_cast hqPrime.one_le : (1 : ℝ) ≤ (q : ℝ)))
      (criticalPrimeTowerRadius_pos hqPrime.pos).le
  have hQ :
      0 ≤ PrimitivePromotedTwoScale.anchoredCrossPair n p q := by
    have hlower :=
      PrimitivePromotedTwoScale.anchoredCrossPair_lower hn hp hq
    nlinarith [mul_nonneg hA hB]
  have hupper := anchoredCrossPair_upper hn hp hq
  nlinarith [sq_nonneg
    (289 * xiGammaEulerPrimitiveDepthZeroAmplitude p *
      xiGammaEulerPrimitiveDepthZeroAmplitude q -
        PrimitivePromotedTwoScale.anchoredCrossPair n p q)]

/-- Complete source-normal capacity of the cofinal depth-nonlocal two-scale
countertransport. -/
def cofinalDepthCountertransportCapacity (n : ℕ) : ℝ :=
  4 * ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
    ∑ q ∈ suzukiMangoldtFivePrimeBlock
        (PrimitivePromotedTwoScale.sourceDilation * n),
      PrimitivePromotedTwoScale.anchoredCrossPair n p q ^ 2 /
        ((primeDepthMultiplicity p : ℝ) *
          (primeDepthMultiplicity q : ℝ))

theorem cofinalDepthCountertransportCapacity_nonneg
    (n : ℕ) :
    0 ≤ cofinalDepthCountertransportCapacity n := by
  unfold cofinalDepthCountertransportCapacity
  positivity

/--
Raw Hilbert capacity of both ordered orientations in the reflected Hodge
carrier.  Unlike the orbit-normalized capacity, this counts both members of
every reflection orbit.
-/
def reflectedHodgeCountertransportCapacity (n : ℕ) : ℝ :=
  ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
    ∑ q ∈ suzukiMangoldtFivePrimeBlock
        (PrimitivePromotedTwoScale.sourceDilation * n),
      (landedDepthPairCapacity n p q +
        landedDepthPairCapacity n q p)

theorem reflectedHodgeCountertransportCapacity_eq
    {n : ℕ} (_hn : 0 < n) :
    reflectedHodgeCountertransportCapacity n =
      2 * cofinalDepthCountertransportCapacity n := by
  unfold reflectedHodgeCountertransportCapacity
  calc
    ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
        ∑ q ∈ suzukiMangoldtFivePrimeBlock
            (PrimitivePromotedTwoScale.sourceDilation * n),
          (landedDepthPairCapacity n p q +
            landedDepthPairCapacity n q p) =
        ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
          ∑ q ∈ suzukiMangoldtFivePrimeBlock
              (PrimitivePromotedTwoScale.sourceDilation * n),
            2 * (4 *
              PrimitivePromotedTwoScale.anchoredCrossPair n p q ^ 2 /
                ((primeDepthMultiplicity p : ℝ) *
                  (primeDepthMultiplicity q : ℝ))) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      rw [landedDepthPairCapacity_eq
          (mem_suzukiMangoldtFivePrimeBlock.mp hp).1.one_lt
          (mem_suzukiMangoldtFivePrimeBlock.mp hq).1.one_lt,
        landedDepthPairCapacity_eq
          (mem_suzukiMangoldtFivePrimeBlock.mp hq).1.one_lt
          (mem_suzukiMangoldtFivePrimeBlock.mp hp).1.one_lt,
        anchoredCrossPair_swap]
      ring
    _ = 2 *
        (∑ p ∈ suzukiMangoldtFivePrimeBlock n,
          ∑ q ∈ suzukiMangoldtFivePrimeBlock
              (PrimitivePromotedTwoScale.sourceDilation * n),
            4 *
              PrimitivePromotedTwoScale.anchoredCrossPair n p q ^ 2 /
                ((primeDepthMultiplicity p : ℝ) *
                  (primeDepthMultiplicity q : ℝ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
    _ = 2 * (4 *
        ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
          ∑ q ∈ suzukiMangoldtFivePrimeBlock
              (PrimitivePromotedTwoScale.sourceDilation * n),
            PrimitivePromotedTwoScale.anchoredCrossPair n p q ^ 2 /
              ((primeDepthMultiplicity p : ℝ) *
                (primeDepthMultiplicity q : ℝ))) := by
      apply congrArg (fun x : ℝ => 2 * x)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = 2 * cofinalDepthCountertransportCapacity n := by
      rfl

/--
**Uniform carrier-capacity theorem.**  The actual-depth countertransport
retains every finite two-scale source coefficient and has one
aperture-independent source-normal capacity.
-/
theorem cofinalDepthCountertransportCapacity_le
    {n : ℕ} (hn : 0 < n) :
    cofinalDepthCountertransportCapacity n ≤ 100 * 289 ^ 2 := by
  have hKn :
      0 < PrimitivePromotedTwoScale.sourceDilation * n :=
    Nat.mul_pos PrimitivePromotedTwoScale.sourceDilation_pos hn
  have hdouble :
      ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
          ∑ q ∈ suzukiMangoldtFivePrimeBlock
              (PrimitivePromotedTwoScale.sourceDilation * n),
            PrimitivePromotedTwoScale.anchoredCrossPair n p q ^ 2 /
              ((primeDepthMultiplicity p : ℝ) *
                (primeDepthMultiplicity q : ℝ)) ≤
        289 ^ 2 *
          depthNormalizedFivePrimeBlockMass n *
          depthNormalizedFivePrimeBlockMass
            (PrimitivePromotedTwoScale.sourceDilation * n) := by
    calc
      ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
          ∑ q ∈ suzukiMangoldtFivePrimeBlock
              (PrimitivePromotedTwoScale.sourceDilation * n),
            PrimitivePromotedTwoScale.anchoredCrossPair n p q ^ 2 /
              ((primeDepthMultiplicity p : ℝ) *
                (primeDepthMultiplicity q : ℝ)) ≤
          ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
            ∑ q ∈ suzukiMangoldtFivePrimeBlock
                (PrimitivePromotedTwoScale.sourceDilation * n),
              289 ^ 2 *
                depthNormalizedPrimeMass p *
                depthNormalizedPrimeMass q := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro q hq
        have hpOne :=
          (mem_suzukiMangoldtFivePrimeBlock.mp hp).1.one_lt
        have hqOne :=
          (mem_suzukiMangoldtFivePrimeBlock.mp hq).1.one_lt
        have hden :
            0 ≤ (primeDepthMultiplicity p : ℝ) *
              (primeDepthMultiplicity q : ℝ) := by positivity
        have hsquare := anchoredCrossPair_sq_upper hn hp hq
        calc
          PrimitivePromotedTwoScale.anchoredCrossPair n p q ^ 2 /
                ((primeDepthMultiplicity p : ℝ) *
                  (primeDepthMultiplicity q : ℝ)) ≤
              (289 ^ 2 *
                xiGammaEulerPrimitiveDepthZeroAmplitude p ^ 2 *
                xiGammaEulerPrimitiveDepthZeroAmplitude q ^ 2) /
                ((primeDepthMultiplicity p : ℝ) *
                  (primeDepthMultiplicity q : ℝ)) :=
            div_le_div_of_nonneg_right hsquare hden
          _ = 289 ^ 2 *
                depthNormalizedPrimeMass p *
                depthNormalizedPrimeMass q := by
            rw [depthNormalizedPrimeMass, depthNormalizedPrimeMass]
            field_simp [
              (show (primeDepthMultiplicity p : ℝ) ≠ 0 by
                exact_mod_cast (primeDepthMultiplicity_pos hpOne).ne'),
              (show (primeDepthMultiplicity q : ℝ) ≠ 0 by
                exact_mod_cast (primeDepthMultiplicity_pos hqOne).ne')]
      _ = 289 ^ 2 *
          depthNormalizedFivePrimeBlockMass n *
          depthNormalizedFivePrimeBlockMass
            (PrimitivePromotedTwoScale.sourceDilation * n) := by
        unfold depthNormalizedFivePrimeBlockMass
        calc
          ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
              ∑ q ∈ suzukiMangoldtFivePrimeBlock
                  (PrimitivePromotedTwoScale.sourceDilation * n),
                289 ^ 2 * depthNormalizedPrimeMass p *
                  depthNormalizedPrimeMass q =
              ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
                (289 ^ 2 * depthNormalizedPrimeMass p) *
                  (∑ q ∈ suzukiMangoldtFivePrimeBlock
                      (PrimitivePromotedTwoScale.sourceDilation * n),
                    depthNormalizedPrimeMass q) := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [Finset.mul_sum]
          _ =
              (∑ p ∈ suzukiMangoldtFivePrimeBlock n,
                289 ^ 2 * depthNormalizedPrimeMass p) *
                  (∑ q ∈ suzukiMangoldtFivePrimeBlock
                      (PrimitivePromotedTwoScale.sourceDilation * n),
                    depthNormalizedPrimeMass q) := by
            rw [Finset.sum_mul]
          _ = 289 ^ 2 *
                (∑ p ∈ suzukiMangoldtFivePrimeBlock n,
                  depthNormalizedPrimeMass p) *
                  (∑ q ∈ suzukiMangoldtFivePrimeBlock
                      (PrimitivePromotedTwoScale.sourceDilation * n),
                    depthNormalizedPrimeMass q) := by
            exact congrArg
              (fun x : ℝ =>
                x * (∑ q ∈ suzukiMangoldtFivePrimeBlock
                  (PrimitivePromotedTwoScale.sourceDilation * n),
                    depthNormalizedPrimeMass q))
              (by rw [Finset.mul_sum])
  have hlow := depthNormalizedFivePrimeBlockMass_le_five hn
  have hhigh := depthNormalizedFivePrimeBlockMass_le_five hKn
  have hmassLow :
      0 ≤ depthNormalizedFivePrimeBlockMass n := by
    apply Finset.sum_nonneg
    intro p hp
    exact depthNormalizedPrimeMass_nonneg
      (mem_suzukiMangoldtFivePrimeBlock.mp hp).1.one_lt
  have hmassHigh :
      0 ≤ depthNormalizedFivePrimeBlockMass
        (PrimitivePromotedTwoScale.sourceDilation * n) := by
    apply Finset.sum_nonneg
    intro q hq
    exact depthNormalizedPrimeMass_nonneg
      (mem_suzukiMangoldtFivePrimeBlock.mp hq).1.one_lt
  unfold cofinalDepthCountertransportCapacity
  nlinarith

/--
Uniform capacity of the genuine doubled reflected-Hodge carrier.  The
constant is exactly twice the orbit-normalized bound because this norm
counts both ordered orientations.
-/
theorem reflectedHodgeCountertransportCapacity_le
    {n : ℕ} (hn : 0 < n) :
    reflectedHodgeCountertransportCapacity n ≤ 200 * 289 ^ 2 := by
  rw [reflectedHodgeCountertransportCapacity_eq hn]
  have hcapacity := cofinalDepthCountertransportCapacity_le hn
  nlinarith

/-- Complete singular depth readout is still exactly the original
two-scale current. -/
theorem cofinalDepthCountertransport_readout_eq
    {n : ℕ} (_hn : 0 < n) :
    ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
        ∑ q ∈ suzukiMangoldtFivePrimeBlock
            (PrimitivePromotedTwoScale.sourceDilation * n),
          ∑ r : Fin (primeDepthMultiplicity p),
            ∑ s : Fin (primeDepthMultiplicity q),
              landedDepthPairProfile n p q r s =
      PrimitivePromotedTwoScale.anchoredTwoScaleEnergy n := by
  unfold PrimitivePromotedTwoScale.anchoredTwoScaleEnergy
  calc
    ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
        ∑ q ∈ suzukiMangoldtFivePrimeBlock
            (PrimitivePromotedTwoScale.sourceDilation * n),
          ∑ r : Fin (primeDepthMultiplicity p),
            ∑ s : Fin (primeDepthMultiplicity q),
              landedDepthPairProfile n p q r s =
        ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
          ∑ q ∈ suzukiMangoldtFivePrimeBlock
              (PrimitivePromotedTwoScale.sourceDilation * n),
            2 * PrimitivePromotedTwoScale.anchoredCrossPair n p q := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      exact sum_landedDepthPairProfile
        (n := n) (p := p) (q := q)
        (mem_suzukiMangoldtFivePrimeBlock.mp hp).1.one_lt
        (mem_suzukiMangoldtFivePrimeBlock.mp hq).1.one_lt
    _ = 2 *
        ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
          ∑ q ∈ suzukiMangoldtFivePrimeBlock
              (PrimitivePromotedTwoScale.sourceDilation * n),
            PrimitivePromotedTwoScale.anchoredCrossPair n p q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]

/--
Uniform carrier capacity forces singular scalar readout.  Any nonnegative
gain controlling the finite two-scale readout by the square root of the
carrier capacity grows at least linearly.
-/
theorem scalarReadoutGain_linear_lower
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ))
    {gain : ℝ} (hgain : 0 ≤ gain)
    (hreadout :
      PrimitivePromotedTwoScale.anchoredTwoScaleEnergy n ≤
        gain * Real.sqrt (cofinalDepthCountertransportCapacity n)) :
    (10 / 289 : ℝ) * n ≤ gain := by
  have hnPos : 0 < n := by
    have : (0 : ℝ) < n := (Real.exp_pos 20).trans_le hn
    exact_mod_cast this
  have hcapNonneg :=
    cofinalDepthCountertransportCapacity_nonneg n
  have hcapUpper :=
    cofinalDepthCountertransportCapacity_le hnPos
  have hsqrtSq :
      Real.sqrt (cofinalDepthCountertransportCapacity n) ^ 2 =
        cofinalDepthCountertransportCapacity n :=
    Real.sq_sqrt hcapNonneg
  have hsqrtUpper :
      Real.sqrt (cofinalDepthCountertransportCapacity n) ≤
        10 * 289 := by
    nlinarith [Real.sqrt_nonneg
      (cofinalDepthCountertransportCapacity n)]
  have henergy :=
    PrimitivePromotedTwoScale.anchoredTwoScaleEnergy_linear_lower hn
  have hmul :
      gain * Real.sqrt (cofinalDepthCountertransportCapacity n) ≤
        gain * (10 * 289) :=
    mul_le_mul_of_nonneg_left hsqrtUpper hgain
  nlinarith

/-! ## Actual cell-incidence realization -/

/-- Canonical shifted cross-prime defect/packet exterior carrier. -/
def shiftedCrossPrimeDepthCarrier
    {p q : Nat.Primes} (_hpq : p ≠ q)
    (e f r s : ℕ) :
    ⋀[ℂ]^2 XiGammaEulerCalderonWittCellDegreeOne :=
  exteriorPower.ιMulti ℂ 2
    ![
      DirectSum.lof ℂ XiGammaEulerCalderonWittCell
        (fun re => DeningerCalderonWittAlgebraicDegreeOne re.1)
        (p, e + r) (deningerCalderonWittUnitDefect p, 0),
      DirectSum.lof ℂ XiGammaEulerCalderonWittCell
        (fun re => DeningerCalderonWittAlgebraicDegreeOne re.1)
        (q, f + s) (0, deningerCalderonWittAlgebraicUnitPacket q)]

theorem shiftedCrossPrimeDepthCarrier_mem_incidence
    {p q : Nat.Primes} (hpq : p ≠ q)
    (e f r s : ℕ) :
    shiftedCrossPrimeDepthCarrier hpq e f r s ∈
      xiGammaEulerCalderonWittCellMilnorIncidence := by
  apply xiGammaEulerCalderonWittCrossCell_mem_milnorIncidence
  · intro hcell
    exact hpq (Prod.mk.inj hcell).1

theorem shiftedCrossPrimeDepthCarrier_green
    {p q : Nat.Primes} (hpq : p ≠ q)
    (e f r s : ℕ) :
    (xiGammaEulerCalderonWittCellMilnorGreenRetraction
        (shiftedCrossPrimeDepthCarrier hpq e f r s) :
      ⋀[ℂ]^2 XiGammaEulerCalderonWittCellDegreeOne) =
      shiftedCrossPrimeDepthCarrier hpq e f r s := by
  rw [xiGammaEulerCalderonWittCellMilnorGreenRetraction_coe]
  have hcup :
      xiGammaEulerCalderonWittCellExteriorCup
          (shiftedCrossPrimeDepthCarrier hpq e f r s) = 0 :=
    shiftedCrossPrimeDepthCarrier_mem_incidence hpq e f r s
  rw [hcup, map_zero, sub_zero]

/-- Finite actual-depth countertransport of one recorded cross-prime
incidence carrier. -/
def sourceNormalDepthSpreadCarrier
    {p q : Nat.Primes} (hpq : p ≠ q)
    (e f : ℕ) (N M : ℕ) (w : ℂ) :
    xiGammaEulerCalderonWittCellMilnorIncidence :=
  ∑ r ∈ Finset.range N, ∑ s ∈ Finset.range M,
    (((criticalDepthDeattenuation (p, e) r *
        criticalDepthDeattenuation (q, f) s : ℝ) : ℂ) *
      (w / ((N : ℂ) * (M : ℂ)))) •
        ⟨shiftedCrossPrimeDepthCarrier hpq e f r s,
          shiftedCrossPrimeDepthCarrier_mem_incidence hpq e f r s⟩

/-- The depth-spread carrier remains exact cell incidence. -/
theorem sourceNormalDepthSpreadCarrier_mem_incidence
    {p q : Nat.Primes} (hpq : p ≠ q)
    (e f : ℕ) (N M : ℕ) (w : ℂ) :
    (sourceNormalDepthSpreadCarrier hpq e f N M w :
        ⋀[ℂ]^2 XiGammaEulerCalderonWittCellDegreeOne) ∈
      xiGammaEulerCalderonWittCellMilnorIncidence := by
  exact (sourceNormalDepthSpreadCarrier hpq e f N M w).property

/-- Green contraction fixes the complete depth-nonlocal carrier. -/
theorem sourceNormalDepthSpreadCarrier_green
    {p q : Nat.Primes} (hpq : p ≠ q)
    (e f : ℕ) (N M : ℕ) (w : ℂ) :
    (xiGammaEulerCalderonWittCellMilnorGreenRetraction
        (sourceNormalDepthSpreadCarrier hpq e f N M w :
          ⋀[ℂ]^2 XiGammaEulerCalderonWittCellDegreeOne)) =
      sourceNormalDepthSpreadCarrier hpq e f N M w := by
  apply Subtype.ext
  rw [xiGammaEulerCalderonWittCellMilnorGreenRetraction_coe]
  have hcup :
      xiGammaEulerCalderonWittCellExteriorCup
          (sourceNormalDepthSpreadCarrier hpq e f N M w :
            ⋀[ℂ]^2 XiGammaEulerCalderonWittCellDegreeOne) = 0 :=
    (sourceNormalDepthSpreadCarrier hpq e f N M w).property
  rw [hcup, map_zero, sub_zero]

end PrimitivePromotedCofinalDepth
end RHTower
