import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCrossPairResponseCompensator

/-!
# Source-independent scalar response dichotomy

HC19 shows that even a division-free response can cancel every Xi fibre when it is allowed to
match the reflected source. This module proves the exact complementary classification for a fixed
scalar response independent of the Xi divisor.

The corrected current with constant response `c` is exactly `c` times the literal unsquared-source
current. Therefore its pointwise zero locus is

`c = 0 ∨ Re(q) = 1/2`,

and its universal zero law is exactly

`c = 0 ∨ RH`.

Thus zero response is the unique blind fixed scalar branch; every nonzero fixed response retains
full RH force. At unit response its Ward identity is equivalent to canonical Peierls--Darboux
optical darkness.

`[NEW] [EXACT DICHOTOMY] [SOURCE-INDEPENDENT CLASSIFICATION] [RH EQUIVALENCE] [LEAN-PROVED]`
-/

open Complex Real Set

namespace RHTower

noncomputable section

/-- Divisor-independent scalar response correction. -/
def d4BMXiSecondHarmonicSourceIndependentResponseCorrection
    (c : ℂ) : XiZeroCopy → ℂ :=
  fun _ => c

/-- Reflected BM current with one fixed scalar response on every Xi divisor. -/
def d4BMXiSecondHarmonicSourceIndependentResponseCurrent
    (n : ℕ) (c : ℂ) (q : XiZeroCopy) : ℂ :=
  d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent n
    (d4BMXiSecondHarmonicSourceIndependentResponseCorrection c) q

/-- A fixed scalar response factors completely out of the physical unsquared-source current. -/
theorem d4BMXiSecondHarmonicSourceIndependentResponseCurrent_eq_mul
    (n : ℕ) (c : ℂ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicSourceIndependentResponseCurrent n c q =
      c * d4BMXiSecondHarmonicUnsquaredSourceReflectionCurrent n q := by
  rw [d4BMXiSecondHarmonicSourceIndependentResponseCurrent,
    d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_neg_charge_add]
  rw [d4BMXiSecondHarmonicUnsquaredSourceReflectionCurrent,
    d4BMXiReflectionComplexWeightedRegularComplementaryCurrent]
  have hz0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hz1 : (1 / 2 : ℝ) < 1 := by norm_num
  rw [d4BMSecondHarmonicRegularComplementaryPolarizedCurrentValue_eq_negExponent n
      (d4BMXiMixedHorizonAngularMomentum q)
      (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q) hz0 hz1,
    d4BMSecondHarmonicRegularComplementaryPolarizedCurrentValue_eq_negExponent n
      (d4BMXiMixedHorizonAngularMomentum (xiZeroCopyReflectEquiv q))
      (d4BMXiMixedHorizonAngularMomentum_re_ne_zero (xiZeroCopyReflectEquiv q)) hz0 hz1]
  unfold d4BMXiSecondHarmonicPeierlsResponseCharge
    d4BMXiSecondHarmonicSourceIndependentResponseCorrection
    d4BMXiSecondHarmonicUnitUnsquaredSourceAmplitude
    d4BMXiPlusPlusComplementaryExponent
  ring

/-- Exact local dichotomy: zero response is blind; otherwise zeros are precisely on the wall. -/
theorem d4BMXiSecondHarmonicSourceIndependentResponseCurrent_eq_zero_iff
    (n : ℕ) (c : ℂ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicSourceIndependentResponseCurrent n c q = 0 ↔
      c = 0 ∨ (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiSecondHarmonicSourceIndependentResponseCurrent_eq_mul, mul_eq_zero,
    d4BMXiSecondHarmonicUnsquaredSourceReflectionCurrent_eq_zero_iff]

/-- Exact global dichotomy for every fixed scalar response, with no side condition. -/
theorem forall_d4BMXiSecondHarmonicSourceIndependentResponseCurrent_eq_zero_iff
    (n : ℕ) (c : ℂ) :
    (∀ q : XiZeroCopy,
      d4BMXiSecondHarmonicSourceIndependentResponseCurrent n c q = 0) ↔
      c = 0 ∨ RiemannHypothesis := by
  constructor
  · intro h
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      apply (forall_d4BMXiSecondHarmonicUnsquaredSourceReflectionCurrent_eq_zero_iff_rh n).mp
      intro q
      have hq :=
        (d4BMXiSecondHarmonicSourceIndependentResponseCurrent_eq_zero_iff n c q).mp (h q)
      exact (hq.resolve_left hc)
        |> (d4BMXiSecondHarmonicUnsquaredSourceReflectionCurrent_eq_zero_iff n q).mpr
  · rintro (hc | hRH)
    · intro q
      rw [d4BMXiSecondHarmonicSourceIndependentResponseCurrent_eq_mul, hc, zero_mul]
    · intro q
      apply (d4BMXiSecondHarmonicSourceIndependentResponseCurrent_eq_zero_iff n c q).mpr
      right
      have hq :=
        (forall_d4BMXiSecondHarmonicUnsquaredSourceReflectionCurrent_eq_zero_iff_rh n).mpr hRH q
      exact (d4BMXiSecondHarmonicUnsquaredSourceReflectionCurrent_eq_zero_iff n q).mp hq

/-- Every nonzero fixed scalar response has universal stationarity exactly under RH. -/
theorem forall_d4BMXiSecondHarmonicSourceIndependentResponseCurrent_eq_zero_iff_rh_of_ne_zero
    (n : ℕ) (c : ℂ) (hc : c ≠ 0) :
    (∀ q : XiZeroCopy,
      d4BMXiSecondHarmonicSourceIndependentResponseCurrent n c q = 0) ↔
      RiemannHypothesis := by
  rw [forall_d4BMXiSecondHarmonicSourceIndependentResponseCurrent_eq_zero_iff,
    or_iff_right hc]

/-- Unit fixed response gives a premise-free universal RH endpoint. -/
theorem forall_d4BMXiSecondHarmonicSourceIndependentUnitResponseCurrent_eq_zero_iff_rh
    (n : ℕ) :
    (∀ q : XiZeroCopy,
      d4BMXiSecondHarmonicSourceIndependentResponseCurrent n 1 q = 0) ↔
      RiemannHypothesis := by
  rw [forall_d4BMXiSecondHarmonicSourceIndependentResponseCurrent_eq_zero_iff]
  norm_num

/-- Fixed unit response stationarity is exactly canonical Peierls--Darboux optical darkness. -/
theorem d4BMXiSecondHarmonicSourceIndependentUnitWard_iff_canonicalOpticalWard
    (n : ℕ) :
    (∀ q : XiZeroCopy,
      d4BMXiSecondHarmonicSourceIndependentResponseCurrent n 1 q = 0) ↔
      ∀ q : XiZeroCopy,
        hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q = 0 := by
  rw [forall_d4BMXiSecondHarmonicSourceIndependentUnitResponseCurrent_eq_zero_iff_rh,
    forall_hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_zero_iff_rh]

/-- A nonzero fixed response cannot cancel at any tilted Xi copy. -/
theorem d4BMXiSecondHarmonicSourceIndependentResponseCurrent_ne_zero_of_tilt
    (n : ℕ) (c : ℂ) (hc : c ≠ 0) (q : XiZeroCopy)
    (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    d4BMXiSecondHarmonicSourceIndependentResponseCurrent n c q ≠ 0 := by
  exact (d4BMXiSecondHarmonicSourceIndependentResponseCurrent_eq_zero_iff n c q).not.mpr
    (not_or_intro hc htilt)

end

end RHTower
