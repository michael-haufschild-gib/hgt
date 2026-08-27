import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicUnsquaredSourceOrientationRigidity

/-!
# Peierls-response odd-charge classification for reflected BM currents

For arbitrary divisor-dependent response correction `K`, the corrected reflected BM current is
exactly minus the sum of composite charges

`H(q) = A(q) K(q) λ(q)`,

where `A` is literal unsquared angular--Einstein source amplitude and `λ` the exact BM complementary
exponent.  Thus corrected cancellation is equivalent, pointwise and globally, to reflection oddness
of `H`.

Oddness by itself contains no RH force.  Dividing Xi height by `A(q)λ(q)` produces a canonical
pointwise correction: its charge is height off the critical wall and zero on the wall.  This charge
is reflection-odd, so corrected current cancels on every Xi fibre unconditionally.  The construction
is singular across vanishing source wall and identifies exact remaining physical gate: augmented
Peierls response must obey analytic/causal regularity excluding such divisorwise division.

`[NEW] [CLASSIFICATION] [COUNTERMODEL] [NO-GO] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex Real Set

namespace RHTower

noncomputable section

/-- Literal unsquared angular--Einstein source amplitude at unit seed. -/
def d4BMXiSecondHarmonicUnitUnsquaredSourceAmplitude (q : XiZeroCopy) : ℂ :=
  d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q

/-- Composite incidence charge carried by source, response correction, and radial exponent. -/
def d4BMXiSecondHarmonicPeierlsResponseCharge
    (n : ℕ) (correction : XiZeroCopy → ℂ) (q : XiZeroCopy) : ℂ :=
  d4BMXiSecondHarmonicUnitUnsquaredSourceAmplitude q * correction q *
    d4BMXiPlusPlusComplementaryExponent n q

/-- Reflection-paired BM current with an arbitrary divisor-dependent response correction. -/
def d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent
    (n : ℕ) (correction : XiZeroCopy → ℂ) (q : XiZeroCopy) : ℂ :=
  d4BMXiReflectionComplexWeightedRegularComplementaryCurrent n q
    (d4BMXiSecondHarmonicUnitUnsquaredSourceAmplitude q * correction q)
    (d4BMXiSecondHarmonicUnitUnsquaredSourceAmplitude (xiZeroCopyReflectEquiv q) *
      correction (xiZeroCopyReflectEquiv q))

/-- Exact charge factorization of every response-corrected reflected BM current. -/
theorem d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_neg_charge_add
    (n : ℕ) (correction : XiZeroCopy → ℂ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent n correction q =
      -(d4BMXiSecondHarmonicPeierlsResponseCharge n correction q +
        d4BMXiSecondHarmonicPeierlsResponseCharge n correction
          (xiZeroCopyReflectEquiv q)) := by
  have hz0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hz1 : (1 / 2 : ℝ) < 1 := by norm_num
  rw [d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent,
    d4BMXiReflectionComplexWeightedRegularComplementaryCurrent,
    d4BMSecondHarmonicRegularComplementaryPolarizedCurrentValue_eq_negExponent n
      (d4BMXiMixedHorizonAngularMomentum q)
      (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q) hz0 hz1,
    d4BMSecondHarmonicRegularComplementaryPolarizedCurrentValue_eq_negExponent n
      (d4BMXiMixedHorizonAngularMomentum (xiZeroCopyReflectEquiv q))
      (d4BMXiMixedHorizonAngularMomentum_re_ne_zero (xiZeroCopyReflectEquiv q)) hz0 hz1]
  unfold d4BMXiSecondHarmonicPeierlsResponseCharge
    d4BMXiPlusPlusComplementaryExponent
  ring

/-- Corrected reflection current cancels exactly when composite response charge is odd. -/
theorem d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_zero_iff
    (n : ℕ) (correction : XiZeroCopy → ℂ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent n correction q = 0 ↔
      d4BMXiSecondHarmonicPeierlsResponseCharge n correction
          (xiZeroCopyReflectEquiv q) =
        -d4BMXiSecondHarmonicPeierlsResponseCharge n correction q := by
  rw [d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_neg_charge_add]
  constructor <;> intro h
  · have h' := neg_eq_zero.mp h
    linear_combination h'
  · apply neg_eq_zero.mpr
    linear_combination h

/-- Universal corrected cancellation is precisely reflection oddness of composite charge. -/
theorem forall_d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_zero_iff_odd
    (n : ℕ) (correction : XiZeroCopy → ℂ) :
    (∀ q : XiZeroCopy,
      d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent n correction q = 0) ↔
      ∀ q : XiZeroCopy,
        d4BMXiSecondHarmonicPeierlsResponseCharge n correction
            (xiZeroCopyReflectEquiv q) =
          -d4BMXiSecondHarmonicPeierlsResponseCharge n correction q := by
  constructor <;> intro h q
  · exact (d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_zero_iff
      n correction q).mp (h q)
  · exact (d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_zero_iff
      n correction q).mpr (h q)

/-- Canonical pointwise correction obtained by dividing the Xi height charge by source and exponent. -/
def d4BMXiSecondHarmonicPuncturedHeightResponseCorrection
    (n : ℕ) (q : XiZeroCopy) : ℂ :=
  ((q.1 : ℂ).im : ℂ) /
    (d4BMXiSecondHarmonicUnitUnsquaredSourceAmplitude q *
      d4BMXiPlusPlusComplementaryExponent n q)

/-- Punctured-height correction produces height charge off wall and zero charge on wall. -/
theorem d4BMXiSecondHarmonicPuncturedHeightResponseCharge_eq
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicPeierlsResponseCharge n
        (d4BMXiSecondHarmonicPuncturedHeightResponseCorrection n) q =
      if (q.1 : ℂ).re = 1 / 2 then 0 else ((q.1 : ℂ).im : ℂ) := by
  by_cases hline : (q.1 : ℂ).re = 1 / 2
  · have hmix : d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q = 0 :=
      (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_zero_iff q).mpr hline
    simp [d4BMXiSecondHarmonicPeierlsResponseCharge,
      d4BMXiSecondHarmonicPuncturedHeightResponseCorrection,
      d4BMXiSecondHarmonicUnitUnsquaredSourceAmplitude,
      d4BMXiSecondHarmonicPolarizedSourceAmplitude, hline, hmix]
  · have hmix : d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q ≠ 0 :=
      (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_zero_iff q).not.mpr hline
    have hcarrier :
        d4ThetaHawkingSelfDualQuadraticCarrierCoefficient 1 (xiSpectralPoint q) ≠ 0 :=
      d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_ne_zero one_ne_zero q
    have hamp : d4BMXiSecondHarmonicUnitUnsquaredSourceAmplitude q ≠ 0 := by
      exact mul_ne_zero hmix hcarrier
    have hexp := d4BMXiPlusPlusComplementaryExponent_ne_zero n q
    rw [if_neg hline]
    unfold d4BMXiSecondHarmonicPeierlsResponseCharge
      d4BMXiSecondHarmonicPuncturedHeightResponseCorrection
    field_simp [hamp, hexp]

/-- Punctured-height composite charge is reflection-odd unconditionally. -/
theorem d4BMXiSecondHarmonicPuncturedHeightResponseCharge_reflection_odd
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicPeierlsResponseCharge n
        (d4BMXiSecondHarmonicPuncturedHeightResponseCorrection n)
        (xiZeroCopyReflectEquiv q) =
      -d4BMXiSecondHarmonicPeierlsResponseCharge n
        (d4BMXiSecondHarmonicPuncturedHeightResponseCorrection n) q := by
  rw [d4BMXiSecondHarmonicPuncturedHeightResponseCharge_eq,
    d4BMXiSecondHarmonicPuncturedHeightResponseCharge_eq]
  have hlineRef :
      ((xiZeroCopyReflectEquiv q).1 : ℂ).re = 1 / 2 ↔
        (q.1 : ℂ).re = 1 / 2 := by
    constructor
    · intro h
      have hm := (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_zero_iff
        (xiZeroCopyReflectEquiv q)).mpr h
      rw [d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_reflect] at hm
      exact (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_zero_iff q).mp hm
    · intro h
      apply (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_zero_iff
        (xiZeroCopyReflectEquiv q)).mp
      rw [d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_reflect]
      exact (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_zero_iff q).mpr h
  have href : ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) :=
    xiZeroReflectEquiv_apply q.1
  have himref : ((xiZeroCopyReflectEquiv q).1 : ℂ).im = -(q.1 : ℂ).im := by
    rw [href]
    simp
  by_cases hline : (q.1 : ℂ).re = 1 / 2
  · rw [if_pos hline, if_pos (hlineRef.mpr hline)]
    simp
  · rw [if_neg hline, if_neg (hlineRef.not.mpr hline)]
    exact_mod_cast himref

/-- Oddness alone is too weak: canonical pointwise correction cancels every Xi fibre unconditionally. -/
theorem forall_d4BMXiSecondHarmonicPuncturedHeightResponseCorrectedReflectionCurrent_eq_zero
    (n : ℕ) :
    ∀ q : XiZeroCopy,
      d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent n
        (d4BMXiSecondHarmonicPuncturedHeightResponseCorrection n) q = 0 := by
  intro q
  exact (d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_zero_iff n
    (d4BMXiSecondHarmonicPuncturedHeightResponseCorrection n) q).mpr
      (d4BMXiSecondHarmonicPuncturedHeightResponseCharge_reflection_odd n q)

end

end RHTower
