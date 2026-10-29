# All-level payment for every cube and higher prime power

## Theorem and actual source

For each prime p and exponent r>=3, retain the literal critical Euler
coefficient 2 log(p)/p^(r/2) and the physical translation by r log(p).
Their total coefficient mass H is finite across all primes and exponents.
The complete correlation contribution is absolutely convergent on whole-line
L2. For every original compact real BV profile and A>=1, the sum of absolute
coefficientwise changes after removing Q_A f is at most

96 H Gamma(f)/(1+log A), where Q_A=U(1-P_A)U*.

The complete source and every finite prime-power selection satisfy the same
bound. For actual finite cell profiles, f-Q_A f=U P_A U* f. One cutoff
A>exp(96 H/delta) pays delta Gamma(f) simultaneously for every profile,
horizon and finite selection. All retained generator families keep their
entire translation orbits. The estimate precedes any cancellation between
Euler terms.

## Arithmetic boundary

For every natural r, the tail beginning at exponent r+1 is summable
exactly when r>=2. Summability of the first exponent slice would imply
summability of p^(-(r+1)/2), because log(p)>=log(2)>0. The corpus's exact
prime Dirichlet threshold forces r>=2. The positive direction is a tail
reindexing of the existing all-prime cube-and-higher summability theorem.

This classifies the absolute coefficient method. It does not show that the
actual prime or square correlation sums diverge on compact sources, nor
does it rule out signed cancellation or the square-pole compensation.
The positive survivor is the complete all-prime higher-power correlation
with one original-source Gamma budget across every dyadic level.

## Mathematical mechanism

The uniform real-lag error is96 Gamma(f)/(1+log A). Absolute coefficient
summability gives absolute convergence on whole-line L2 before any infinite
correlations are subtracted. Original real BV correlation integrals are
identified term by term. Every finite coefficient selection has mass at
most H, so one reserve pays the directed exhaustion and its limit.

Corpus inputs: EveryTranslationHasAnAllLevelGammaTailBound;
AllHigherPrimePowerMixedTailsAreGammaSmall for the actual coefficient
identity; XiMassPrimePowerVerticalIdeal for double summability;
RandomEulerAbscissa for the prime Dirichlet threshold.
## Lean formalization and audit

- [CriticalEulerCoefficientMassStartsAtCubes.lean](../../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/CriticalEulerCoefficientMassStartsAtCubes.lean):
  `criticalEulerTailWeight_eq`, `summable_criticalEulerTailWeight_iff`,
  `not_summable_criticalPrimeCoefficients`, `not_summable_criticalSquareCoefficients`.
- [AllHigherPrimePowersHaveAllLevelGeneratorApproximation.lean](../../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/AllHigherPrimePowersHaveAllLevelGeneratorApproximation.lean):
  `summable_norm_wholeLineHigherEuler`, `hasSum_wholeLineHigherEuler`,
  `tsum_abs_higherEuler_head_error_le`,
  `abs_wholeLineHigherEulerTruncation_head_error_le`,
  `summable_norm_original_higherEuler_integrals`,
  `abs_wholeCell_higherEuler_head_error_le`,
  `exists_allPrimeHigherEuler_allLevel_generator_approximation`.

Both final individual no-olean Lean checks pass. Printed transitive
capstone dependencies contain only `propext`, `Classical.choice`, `Quot.sound`.
The negative coefficient classification and its exact positive survivor
are both formalized. No projected-source Gamma estimate is assumed.

## Remaining boundary

Prime and square layers, full Gamma/pole transfer and retained-orbit signs
remain outside this theorem. General BV inputs retain their noncell
component after removing the high-generator projection.
