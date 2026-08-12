# Hedenmalm theta prime anomaly Haar cyclicity

- **ID:** `hedenmalm-theta-prime-anomaly-haar-cyclicity`
- **Stage:** 1-in-progress
- **Label:** `P-G107`
- **Type:** `[CONJECTURE LOOP] [ROUTE-P CARRIER CLASSIFICATION] [NO COMPUTATION]`
- **Parents:** `HedenmalmThetaPrimeTranslationHaarCarrier.lean`,
  `HedenmalmThetaPrimeQuantileHaarCarrier.lean`, `HedenmalmThetaIntervalTransform.lean`,
  `XiThetaL2Cyclicity.lean`

## Frozen conjecture

For every integer `n >= 2`, let `r_n` be the coefficient-one source anomaly of normalized
integer translation. Prove:

1. `r_n` is an honest nonzero vector of `L1(R) intersection L2(R)`; `[LEAN-PROVED upstream]`
2. its unitary Fourier profile is almost everywhere

   ```text
   shiftMultiplier(n,-2 pi t) XiC(-2 pi t);
   ```

3. that profile is nonzero almost everywhere, because both zero sets are countable;
4. the complete real-translation orbit of `r_n` is cyclic in Haar `L2(R)`;
5. consequently every continuous linear quotient on a carrier with dense Haar-`L2` image that
   kills all translates of `r_n` is zero.

At every retained Xi divisor, the same nonzero `r_n` is killed by the divisor conormal. Thus the
divisor reporter cannot extend continuously to the forced Haar carrier. The common-forcing
equation lives across a genuine rigging boundary: its physical forcing is cyclic in the bulk and
simultaneously zero in every divisor fibre.

## Conjecture loop audit

- Fixed-prime Haar--bilateral orbit decomposition was rejected as the main result: the corpus
  already proves that ambient prime dilation is a constant-multiplicity bilateral shift with no
  point spectrum.
- Ordinary theta-source Haar cyclicity is already formalized and is not new.
- The surviving source-specific statement concerns the *prime anomaly itself*. Its transform has
  the extra prime multiplier, so cyclicity is not automatic from source cyclicity until the
  multiplier's real zero set is audited.
- The result cannot imply RH alone: countable divisor holes are invisible to ordinary `L2`.
  Its positive content is a classification of the only carrier category in which the remaining
  Route-P quotient can live.

## Significance gate

P-G103--P-G106 force prime covariance onto a sigma-finite Haar carrier. P-G107 would prove that
no regular Hausdorff completion of that carrier can retain the common-forcing divisor quotient.
Therefore the next producer must be a singular/rigged conormal carrier where analytic point
evaluation is continuous although ordinary Haar `L2` is not dense. This removes all continuous
Hilbert-quotient variants of the response-identification proposal at once.

## Falsifiers

- If the Fourier profile has a positive-measure zero set, the anomaly is not cyclic.
- If the exact Fourier normalization differs from `-2 pi t`, the displayed profile must be
  corrected before any cyclicity claim.
- If a nonzero continuous reporter on a dense Haar completion kills the anomaly orbit, the
  collapse theorem is false.

## Gates

- [x] prior Route P, Haar cyclicity, and bilateral no-point-spectrum corpus audited
- [x] conjecture frozen
- [ ] exact L1/L2 Fourier profile proved
- [ ] multiplier zero set proved countable/null
- [ ] anomaly translation orbit proved cyclic
- [ ] continuous quotient collapse proved
- [ ] umbrella, direct Lean, lint, and axiom audits pass

## Lean status

Planned module:
`formal/GaloisForLFunctions/RHTower/HedenmalmThetaPrimeAnomalyHaarCyclicity.lean`.
