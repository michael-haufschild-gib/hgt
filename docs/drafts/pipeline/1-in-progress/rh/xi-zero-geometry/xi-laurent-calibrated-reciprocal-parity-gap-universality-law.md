# Xi Laurent–calibrated reciprocal parity-gap universality law

Status: **Stage 3 — formalised in Lean 4**

## Discovery

Whole-corpus reusable-symbol posting joined:

- `XiCenteredReciprocalLaurentParitySourceUniversalityLaw`, which identifies every even
  signed centered Laurent trace with the corresponding central Xi/source moment and annihilates
  every adjacent odd trace; and
- `ThetaCuspCassiniCalibratedReciprocalMomentNoGo`, which proves that the calibrated
  reciprocal theta carrier's first moment strictly exceeds `normalizedPrimeArchMoment 1`.

The join is theorem-generated: no target law was selected before reading both terminal modules.

## Universal law

For every depth `m`, the signed centered reciprocal Xi Laurent coordinate is absolutely summable
at order `2m+3` and its trace vanishes. At the first nontrivial reciprocal-moment degree,

`Re (xiCenteredReciprocalLaurentTrace 4)
  < ∫ x, x ∂thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure`.

Simultaneously the order-two Laurent trace is strictly positive and the order-five trace is zero.
Thus the calibrated positive reciprocal carrier cannot represent the parity-restored signed Xi
Laurent tower: its first positive-degree mismatch sits between exact even/odd spectral channels.

## Dependency-closed paper proof

1. `summable_xiCenteredReciprocalLaurentCoordinate_pow (2*m+3)` gives absolute summability.
2. `xiCenteredReciprocalLaurentTrace_odd_eq_zero m` gives every odd vacuum.
3. `xiCenteredReciprocalLaurentTrace_lowEvenPos_oddZero 0` gives positivity at order two.
4. At `m = 1`,
   `xiCenteredReciprocalLaurentTrace_even_eq_centralMoment` identifies order four with
   `xiCentralReciprocalMoment 1`.
5. `normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment 1` identifies its real part with
   `normalizedPrimeArchMoment 1`.
6. Apply
   `normalizedPrimeArchMoment_one_lt_thetaCuspCassiniCalibratedReciprocal_firstMoment`.
7. `xiCenteredReciprocalLaurentTrace_odd_eq_zero 1` gives the adjacent order-five vacuum.

No RH assumption, numerical evaluation, or new analytic input enters.

## Formal target

`xiLaurent_calibratedReciprocalParityGapUniversality`

## Novelty audit

Post-proof arXiv and HAL searches found literature on Li coefficients, reciprocal sums over zeta
zeros, theta/Fourier representations of Xi, and generic moment problems. No result located combines
the exact centered signed Laurent parity tower with the calibrated reciprocal Cassini likelihood
carrier or proves this strict order-four carrier gap. Novelty claim remains scoped to this search.

## Lean status

Formalised in
`formal/GaloisForLFunctions/RHTower/XiLaurentCalibratedReciprocalParityGapUniversalityLaw.lean`
and imported by `formal/GaloisForLFunctions/RHTower.lean`.

Exact-file check:

`lake env lean GaloisForLFunctions/RHTower/XiLaurentCalibratedReciprocalParityGapUniversalityLaw.lean`

passed with no diagnostics.
