# Constrained-prolate ground reversed Gamma-recurrence/Xi universality law

## Status

`[LEAN PROVED — LITERATURE AUDITED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`

## Lean-derived statement

Normalize both dominant theta-source and Liouville--Gibbs fixed-Gamma coordinates by the actual
constrained-prolate ground scale. Then:

- normalized source coordinates are exactly constrained-prolate ground raw even moments;
- the exact Liouville--Ward bridge is unchanged;
- every positive-order sharp equipartition recurrence reverses direction;
- its rational recurrence also reverses direction;
- the theta upper half-density budget becomes a constrained-prolate lower budget;
- the global Fourier transform remains the same negative normalization of completed Xi.

## Corpus inputs

- `constrainedProlateGroundHermiteXiScale_neg`
- `constrainedProlateGroundHermiteAtomRawEvenMoment_eq_scale_mul_theta`
- `thetaCuspFirstAtom_sourceGammaCoordinate_eq_rawEvenMoment`
- `thetaCuspFirstAtom_fixedGamma_liouvilleWardBridge`
- `thetaCuspFirstAtom_fixedGamma_equipartitionRecurrence`
- `thetaCuspFirstAtom_fixedGamma_rationalRecurrence`
- `constrainedProlateGroundHermiteFirstAtom_halfDensityLowerBudget`
- `fourier_constrainedProlateGroundHermiteSchwartz_scaled`

No numerical computation or external premise is used.

## Paper proof

Write `s` for `constrainedProlateGroundHermiteXiScale`, `S_j` for the theta source Gamma
coordinate, and `G_k` for the theta Gibbs Gamma coordinate. Define normalized coordinates

```text
S'_j = s S_j,  G'_k = s G_k.
```

The corpus proves `s < 0`. The source evaluation and Ward bridge are equalities, so multiplication
by `s` preserves them and yields the normalized source-moment identity and normalized Ward bridge.
The theta recurrence is

```text
4 pi G_(k+1) + (2 pi - 5/2) G_k <= k G_(k-1).
```

Multiplication by `s < 0` reverses the inequality:

```text
k G'_(k-1) <= 4 pi G'_(k+1) + (2 pi - 5/2) G'_k.
```

The identical argument reverses `12 G_(k+1) <= k G_(k-1)`. Existing scale transport gives the
lower budget and exact Xi Fourier realization.

## Hostile subsumption audit

- The constrained-prolate parent contains source moments, Ward transport, lower budget, and Xi
  transform, but no recurrence for any constrained Gibbs coordinate.
- The theta fixed-Gamma parent contains the recurrence, but no constrained-prolate state, negative
  scale, reversed inequality, or Xi Fourier realization.
- The connector is not a conjunction wrapper: strict negativity changes the order direction, so
  the theorem produces new inequalities for newly identified constrained-prolate coordinates.
- Whole-corpus search found no constrained-prolate Gamma recurrence or normalized constrained
  Gibbs coordinate.

## Lean verification

Formal module:

```text
formal/GaloisForLFunctions/RHTower/ConstrainedProlateGroundReversedGammaRecurrenceXiUniversalityLaw.lean
```

Required exact check passed:

```text
lake env lean GaloisForLFunctions/RHTower/ConstrainedProlateGroundReversedGammaRecurrenceXiUniversalityLaw.lean
```

The module is imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Post-proof literature boundary

Searches were run only after the Lean theorem passed. Closest located sources were:

- Dan Romik, *Orthogonal polynomial expansions for the Riemann xi function*, arXiv:1902.06330,
  which studies Xi in Hermite and other orthogonal-polynomial bases, including coefficient signs
  and Fourier-flow structure;
- Alain Connes and Henri Moscovici, *Prolate spheroidal operator and Zeta*, arXiv:2112.05500, and
  Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*, arXiv:2310.18423, which
  relate prolate/Sonin spectral geometry to zeta zeros;
- NIST DLMF §8.8, which records standard incomplete-Gamma recurrences.

No located source states the exact combined law: normalize the theta source and Liouville--Gibbs
fixed-half-line Gamma coordinates by the negative constrained-prolate ground Xi scale, thereby
reverse both equipartition inequalities while preserving the Ward identity, signed endpoint
budget, and exact completed-Xi Fourier realization. Negative search is not proof of priority;
specialist review remains required.

## Gates

- [x] whole-corpus source search
- [x] exact conjecture stated from theorem interfaces
- [x] dependency-closed paper proof
- [x] hostile corpus-subsumption audit
- [x] Lean exact check
- [x] umbrella wiring
- [x] post-proof literature audit
- [ ] final axiom/lint/build audit
