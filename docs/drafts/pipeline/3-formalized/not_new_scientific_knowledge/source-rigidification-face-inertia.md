# Source rigidification and face-created inertia

- **ID:** `source-rigidification-face-inertia`
- **Stage:** 3-formalized
- **Type:** EXACT SOURCE DATA-PROCESSING NO-GO / ARBITRARY-RANK POSITIVE SUCCESSOR
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [PARENT BRIDGE]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH RESULT]`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/SourceRigidificationFaceInertia.lean`
- **Successor:**
  `../../1-in-progress/hypertranscendental-source-face-vanishing-cycle-conservation.md`

## Exact no-go: source-only data processing has zero reconstruction gain

Let `S` be a commuting difference-differential source and let

```text
Q_S(x)=((sigma_i-1)x)_i
```

be its complete additive boundary.  Suppose every reporter is source-derived in the exact sense

```text
R_r=P_r o Q_S.                                               (1)
```

For the augmented observation

```text
Obs_P(x)=(Q_S(x),(R_r(x))_r),                                (2)
```

Lean proves

```text
Obs_P(x)=Obs_P(y)  iff  x-y is fixed by every sigma_i,        (3)
Obs_P injective    iff  Q_S injective.                        (4)
```

Thus no family of linear source-only completions refines even one fibre of the bare source.  This
is stronger than saying that a particular completion fails: source factorization itself forces
every reporter to vanish on the residual joint-fixed gauge.

## Strong positive successor: a source face creates arbitrary-rank inertia

Let

```text
e_m(z)=exp(2 pi i m z),   m>=1,
```

and let `tau` have nonzero imaginary part.  For every finite `k`, put

```text
V_k=span_C{e_1,...,e_k}.                                    (5)
```

Lean proves the stronger coefficient-level statement:

```text
dim V_k=k,
every f in V_k is 1-periodic,
f in V_k and f is tau-periodic  implies  f=0.                (6)
```

The proof is spectral.  Translation by `tau` acts on `e_m` by the distinct nonunit-modulus
eigenvalue `exp(2 pi i tau)^m`; no positive power is one when `Im(tau)` is nonzero.  Linear
independence of the exponential modes then excludes every nonzero packet.

Consequently, deleting the `tau`-translation creates a `k`-dimensional boundary-only gauge space
for every `k`.  A source face can therefore create normalization inertia of unbounded finite rank;
the loss of one source constraint is not merely the loss of one scalar equation.

## Exact synthesis

Equations `(3)`--`(6)` expose two logically separate facts.

1. At a fixed source, source-derived observation cannot see the stabilizer already forgotten by
   that source.
2. Under degeneration, the stabilizer itself can jump from the generic source to the boundary
   source by arbitrarily large rank.

The correct higher object must therefore retain the comparison

```text
generic joint-fixed gauge  ->  boundary joint-fixed gauge,   (7)
```

not only the boundary observation on either fibre.  Its kernel records gauge death and its
cokernel records gauge birth.  This is the exact seed of the conjectural
rigidification--specialization commutator; no such derived commutator is proved here.

## Novelty and anti-theatre gate

- `[NOVELTY -- PARENT]` Factorization through a quotient cannot recover quotient fibres; finite
  Fourier modes and their translation eigenvalues are classical.
- `[ANTI-THEATRE -- PASS]` The bridge is not promoted as a discovery.  Its purpose is to force the
  new field-level conjecture to calculate a jumping stabilizer rather than merely rename a kernel.
- `[SIGNIFICANCE -- LOAD-BEARING POSITIVE BRIDGE]` Arbitrary-rank gauge birth is the first exact
  model showing that a thin source face can carry unbounded normalization capacity.
- `[RH BOUNDARY]` No zeta function, Xi divisor, critical zero, or positivity claim occurs.

## Lean certificate

Principal declarations:

- `familySourceFactorizedBoundaryFingerprint_eq_iff`;
- `familySourceFactorizedBoundaryFingerprint_injective_iff`;
- `gammaPositivePeriodicFourierPacket_periodic`;
- `gammaPositivePeriodicFourierPacket_not_periodic_of_im_ne_zero`;
- `nonreal_sourceFace_arbitraryPositiveGaugeBirth`.

The exact module cache target was built once because its `.olean` was missing.  The touched source
then passed direct `lake env lean` verification.  No full or area build was run.

## Gates

- [x] source-factorized reporter family defined
- [x] exact equality fibre proved unchanged
- [x] exact injectivity equivalence proved
- [x] positive Fourier packet space proved linearly independent
- [x] every nonzero positive packet proved boundary-only for a nonreal deleted shift
- [x] unconditional Lean formalization
- [ ] construct the generic-to-face stabilizer map for an actual elliptic-gamma family
- [ ] identify its cokernel with the boundary-normal character filtration
