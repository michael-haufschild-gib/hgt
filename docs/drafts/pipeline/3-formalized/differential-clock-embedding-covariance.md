# Differential-clock embedding covariance

- **ID:** differential-clock-embedding-covariance
- **Stage:** 3-formalized
- **Type:** PROVED IN LEAN / GENERAL HYPERTRANSCENDENCE BRIDGE
- **Source:** locally covariant QFT and non-invertible quantum reference changes
- **Statement:** A derivation-preserving algebra homomorphism between fields preserves and reflects all finite jet-clock tests, hypertranscendence, and the exact HT clock-erosion law; no inverse or surjectivity hypothesis is required.

## Goal

Remove the unnecessary global inverse from the general HT clock covariance API.  Later consumers can
now transport the full finite observability structure into a larger differential field using only a
derivation-compatible embedding.  The result applies to every hypertranscendental element and is not
specific to zeta or `RHTower`.

## Gates

- [x] 0 → 1 in-progress: the invertibility premise was isolated and shown absent from the jet proofs
- [x] 1 → 2 fully-proven: covariance and reflection proved from field-hom injectivity
- [x] 2 → 3 formalized: exact-module build, direct source check, and axiom audit pass
- [ ] 3 → 4 publication-ready: supply a source-specific differential embedding consumer

## Physics source

- R. Brunetti, K. Fredenhagen, and R. Verch, *The generally covariant locality principle -- A new paradigm for local quantum physics*, arXiv:math-ph/0112041, formulates locally covariant QFT as a covariant functor from spacetime embeddings to unital injective algebra morphisms.  Covariance is therefore native along embeddings, not only automorphisms.
- A.-C. de la Hamette and T. D. Galley, *Quantum reference frames for general symmetry groups*, arXiv:2004.14292, constructs both reversible and irreversible changes of quantum reference system.
- T. Carette, J. Głowacki, and L. Loveridge, *Operational Quantum Reference Frame Transformations*, arXiv:2303.14002, shows that frame transformations are invertible only under an additional localizability condition.

The Lean theorem is an exact differential-algebraic transfer of the embedding-covariance principle.
It does not identify differential fields with QFT observable algebras or claim that every physical
irreversible channel is a field embedding.

## Exact relation

Let

```text
e : E ->_F L
```

be an `F`-algebra homomorphism between fields satisfying

```text
e(delta z) = delta'(e z).
```

Because every field homomorphism is injective, for all `n` and `N`,

```text
e(delta^n x) = delta'^n(e x),
e(P_N(x)) = P_N(e x),
delta^q z in B  iff  delta'^q(e z) in e(B).
```

Thus every finite family of clock tests is preserved and reflected.  Algebraic independence maps
forward by injectivity and reflects along composition, giving

```text
HypertranscendentalOver(F,e x)
  iff HypertranscendentalOver(F,x).
```

For hypertranscendental `x`, exact clock erosion transports without an inverse:

```text
all tests q <= r keep z inside P_(N+r)(x)
  iff e z lies in P_N(e x).
```

This is functorial observability under a static inclusion of presentations, not a temporal flow.

## Formalization

`formal/GaloisForLFunctions/HTGeometry/DifferentialClockEmbeddingCovariance.lean` proves:

- `differentialJet_algHom`;
- `jetObservableField_map_algHom`;
- `differentialClockTest_algHom_iff`;
- `finiteDifferentialClockTests_algHom_iff`;
- `jetObservable_clockTests_algHom_iff`;
- `hypertranscendentalOver_algHom_iff`;
- `hypertranscendental_clock_erosion_algHom_iff`.

## Corpus value

All seven former covariance conclusions are available under a strictly weaker map: `AlgHom` replaces
`AlgEquiv`.  This removes construction of a global inverse from any future extension-field consumer.
A targeted search found no honest current `RHTower` differential-field embedding consumer, so no
zeta-only wrapper was added.

## Status

[PROVED IN LEAN] The exact-module build refreshed only stale direct dependencies and the new module;
the touched-file check passes.  The two principal exports depend only on Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` axioms.  No full project build, numerical experiment, or
concurrent Lean process was run.
