# Theta `L²` cyclic-radical core

- **ID:** `theta-l2-cyclic-radical-core`
- **Stage:** 3-formalized
- **Type:** UNCONDITIONAL HILBERT--POLYA TOPOLOGY THEOREM
- **Scientific status:** `[PROVED IN LEAN] [BRIDGE] [NOT AN RH PROOF]`
- **Modules:**
  - `GaloisForLFunctions/RHTower/CyclicRadicalCollapse.lean`
  - `GaloisForLFunctions/RHTower/RealCharacterDenseL2.lean`
  - `GaloisForLFunctions/RHTower/XiThetaL2Cyclicity.lean`
  - `GaloisForLFunctions/RHTower/XiThetaL2MetricSingularity.lean`
  - `GaloisForLFunctions/RHTower/XiThetaSchwartzL2ExtensionObstruction.lean`
  - `GaloisForLFunctions/RHTower/CyclicNullFormNonclosability.lean`
  - `GaloisForLFunctions/RHTower/XiThetaSchwartzL2Nonclosability.lean`

## Theorem package

The formal chain proves unconditionally:

1. every finite Borel measure on `R` has dense real-character span in complex `L²`;
2. the normalized theta-cusp source has Fourier transform `XiC` and is nonzero almost everywhere
   on the real spectral axis;
3. its complete real translation orbit is cyclic in ordinary `L²(R)`;
4. a closed submodule containing a cyclic orbit is the whole ambient space;
5. every jointly continuous sesquilinear form on ordinary `L²(R)` which is invariant under
   simultaneous translation and annihilates the theta source is identically zero;
6. consequently no nonzero metric with those properties exists;
7. a momentum-symmetric theta-null continuous Schwartz form which extends jointly continuously
   to ordinary `L²(R)` is identically zero;
8. every nonzero nonnegative form in that class fails the sequential closability criterion in
   ordinary `L²(R)` and has an `L²`-null sequence of fixed nonzero form energy;
9. within the nonnegative, momentum-symmetric, theta-null cone, sequential `L²` closability is
   equivalent to the form vanishing identically;
10. every source vector is arbitrarily close in ordinary `L²` to the form radical, so the induced
    quotient seminorm vanishes on every source coset.

The final source-specific theorem is

```text
not_exists_nonzero_xiThetaL2_continuousForm.
```

The Schwartz-to-`L²` capstone is

```text
not_exists_nonzero_xiThetaSchwartzForm_l2_extension.
```

The exact closure classification is

```text
xiThetaSchwartzForm_sequentiallyL2Closable_iff_zero.
```

The quotient-collapse theorem is

```text
exists_leftRadical_l2_approx.
```

It contains no RH hypothesis, zero-location hypothesis, positivity interface, assumed cyclicity,
or abstract source-existence premise.  Cyclicity and the almost-everywhere nonvanishing input are
proved for the actual normalized theta source.

## Scientific boundary

The Fourier-character density and cyclic-radical mechanism are classical harmonic analysis.  The
exact application to Hedenmalm's 2026 theta pair may be scientifically new, but it remains under
the route-level novelty audit.  This component is therefore conservatively classified as a bridge.

The theorem forces a positive implementation law:

> A nonzero Hedenmalm metric must be singular relative to ordinary `L²`, or must abandon an
> ordinary translation-stable source domain.  A conventional `L²` completion cannot carry the
> missing orientation.

Combined with the pointed analytic-moment determinacy theorem, this locates the remaining carrier
without claiming its sign: all moments determine the source and its Bezoutian, while any nonzero
orientation of that reconstructed Bezoutian is forced to live in a topology singular to ordinary
`L²`.
