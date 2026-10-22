# Route P pointed four-unit transverse reporter

- **ID:** `route-p-pointed-four-unit-transverse-reporter`
- **Label:** P-G166
- **Stage:** 1-in-progress
- **Type:** THEOREM / POSITIVE SURVIVOR / SOURCE INCIDENCE
- **Lean:** scratch-built, axiom-audited, umbrella-wired in current working tree
- **RH status:** open

## Conjecture attacked

The literal full-Euler pre-scalar Gamma reporter has critical energy eight,
canonically split into orthogonal radial and transverse records of energy
four each. Same-carrier rigidity says neither record can be deleted while
preserving the full unpointed coefficient family. Conjecture: after retaining
the singular graph denominator and passing to pointed coefficient differences,
the radial record may be pure gauge, leaving a lossless four-unit reporter.

## Result

Write `D_sigma(u)` for the retained graph denominator, `F(s)` for the infinite
prime flux, `R_sigma` for the radial source, and `T_sigma` for the transverse
Fisher source. Lean proves the division-free identities

```text
<R_sigma,damped_sigma(u)>
  = 2 D_sigma(u) F(sigma),                         (P-G166.1)

<T_sigma,damped_sigma(u)>
  = 2 D_sigma(u) [F(sigma+u(sigma-1))-F(sigma)].  (P-G166.2)
```

`D_sigma(u)` is nonzero for `sigma>1`, `u>=0`. Hence graph normalization gives

```text
<R_sigma,damped_sigma(u)>/D_sigma(u)=2F(sigma),   (P-G166.3)

<T_sigma,damped_sigma(u)>/D_sigma(u)
  =2[F(sigma+u(sigma-1))-F(sigma)].               (P-G166.4)
```

The radial channel is exactly constant in `u`, while the transverse channel
vanishes at `u=0`. Therefore

```text
normalized(full,u)-normalized(full,0)
  = normalized(transverse,u).                     (P-G166.5)
```

After adding the explicit pointed archimedean correction, the transverse
source alone reconstructs the exact continued Xi trace difference:

```text
(-i/2)[normalized(transverse,u)-2(A(s_u)-A(sigma))]
  = Trace_Xi(s_u)-Trace_Xi(sigma).                 (P-G166.6)
```

Its source energy tends to four. Thus the eight-unit obstruction applies to
absolute coefficients, but disappears losslessly for pointed graph data.

## Heavy conjecturing loop verdict

1. **Conjecture:** build a new rational off-diagonal unitary lift of the Xi
   response.
2. **Failure:** corpus already contains Julia/Pythagoras lifts and cofinal
   contractive realizations; another lift would add no mathematical producer.
3. **Pivot:** reinterpret the eight-unit obstruction as gauge plus variation.
4. **Proof:** radial/transverse coefficient factorization shows radial record
   is graph-normalized constant, while transverse record contains all pointed
   variation.
5. **Survivor:** exact pointed completed Xi incidence carried by one actual
   four-unit Hilbert source.

## New universal principle

```text
capacity of an absolute reporter need not equal capacity of its pointed
variation: graph normalization can turn an orthogonal source record into a
flat gauge channel, which cancels from every pointed observable.
```

The factor `8=4+4` was not uniformly irreducible. It is irreducible for the
complete absolute coefficient family, but pointed Xi variation lives entirely
in the transverse four-unit summand. This resolves the
`FOUR_UNIT_PRESERVING_GAMMA_COPOISSON_COMPRESSION` open core for pointed
continued-trace data, without contradicting same-carrier reporter rigidity.

## Formalization

`formal/GaloisForLFunctions/RHTower/RoutePPointedFourUnitTransverseReporter.lean`
proves:

- graph-denominator nonvanishing;
- exact radial and transverse division-free coefficients;
- radial gauge constancy and transverse pointed-current identity;
- exact full-minus-base cancellation to the transverse source;
- exact pointed continued Xi trace reconstruction;
- sharp four-unit critical source energy.

Scratch source was explicitly built to
`/tmp/routep-src/RoutePPointedFourUnitTransverseReporter.olean` with
`lake env lean`. All audited theorems report only
`[propext, Classical.choice, Quot.sound]`. Repository source is byte-identical
to scratch source and is wired into `RHTower.lean`. No project or umbrella
build was run.

## Remaining open core

P-G166 supplies an exact four-unit source for **pointed scalar trace
differences**. It does not yet supply the polarized two-node positive kernel
needed by P-G160, nor identify its graph-normal coefficient with P-G161's true
Hardy-complement response. Next step must polarize this transverse incidence
before scalar observation and prove one joint causal/anti-causal conserved
form. If that composition only recovers a scalar trace, it remains a receiver
and must be rejected.

## Log

- 2026-08-14 — conjectured, proved in scratch Lean, axiom-audited, copied
  byte-identically, and umbrella-wired without full build.
