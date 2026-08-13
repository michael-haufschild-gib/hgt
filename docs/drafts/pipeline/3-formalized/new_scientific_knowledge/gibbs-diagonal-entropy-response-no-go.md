# Gibbs diagonal entropy-response no-go

- **ID:** `gibbs-diagonal-entropy-response-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM / NO-GO CLOSURE
- **Conjecture label:** C14
- **Inputs:** `GibbsAntiscaleFirstTraceFrame`, `ThermodynamicAffinityHolonomy`,
  `PrimeArchEntropyProductionResponseRH`

## Failed conjecture

The new Gibbs antiscale first-trace frame might feed the prime--archimedean entropy-response RH
endpoint by using its diagonal antiscale/same-sign channel decomposition as a finite KMS
observable.

## Exact failure

Entropy-production response is supported on off-diagonal transitions with nonzero energy gaps.
For any amplitude supported on the diagonal, each off-diagonal intensity vanishes by support and
each diagonal intensity vanishes because its thermodynamic affinity is zero. Therefore the entire
finite transition response is identically zero at every spectral parameter. The diagonal Gibbs
first-trace data cannot approximate a nonzero prime--archimedean source response.

## Positive survivor

Prove unconditionally:

1. diagonal support forces every finite KMS entropy-production transition intensity to vanish;
2. the associated finite passive response is identically zero.

This identifies the required replacement: the order-free cross-leaf batch dispersion already
present in `GibbsAntiscaleFirstTraceFrame` must be promoted to a Hermitian off-diagonal amplitude.

## Paper proof

If `a = b`, Gibbs population values agree, so their logarithmic affinity is `0`. If `a != b`, a
diagonally supported amplitude has `A(a,b)=0`, and the commutator intensity contains
`|A(a,b)|^2`. Thus every entropy-production intensity is zero. Substitution into the finite double
Cauchy sum makes every summand, hence the response, zero.

## Gates

- [x] Exact failure and positive survivor frozen
- [x] Dependency-closed paper proof
- [x] Lean formalization and axiom audit

## Novelty audit

Physics literature treats dynamical response as controlled by off-diagonal observable matrix
elements, so the abstract diagonal-vanishing principle is not claimed globally new. New content is
the exact corpus-level consequence: Route E's diagonal antiscale first trace cannot inhabit the
prime--archimedean entropy-response producer, while its cross-leaf dispersion is the forced next
carrier.

## Formalization

`GaloisForLFunctions.HTGeometry.ThermodynamicDiagonalResponseNoGo` proves both intensity and
response vanishing, is wired into `HTGeometry.lean`, and passes exact `lake env lean` source
verification. Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. Final
module build audit passed 2026-08-13
(`lake build GaloisForLFunctions.HTGeometry.ThermodynamicDiagonalResponseNoGo`), axiom audit
re-verified clean on both vanishing theorems.
