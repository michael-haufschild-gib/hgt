# Gamma--Jacobi counterreader barycentric aggregation

- **ID:** `gamma-jacobi-counterreader-barycentric-aggregation`
- **Stage:** 3 — formalized
- **Type:** SOURCE-SPECIFIC AGGREGATION LAW / POSITIVE SURVIVOR IN LIVE NARROWED ROUTE M
- **Scientific status:** `[PAPER-PROVED] [FORMALIZED] [NOVELTY PROVISIONAL] [NOT RH]`
- **Parent no-go:** `../../5-failed/gamma-jacobi-euler-tail-cyclic-reader-no-go.md`
- **RH used:** no
- **Computation used:** no

## Statement

For moment source `m` with `m₃ ≠ 0`, first nonconstant coefficient of canonical two-sided
Hankel--Toeplitz counterreader is

```text
c₁(m) = -m₄/m₃.
```

For finite edge packet with nonzero third moments and nonzero accumulated third moment,

```text
c₁(sum_e m_e)
  = sum_e [m_e(3)/sum_f m_f(3)] c₁(m_e).
```

Thus source addition gives third-moment-weighted barycentric aggregation. It is not edge-symbol
multiplication: product first coefficient is `sum_e c₁(m_e)`. For two edges with positive third and
fourth moments, these values differ. Actual von Mangoldt successor edges `2→3` and `3→4` satisfy
those hypotheses, providing literal source witness.

## Route consequence

`SR-48` Blaschke nodes may remain useful as marked edge data, but product of isolated edge readers
cannot be identified with accumulated nonlinear counterreader. A viable continuation must retain
edge and fibre marks before contraction and use a noncyclic pointed reader. This is Route M's live
positive survivor, not an RH proof and not a reopening of its dead scalar inner--outer predecessor.

## Lean

Formalized unconditionally in:

- `formal/GaloisForLFunctions/RHTower/VonMangoldtCounterreaderBarycentricAggregation.lean`;
- `formal/GaloisForLFunctions/RHTower/GammaJacobiSingularReaderRouteClosure.lean`.

Load-bearing declarations:

- `counterreaderFirstSymbolCoefficient_eq`;
- `counterreaderFirstSymbolCoefficient_finiteEdgeAccumulatedMoment`;
- `twoEdgeCounterreaderFirstCoefficient_ne_product`;
- `vonMangoldt_twoEdgeCounterreaderFirstCoefficient_ne_product`;
- `gammaJacobiSingularReader_positiveCyclicReaderFluxNoGo`;
- `gammaJacobiSingularReaderRouteClosure`.

Direct elaboration and targeted capstone build pass. `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Novelty boundary

Ratio-of-additive-moments algebra is elementary and not claimed generically new. Provisional local
novelty is exact composition with canonical von Mangoldt Hankel--Toeplitz counterreader and its use
to close the edge-product loophole in Gamma--Jacobi Route M. Searches found no external treatment
of this source composition; absence of a hit is not a priority certificate.
