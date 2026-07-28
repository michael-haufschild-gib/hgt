# Summable pure-point observer recurrence

- **ID:** `summable-pure-point-observer-recurrence`
- **Stage:** 3-formalized
- **Type:** THEOREM CANDIDATE / COUNTABLE PURE-POINT RECURRENCE
- **Source:** positive survivor from the infinite zero-law limitation
- **Statement:** Every summable countable pure-point phase energy has a finite positive
  recurrence clock at every positive resolution.

## Frontier

- `[CORPUS]` `purePointObserverDistanceSq_eq_phaseEnergy` gives the exact arbitrary-index
  observer identity.
- `[CORPUS]` `summable_purePointObserver_distance_iff_phaseEnergy` identifies its summability
  condition.
- `[CORPUS]` current pure-point capstone proves only the exact zero set, not recurrence.
- `[LITERATURE]` Gimeno--Sotoca proves recurrence bounds for mixed states with finite and
  countably discrete spectra. Qualitative infinite recurrence is therefore not a novelty object.

## Exact theorem

Let `a_p>=0` be a summable real sequence and let `z_p` be arbitrary unit phases. Define

```text
E(n)=sum'_p a_p |z_p^n-1|^2.
```

### Theorem `[FORMALIZED] [REDISCOVERED]`

For every `epsilon>0`, there is a positive integer `n` such that

```text
E(n)<epsilon.                                             (1)
```

More quantitatively, choose `M` with

```text
sum'_(p>=M) a_p<epsilon/8,
```

and choose `Q>=1` with

```text
(2pi/(Q+1))^2 sum_(p<M)a_p<epsilon/2.
```

Then one may take

```text
1<=n<=(Q+1)^M.                                            (2)
```

Every countable pure-point observer family whose phase-energy blocks admit such an enumeration
therefore recurs in its total displacement at every positive resolution.

## Paper proof

Partition each of the first `M` phase circles into `Q+1` equal arcs. Among
`(Q+1)^M+1` orbit points, two occupy one product cell. Their positive difference `n` satisfies
`(2)` and

```text
|z_p^n-1|<=2pi/(Q+1),  p<M.
```

The head energy is below `epsilon/2`. Every unit-phase chord has squared norm at most four, so the
tail is below

```text
4 sum'_(p>=M)a_p<epsilon/2.
```

Summing proves `(1)`.

## Hostile attack

1. **“This is a continuous-spectrum theorem.”** False. Summable countable pure-point energy is
   essential.
2. **“It gives one dimension-independent deadline.”** False. The effective head size `M`
   depends on resolution and tail decay.
3. **“This is scientifically new.”** `REDISCOVERED`; the theorem is included to close scope,
   replace the zero-law appendix by genuine recurrence, and connect the exact observer identity
   to an honest infinite conclusion.

Verdict: `REDISCOVERED`, but required closure theorem. Exact theorem is formalized in
`SummablePurePointPhaseRecurrence.lean`, with load-bearing declarations
`exists_summablePhaseEnergy_recurrence_quantitative` and
`exists_summablePhaseEnergy_recurrence`.

## Gates

- [x] 0 → 1: exact statement and complete paper proof
- [x] 1 → 2: exact-source audit and sequence normalization complete
- [x] 2 → 3: unconditional Lean theorem and targeted foreground check
- [x] 3 → 4: replaced infinite zero-law section by genuine countable recurrence
- [ ] Final: axiom audit and capstone module build
