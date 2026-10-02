# BAG: contraction-scale one-sided control of the actual prime cubic

- **ID:** BAG-C28.43/F334
- **Stage:** 5-failed
- **Type:** FALSIFIED estimate; THEOREM (Lean) positive survivor
- **Source:** `../1-in-progress/bagchi-quantitative-sparse-recurrence.md`, C28.43; `../../../reports/rh-current-frontier-map.md`, BAG.
- **Statement:** Neither real Jordan part of the complete actual noncontracting physical Gaussian prime cubic is bounded after normalization by `log(N)^2/N`.

## Scope

Only the proposed bounded one-sided or absolute-majorant estimate is retired. BAG, the full signed cubic asymptotic and RH remain open. Divergence of both parts does not determine their difference.

## Dependency-closed proof [PROVED HERE]

Write `N=K^(4m)`, `h=K^m`, `K=10000000`. The source global prime mass, sparse-cell deletion and upper sieve produce at least `c*N*h/log(N)^2` actual ordered prime pairs `(r,p)` in `(3N/2,25N/16]` with `h/K<d=|p-r|<=h`. No prime-pair asymptotic is assumed.

For each pair and each sign, take every prime in the disjoint windows
`r+(r/d)*(k+beta) < q <= r+(r/d)*(k+beta+1/12)`,
where `1<=k<=floor(d/128)` and `beta=0` or `1/2`. Their length is `r/(12d)>=N/(12h)`. This eventually dominates twice `(2N)^(2/3)`, so the corpus's unconditional every-window theta theorem and theta-to-cardinality bound give at least `N/(24576 logN)` partners for each sign. Every prime remains in the literal full band and every saddle is on the actual `W=1` plateau.

The exact phase is `exp(2*pi*i*(p-r)*(q-r)/r)`. Integer and half-integer recentering give signed real phase at least `1/3`, including `p<r` by cosine symmetry. The actual Gaussian factors are bounded below by `v=Re V(2)>0`. F332's complete physical entry remainder is at most `C/N^2`, leaving signed actual entry at least `v^3/(6N)` eventually. Thus each actual signed part is at least `A*N*h/log(N)^3`, for one `A>0`. Its normalized value is at least `A*h/logN`, which tends to infinity.

## No-go closure

- **Exact killing theorem:** `RHTower.tendsto_primeGaussianCubicSignedVariation`, for each Bool sign. The definition sums the appropriate nonnegative real part over EVERY full-band noncontracting triple; no sector is removed from the public quantity.
- **Strongest positive survivor:** Actual near-pair and phase-sector constructions, with both complete physical Jordan parts diverging. This is an unconditional arithmetic/physical-family theorem, not a renamed negation of a bound.
- **New insight:** The actual full Gaussian family itself requires cancellation between contributions individually larger than the contraction scale. Energy-only packet examples and one positive core no longer describe the full obstruction.
- **Lean:** `formal/GaloisForLFunctions/RHTower/ChiPrimeGaussianHyperbolicCore.lean` and `ChiPrimeGaussianCubicSignedVariation.lean`. Direct source67882 and leaf66593 passed warning-free; all16 public/new/reused declarations passed axiom audit96086 with only `propext`, `Classical.choice`, `Quot.sound`. Wired in `RHTower.lean`; no umbrella build.
- **Audit limits:** Novelty search15952 was partial; all20 candidate and20 source statements plus ingredients inspected, no matching actual-family theorem returned. No external novelty claim. Lint10435 found eleven unrelated unreachable leaves; global gate remains unclean, no new BAG error.

## Log

- 2026-10-02 — C28.43 proved and audited. Direct `lake --old env lean` leaf checks and `/tmp` axiom audit used, respecting the prohibition on full builds. No numerical experiments, added axioms, heartbeat changes or subagents.
