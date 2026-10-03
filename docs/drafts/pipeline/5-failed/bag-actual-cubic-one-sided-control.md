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
- **Strongest positive survivor:** Actual near-pair and phase-sector constructions prove both complete physical Jordan parts diverge. F335 additionally proves genuine cancellation on a widening actual subfamily whose OWN two Jordan parts diverge: completing each q-row and summing row norms gives normalized limit zero. F336 removes the entire lower gap cutoff, including bounded gaps, while retaining divergence of both parts on the same larger family.
- **New insight:** The actual full Gaussian family itself requires cancellation between contributions individually larger than the contraction scale. Energy-only packet examples and one positive core no longer describe the full obstruction.
- **Lean:** `formal/GaloisForLFunctions/RHTower/ChiPrimeGaussianHyperbolicCore.lean` and `ChiPrimeGaussianCubicSignedVariation.lean`. Direct source67882 and leaf66593 passed warning-free; all16 public/new/reused declarations passed axiom audit96086 with only `propext`, `Classical.choice`, `Quot.sound`. Wired in `RHTower.lean`; no umbrella build.
- **Audit limits:** Novelty search15952 was partial; all20 candidate and20 source statements plus ingredients inspected, no matching actual-family theorem returned. No external novelty claim. Lint10435 found eleven unrelated unreachable leaves; global gate remains unclean, no new BAG error.

## Log

- 2026-10-02 — C28.43 proved and audited. Direct `lake --old env lean` leaf checks and `/tmp` axiom audit used, respecting the prohibition on full builds. No numerical experiments, added axioms, heartbeat changes or subagents.

## Further positive survivor — C28.45/F335 [LEAN PROVED]

For every full-band pair m²/10000000<|p-r|<=m³ on N=10000000^(4m), retain the complete noncontracting physical q-row. `tendsto_primeGaussianCubicGapRowMass` proves the normalized sum of row norms tends0; `tendsto_primeGaussianCubicGapSignedVariation` proves each normalized Jordan part on this identical family tends to infinity. Exact log unweighting, source theta-Abel control and endpoint-vanishing C² Fourier decay produce cancellation. Global prime mass, finite cell deletion and the uniform source two-sign sector theorem produce the divergent variation. Full paper/Lean details and limitations are recorded under C28.45/F335 on the source card.

Direct source11994/54339 and leaf93703 checks pass; all32 public/new/reused axiom audits1375 use only standard logical axioms. No assertion about the complementary gaps or complete signed cubic follows. The new insight is an actual physical family exhibiting both the obstruction to entrywise one-sided control and a proved mechanism for signed cancellation.


## Stronger positive survivor — C28.46/F336 [LEAN PROVED]

`ChiPrimeGaussianCubicNearCancellation.lean` closes ALL noncontracting near pairs
`0 < abs(p-r) <= m^3` at the same conductors. Its exact physical row-norm limit is zero
and both same-family Jordan parts diverge. The source two-prime sieve pays the missing
small-gap arithmetic through the completed-row inverse-square decay; its full finite
remainder is retained and then absorbed by a proved asymptotic. This eliminates the
previous small-gap exclusion, not merely a constant in the old annulus.

Direct production79689 and final axiom9061 pass cleanly; both public capstones and the
literal sieve producer depend only on standard logical axioms. Wired into RHTower;
no full or umbrella build. Global lint8309 still has15 unrelated unreachable modules.
Large-gap joint signed cancellation, full cubic asymptotics and RH remain open.

## Further positive survivor — C28.47/F337 [LEAN PROVED]

`ChiPrimeGaussianCubicHalfCancellation.lean` proves normalized complete-row norm
cancellation for ALL band-prime pairs `abs(2*p-3*r)<=m^3` on the same conductors.
This is a macroscopic-gap family. Its true frozen profile has a nonzero lower band
endpoint, retained by one integration and exact log unweighting. Actual dilation-pair
density with fourth-root singular cost pays the missing arithmetic aggregation.
Every physical error, moving window and contraction removal remains explicit.
No Jordan-part lower bound is asserted for this new family; F336 still supplies the
same-family divergent-parts result on the original near pairs.

All three direct production leaves pass cleanly (17659,90739,55859); final seven-query
axiom66643 exits0 with only `propext`, `Classical.choice`, `Quot.sound`. Full joint cancellation outside the closed families and RH
remain open.
