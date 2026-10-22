# Route-P ordered-prime Pluecker chirality at every depth

- **ID:** `P-G81`
- **Stage:** `1-in-progress`
- **Type:** full prime-by-depth local source theorem
- **Status:** `[CORPUS-NEW] [PAPER-PROVED] [LEAN EXACT-BUILT] [UMBRELLA-WIRED] [NOT RH]`
- **Parent:** `hedenmalm-theta-route-p-ordered-prime-plucker-chirality.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesOrderedPrimeDepthPluckerChirality.lean`

## Conjecture P-G81.A: ordered-prime gain survives every Kummer depth

P-G80 used depths `0,1`. For arbitrary `e`, test literal physical cell

```text
(p,e), (p,e+1), (q,e), (q,e+1),       p<q.
```

At aperture

```text
0<a<(e+1/2)log(p),
```

conjecture same strict anti-monotone minor/Fisher covariance.

**Verdict: true, unconditionally proved.** Exact consecutive minor at `(p,e)` is

```text
4a^2 /
 ((p+1)^4 log(p)^2
  ((e+1/2)^2-(a/log(p))^2)^2
  ((e+3/2)^2-(a/log(p))^2)^2).
```

For fixed `a,e`, every positive denominator factor strictly increases from `p` to `q`. Therefore
physical lower-prime minor and probability are strictly larger. Prime Fisher clock orders
oppositely. Six-pair complement cancellation gives positive physical chirality--Fisher moment at
every depth.

## Consequences

For every depth and ordered prime pair:

```text
1/2 < physical Schur fraction < 1,
0 < physical residual(pk) < (1/2) information-depleted weight(pk)
```

for every retained prime-power label `pk`. No valuation depth, divisor copy, or physical
orientation is removed.

## New knowledge

Cross-prime complement chirality is a two-dimensional monotone source law on the full
`prime x valuation-depth` lattice, not merely first-depth behavior. Depth changes admissible
aperture and shape factors but never changes sign. Hence cofinal obstruction has narrowed again:
local sign and full Kummer-label coverage are closed; only compatible all-prime/all-depth assembly
and actual Feshbach identification remain.

## Lean realization

Headline declarations:

- `gammaSewnOrderedPrimeDepthPlucker_lowerConsecutiveRawWeight_eq`;
- `gammaSewnOrderedPrimeDepthPlucker_rawWeight_strictAnti`;
- `gammaSewnOrderedPrimeDepthPlucker_chiralityFisherMoment_eq`;
- `gammaSewnOrderedPrimeDepthPlucker_chiralityFisherMoment_pos`;
- `gammaSewnOrderedPrimeDepthPlucker_schurFraction_gt_half`;
- `gammaSewnOrderedPrimeDepthPlucker_schurFraction_lt_one`;
- `gammaSewnOrderedPrimeDepthPlucker_reducedWeight_mem_Ioo_half`.

Exact audit:

```text
lake build GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesOrderedPrimeDepthPluckerChirality
Build completed successfully (12734 jobs).
```

Capstone `#print axioms` audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Next conjecture P-G82

Build finite source-coherent packet sums over disjoint ordered prime pairs and all depths. Prove
positive residual and sub-half domination survive finite assembly without averaging, then use
critical information-depleted summability as a domination theorem for the all-depth/all-pair
limit. Audit dependence on pairing: either prove pair-partition invariance via Pluecker relations
or retain complete interaction graph rather than choose arbitrary matching.

## Honest boundary

P-G81 closes local sign and positive residual on entire ordered-prime-by-depth lattice. It does not
construct pairing-independent cofinal assembly, identify it with weak-kernel Feshbach elimination,
sew Gamma/polar channel, match completed seam moments, or prove RH.
