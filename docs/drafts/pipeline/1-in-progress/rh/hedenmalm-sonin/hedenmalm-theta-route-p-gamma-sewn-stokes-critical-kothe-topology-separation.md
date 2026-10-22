# Route-P critical Hardy--Köthe topology separation

- **ID:** `P-G75`
- **Stage:** `1-in-progress`
- **Type:** exact survivor validation / source-topology separation
- **Status:** `[CORPUS-NEW] [PAPER-PROVED] [LEAN EXACT-BUILT] [UMBRELLA-WIRED] [NOT RH]`
- **Parent:** `hedenmalm-theta-route-p-gamma-sewn-stokes-critical-clock-nonclosability.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesCriticalKotheTopologySeparation.lean`

## Conjecture P-G75.A: Deninger height topology retains P-G74's erased clock direction

Embed P-G74's actual-prime witness on positive Kummer axes:

```text
v_p = p/W(p) (Delta_(p,1)-Delta_(R_p,1)),   p^2<R_p<=2p^2.
```

Conjecture: unlike its reciprocal-prime Hardy image, this sequence is not null in the Deninger
prime-log height Köthe topology.

**Verdict: true, unconditionally proved.** At the `p` coordinate, the first height seminorm sees
exactly `p^2/W(p)`. The critical source bound `W(p)<=14 log(p)/r_p`, `r_p^2=1/p`, plus
`log(p)<=p` gives

```text
1/14 < p^2/W(p) <= seminorm_1(v_p).
```

Consequently `v_p` cannot converge to zero in the Köthe topology, although P-G74 proves its Hardy
compression does.

## New knowledge

This is an exact topology discriminator on the killing family itself. Deninger height topology is
not merely larger bookkeeping: it retains the half-height critical Stokes direction that the
coherent reciprocal-prime Hardy carrier destroys. A source-graph completion can therefore evade
P-G74 without changing arithmetic labels or fitting a norm.

## Lean realization

Headline declarations:

- `primeCriticalStokesKotheWitness`;
- `deningerHeight_criticalStokesPrimeAxis`;
- `primeCriticalStokesKotheWitness_primeAxis`;
- `one_fourteenth_lt_deningerHeightSeminorm_one_primeCriticalStokesKotheWitness`;
- `not_deningerKotheTendsto_primeCriticalStokesKotheNullSequence_zero`.

Exact audit:

```text
lake build GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCriticalKotheTopologySeparation
Build completed successfully (12728 jobs).
```

## Next conjecture

Lift finite Gamma-Schur valuation translation to this Köthe graph carrier. Prove cofinal residuals
are graph-Cauchy in every height seminorm after source weighting, and compute the exact limiting
quadratic response before compact square pushforward.

## Honest boundary

P-G75 validates the forced topology but does not yet construct the Gamma/polar Schur limit or its
completed-seam moments. It does not prove RH.

