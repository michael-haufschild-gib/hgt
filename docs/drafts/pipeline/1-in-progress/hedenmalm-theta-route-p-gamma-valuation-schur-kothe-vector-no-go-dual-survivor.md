# Route-P Gamma-valuation Schur Köthe-vector no-go and dual survivor

- **ID:** `P-G77`
- **Stage:** `1-in-progress`
- **Type:** exact completion no-go / continuous-dual positive survivor
- **Status:** `[CORPUS-NEW] [PAPER-PROVED] [LEAN EXACT-BUILT] [UMBRELLA-WIRED] [NOT RH]`
- **Parent:** `hedenmalm-theta-route-p-gamma-sewn-stokes-critical-kothe-topology-separation.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/GammaValuationSchurKotheVectorNoGoDualSurvivor.lean`

## Conjecture P-G76.A: cofinal Gamma-Schur valuation state converges inside `K_H`

For fixed prime `p`, put the first `N` half-shifted valuation coordinates on their literal Kummer
axes:

```text
V_N(p) = sum_(e<N) x_p^(1/2)(1-x_p)x_p^e Delta_(p,e+1),  x_p=1/p.
```

Conjecture: `(V_N(p))` is Cauchy in every Deninger height seminorm and gives the desired coherent
Schur state in the rapid source.

**Verdict: false, retired unconditionally.** Lean computes the first-seminorm size of every new
coordinate exactly:

```text
seminorm_1(V_(N+1)(p)-V_N(p))
  = p sqrt(1/p) (1-1/p) > 0,
```

independent of `N`. Therefore the prefix sequence is not Köthe-Cauchy.

## Strongest positive survivor

The same infinite coherent family defines the exact dual pairing

```text
a |-> sum_e x_p^(1/2)(1-x_p)x_p^e a_(p,e+1).
```

Every coefficient lies strictly in `(0,1)`, so the series is summable for every rapid test and its
norm is bounded by `seminorm_0(a)`. Hence the completed valuation state exists canonically in
`K_H'`, not `K_H`.

## New universal principle

P-G74--P-G77 determine both sides of the required rigging. Hardy completion is too weak and erases
the critical clock; rapid-source vector completion is too strong and excludes the coherent
valuation state. The only source-faithful placement surviving both exact obstructions is a mixed
kernel/current

```text
K_H -> K_H',
```

with Schur/Feshbach limits interpreted weakly against rapid tests before any scalar compact
pushforward.

## Lean realization

Headline declarations:

- `gammaValuationKothePrefix`;
- `deningerHeightSeminorm_one_gammaValuationKothePrefix_succ_sub`;
- `not_deningerKotheCauchy_gammaValuationKothePrefix`;
- `gammaValuationKotheDualPairing`;
- `summable_gammaValuationKotheDualPairing`;
- `norm_gammaValuationKotheDualPairing_le`.

Exact audit:

```text
lake build GaloisForLFunctions.RHTower.GammaValuationSchurKotheVectorNoGoDualSurvivor
Build completed successfully (12729 jobs).
```

## Next conjecture

Construct the two-prime Gamma-valuation Szegő kernel as a continuous sesquilinear form on
`K_H x K_H`, prove finite Schur prefixes converge weakly to it with the exact translated residual,
then compose with critical Stokes graph operators. Test whether its Schur-reduced reflected
quadratic response remains positive and has completed-seam moments.

## Honest boundary

P-G77 fixes the object class and proves its dual continuity. It does not yet construct the global
all-prime kernel, Gamma/polar reduction, completed moments, or RH.
