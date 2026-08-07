# Mass–Xi full adjacent-prime graph and boundary flux

- **ID:** `mass-xi-full-adjacent-prime-graph-flux`
- **Stage:** `3-formalized`
- **Conjecture/result:** `C39` `[LEAN-PROVED] [STRUCTURAL REDUCTION] [NOT RH]`
- **Parent:** C38 adjacent-prime matching
- **Target:** `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3

## Conjecture loop

### C39-1: even matching is shadow of full ordered-prime graph

For increasing primes `p_n`, critical coefficients `t_n`, and Fourier profile

```text
F_n(a,tau) = stripFourier(xiMassAnalyticTest(a,tau), log p_n),
G_n(a,tau) = t_(n+1) (F_n(a,tau) - F_(n+1)(a,tau)),
```

conjecture that the full edge layer `sum'_n G_n` is absolutely summable and uniformly bounded on
every line `tau=sigma+iu`, `sigma>0`.

**Proof.** The actual integral Lipschitz theorem and the same quarter-exponential potential as C38
give, for `E_n=exp(-log(p_n)/4)`,

```text
‖G_n(a,sigma+iu)‖ <= 16 J_1(sigma) (E_n-E_(n+1)).
```

This is now an exact one-step telescope rather than the coarser even-block telescope. Hence

```text
sum_n ‖G_n(a,sigma+iu)‖ <= 16 J_1(sigma) E_0
```

uniformly in `u`. No PNT, prime-gap estimate, numerical input, or RH-strength assumption enters.

**Status:** proved in Lean.

### C39-2: connected edge control closes scalar source

This conjecture fails. Connectedness alone does not invert graph incidence with a bounded inverse.
Let

```text
T_N = sum_{n<N} t_n.
```

Exact finite Abel summation gives the stronger positive survivor

```text
sum_{n<N} t_n F_n
  = F_(N-1) T_N
    + sum_{n<N-1} T_(n+1) (F_n-F_(n+1)).
```

Thus scalar source is not the unweighted full edge layer. It is a terminal boundary flux plus edge
gradients multiplied by cumulative critical mass. C38/C39-1 only control gradients with local
weight `t_(n+1)`; replacing it by `T_(n+1)` is precisely the unbounded inverse-incidence problem.

**Status:** finite identity proved in Lean; required uniform boundary-flux estimate remains open and
is RH-strength when reassembled into the full scalar source.

## Higher universal principle

Valuation and dilation theorems kill local vertical boundaries. C38 and C39-1 kill local horizontal
graph boundaries. The remaining scalar mode is degree-zero cohomology of the cofinal prime-log
graph. Wold identifies its von-Mangoldt normal source and the critical non-Hilbert--Schmidt wall;
Hedenmalm recurrence rules out finite and summably weighted diagonal coercivity. The missing
completion must therefore control the exact Abel flux above through a nonsummably renormalized,
genuinely non-diagonal all-prime law. Any theorem that only bounds unweighted local gradients is
provably aimed at the wrong norm.

## Lean realization

`formal/GaloisForLFunctions/RHTower/XiMassFullAdjacentPrimeGraph.lean`

Principal theorems:

- `norm_xiMassBalancedSuccessorPrimeLayer_vertical_le`
- `sum_range_xiMassPrimeAtom_eq_graphFlux`

All proofs are unconditional and computation-free.
