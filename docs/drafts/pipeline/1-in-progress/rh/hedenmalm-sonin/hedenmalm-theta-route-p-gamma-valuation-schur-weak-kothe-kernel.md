# Route-P weak Köthe Gamma-valuation Schur kernel

- **ID:** `P-G78`
- **Stage:** `1-in-progress`
- **Type:** exact weak completion / positive continuous kernel
- **Status:** `[CORPUS-NEW] [PAPER-PROVED] [LEAN EXACT-BUILT] [UMBRELLA-WIRED] [NOT RH]`
- **Parent:** `hedenmalm-theta-route-p-gamma-valuation-schur-kothe-vector-no-go-dual-survivor.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/GammaValuationSchurWeakKotheKernel.lean`

## Conjecture P-G77.A: weak `K_H -> K_H'` Schur completion exists and recovers source covariance

For a rapid test `a`, sum its literal positive valuation axes at each depth:

```text
L_e(a) = sum_p a_(p,e+1).
```

Define the weak Gamma-valuation kernel and energy

```text
K(a,b) = sum_e conjugate(L_e(a)) L_e(b),
E(a)   = sum_e |L_e(a)|^2.
```

**Verdict: true, unconditionally proved.** Absolute summability follows from the source's zeroth
height seminorm. Lean proves

```text
|K(a,b)| <= seminorm_0(a) seminorm_0(b),
0 <= E(a) <= seminorm_0(a)^2,
K(a,a) = E(a).
```

For the non-Cauchy coherent prime prefixes `V_N(p)` of P-G77,

```text
K(V_N(p),V_N(q))
  = first-N arithmetic Schur prefix kernel(p,q)
  -> Xi transverse Gamma-valuation Szego kernel(p,q).
```

Thus the exact all-prime source covariance exists as a positive weak kernel even though no
individual coherent prime state belongs to the rapid source completion.

## New knowledge

P-G74--P-G78 close the topology-placement problem. Critical clock data is lost in Hardy topology,
retained by `K_H`, excluded as a completed vector of `K_H`, but recovered canonically as a
continuous positive weak form on `K_H x K_H`. Cofinal Gamma-Schur translation now has a literal
unconditional home: weak covariance before scalar compression.

## Lean realization

Headline declarations:

- `gammaValuationLayerSum`;
- `gammaValuationWeakKernel` and `gammaValuationWeakEnergy`;
- `norm_gammaValuationWeakKernel_le`;
- `gammaValuationWeakEnergy_nonneg` and `gammaValuationWeakEnergy_le`;
- `gammaValuationWeakKernel_self_eq_energy`;
- `gammaValuationWeakKernel_prefix_eq_schurPrefix`;
- `tendsto_gammaValuationWeakKernel_prefix_atTop`.

Exact audit:

```text
lake build GaloisForLFunctions.RHTower.GammaValuationSchurWeakKotheKernel
Build completed successfully (12730 jobs).
```

## Next conjecture

Compose critical Stokes graph multiplication with this weak kernel and compute its reflected
Schur-reduced quadratic response. First hostile gates: continuity on shifted height seminorms,
anti-Herglotz sign, finite central mass, and comparison with P-G72's completed seam mass.

## Honest boundary

P-G78 constructs the forced weak Schur carrier and exact source covariance. It does not yet sew
the archimedean/polar channel, identify completed seam moments, or prove RH.
