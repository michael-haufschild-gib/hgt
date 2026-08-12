# Route-P adjacent-prime primitive recovery

- **ID:** `P-G86`
- **Stage:** `1-in-progress`
- **Type:** exact weak-kernel inverse-incidence theorem
- **Status:** `[CORPUS-NEW] [PAPER-PROVED] [LEAN EXACT-BUILT] [UMBRELLA-WIRED] [NOT RH]`
- **Parent:** `../../5-failed/route-p-adjacent-local-kernel-identification-no-go.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/GammaValuationSchurAdjacentPrimePrimitiveRecovery.lean`

## Conjecture P-G86.A: cumulative adjacent flux recovers complete covariance

For fixed valuation depth `e`, enumerate primes `p_n` and write

```text
a_n = a(p_n,e),
P_e(a) = sum_n (n+1)(a_n-a_(n+1)).
```

Conjecture: `P_e(a)` is absolutely summable for every Deninger Köthe source vector, terminal flux
`N a_N` vanishes, `P_e(a)` equals P-G78's all-prime layer sum, and replacing every layer sum by
`P_e` recovers the full weak kernel.

**Verdict: true, unconditionally proved.**

## Paper proof

Strict prime enumeration and `p_n>=n+2` imply

```text
(n+1)|a_n| <= H(p_n,e)|a_n|.
```

The right side is a subseries of first Deninger height seminorm, hence the index-weighted
coordinates are summable. This proves absolute summability of adjacent primitive terms and
`N a_N -> 0`.

Finite summation by parts gives

```text
sum_(n<N) (n+1)(a_n-a_(n+1))
  = sum_(n<N) a_n - N a_N.
```

Taking limits yields `P_e(a)=sum_p a(p,e)`. Applying this identity to both entries at every depth
gives exact kernel equality

```text
AdjacentPrimitiveKernel(a,b) = gammaValuationWeakKernel(a,b).
```

In particular cumulative primitive restores the prime-index `0`/`2` covariance that P-G85's local
edge Gram misses.

## New knowledge

P-G86 supplies precise universal principle behind P-G83--P-G85:

```text
global Gamma covariance = Gram after inverse incidence,
not sum of local edge Grams.
```

Prime path is sufficient and canonical, but only after cumulative integration. Source topology is
essential twice: zeroth seminorm makes P-G78 weak kernel continuous; first seminorm kills path
boundary flux. This is exact bridge between ordered adjacent-prime geometry and all-prime weak
Köthe completion.

## Lean realization

Headline declarations:

- `nthPrimeSubtype_index_add_two_le`;
- `summable_gammaValuationNthPrimeCoord_indexWeight`;
- `summable_gammaValuationAdjacentPrimitiveTerm`;
- `gammaValuationAdjacentPrimitive_eq_layerSum`;
- `gammaValuationAdjacentPrimitiveKernel_eq_weakKernel`;
- `gammaValuationAdjacentPrimitiveKernel_indexZero_indexTwo_eq_one`.

```text
lake build GaloisForLFunctions.RHTower.GammaValuationSchurAdjacentPrimePrimitiveRecovery
Build completed successfully (12742 jobs).
```

Capstone `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Next conjecture P-G87

Lift P-G80--P-G84 physical Pluecker/Fisher data through cumulative inverse incidence. Construct the
nonlocal physical Schur form before scalar quotient and prove its reduced response is positive,
summable, and exactly the P-G86 weak kernel response. Edgewise fractions cannot be averaged after
elimination; cumulative primitive must precede Gram/Feshbach completion.

## Honest boundary

P-G86 identifies cumulative adjacent incidence with P-G78's abstract weak kernel exactly. It does
not prove P-G84's edge-local scalar fraction implements that inverse incidence, connect the
physical Pluecker/Fisher Schur complement to this kernel, prove completed-seam moment equality,
complete Julia saturation, or prove RH.
