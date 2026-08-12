# Route-P adjacent-local kernel identification no-go

- **ID:** `P-G85`
- **Stage:** `5-failed`
- **Type:** exact operator-identification no-go with formal survivor
- **Status:** `[CORPUS-NEW] [PAPER-PROVED] [LEAN EXACT-BUILT] [UMBRELLA-WIRED] [NOT RH]`
- **Parent:** `../1-in-progress/hedenmalm-theta-route-p-adjacent-prime-cofinal-feshbach.md`
- **Survivor:** `../1-in-progress/hedenmalm-theta-route-p-adjacent-prime-primitive-recovery.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/GammaValuationSchurAdjacentPrimeIncidenceNoGo.lean`

## Failed conjecture P-G85.A

Conjecture: because P-G84's adjacent-prime packet assembly is absolutely summable, its local path
incidence can be identified directly with P-G78's weak Gamma-valuation Köthe kernel.

**Verdict: false.** Lean constructs the natural adjacent edge-block Gram

```text
sum_(e,n) conj(a_(p_n,e)+a_(p_(n+1),e))
                    (b_(p_n,e)+b_(p_(n+1),e)).
```

It is absolutely summable for every pair of Köthe source vectors. Yet deltas at prime indices
`0` and `2` at one common depth give exact values

```text
adjacent edge Gram = 0,
P-G78 weak kernel = 1.
```

Local path incidence is banded; P-G78 layer covariance is rank-one complete prime coupling.
Summability cannot turn one into the other.

## New knowledge and higher principle

P-G83 and P-G85 reveal opposite failure modes:

```text
complete local packets: correct nonlocal reach, infinite repeated-minor incidence;
adjacent local packets: finite incidence and summability, missing nonadjacent covariance.
```

Required object is neither complete local overlap nor bounded local edge Gram. It is inverse
incidence: cumulative path flux must propagate adjacent differences nonlocally before the Gram or
Schur quotient is taken. This matches the independent exact Abel graph-flux law already present in
`XiMassFullAdjacentPrimeGraph.lean`.

## No-go closure audit

P-G86 formalizes the positive survivor. First Köthe height kills terminal path flux and the
cumulative adjacent primitive exactly recovers every all-prime layer sum and the full weak kernel.
Re-attempt direct local identification only if additional nonlocal inverse-incidence terms are
included explicitly.

## Lean audit

Headline declarations:

- `summable_norm_gammaValuationAdjacentEdgeVector`;
- `summable_gammaValuationAdjacentEdgeTerm`;
- `gammaValuationWeakKernel_axisDelta_sameDepth`;
- `gammaValuationAdjacentEdgeKernel_indexZero_indexTwo_eq_zero`;
- `gammaValuationAdjacentEdgeKernel_ne_gammaValuationWeakKernel`.

```text
lake build GaloisForLFunctions.RHTower.GammaValuationSchurAdjacentPrimeIncidenceNoGo
Build completed successfully (12741 jobs).
```

Capstone `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Honest boundary

This rejects local edge-kernel identification, not P-G84's scalar positivity or a cumulative path
representation. It does not connect physical packet Fisher data to inverse incidence, prove
completed-seam moments, or prove RH.
