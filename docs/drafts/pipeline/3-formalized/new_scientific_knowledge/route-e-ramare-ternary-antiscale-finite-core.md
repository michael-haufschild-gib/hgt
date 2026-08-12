# Route E Ramaré ternary antiscale finite core

- **ID:** `ROUTE-E-RAMARE-TERNARY-ANTISCALE-FINITE-CORE-001`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / EXACT FINITE CORE / ESCAPE CLASSIFICATION
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [NOT RH]`
- **Parent:** `route-e-ramare-recombination-ternary-antiscale-law.md`
- **Route:** E
- **RH used:** no
- **Computation used:** no
- **Literature used:** no; internal-corpus derivation

## Result

For a finite packet `Q` of natural primes, a ternary history assigns each prime one of three
states: absent, left, or right.  Let `a_h` and `b_h` be products of left and right primes, let

\[
 \lambda_h=\log(a_h/b_h),\qquad R_Q=\prod_{p\in Q}p,
\]

and give every occupied state the alternating Möbius sign.  Lean closes the finite marker theorem
stack unconditionally.

### A. Arithmetic history geometry

Prime-log linear independence gives injectivity of `h |-> lambda_h`.  Distinct histories obey

\[
 |\lambda_h-\lambda_k|\ge R_Q^{-2}.
\]

Both products are squarefree, their prime supports are disjoint, and

\[
 (a_h,b_h)=1,
 \qquad c_h=\mu(a_h)\mu(b_h).
\]

The last identity is an actual arithmetic bridge, not a formal sign proxy.

### B. Unweighted alternating reporter

Lean proves the exact all-history expansion

\[
 \mathcal T_Q(t)=\prod_{p\in Q}(1-p^{it}-p^{-it})
 =\sum_h c_h e^{it\lambda_h}
\]

and exact coefficient energy

\[
 \sum_h|c_h|^2=3^{|Q|}.
\]

For every real `W`,

\[
 \int_{-W}^{W}|\mathcal T_Q(t)|^2dt
 \le \bigl(2W+4R_Q^2(1+|Q|\log3)\bigr)3^{|Q|}.
\]

Each local factor has norm at most three, with equality exactly when its prime phase is `-1`.
Simultaneous prime-log recurrence gives arbitrarily late reporter values approaching the exact
global supremum `3^|Q|`.  Thus antiscale coherence is the exact pointwise escape mode.

### C. Reciprocal Gibbs reporter

Give local states weights proportional to `1,1/p,1/p`.  Lean proves the exact history expansion and
coefficient energy

\[
 V_Q=\prod_{p\in Q}{1+2/p^2\over(1+2/p)^2}.
\]

The weighted reporter satisfies

\[
 \int_{-W}^{W}|\Phi_Q(t)|^2dt
 \le \bigl(2W+4R_Q^2(1+|Q|\log3)\bigr)V_Q
\]

and

\[
 V_Q\le\exp\left(2\sum_{p\in Q}p^{-2}-2\sum_{p\in Q}p^{-1}\right).
\]

Its local norm is at most one, equality holds exactly at antiscale, and modulus-one escape recurs
cofinally.  Nevertheless `V_Q -> 0` unconditionally along canonical prime packets.  Pointwise
coherence and finite-height Gibbs dissipation therefore coexist exactly.

## Lean certificate

Module:

```text
GaloisForLFunctions.RHTower.Sieve.RouteERamareTernaryAntiscale
```

Principal declarations:

```text
routeETernaryHistoryFrequency_injective
routeETernaryHistoryFrequency_separated
routeETernaryReporter_eq_frequencyPolynomial
routeETernaryHistoryCoefficient_energy
routeETernaryReporter_meanValue_le
routeETernaryLocalFactor_norm_eq_three_iff
exists_gt_routeETernaryReporter_norm_gt_pow_sub

routeETernaryWeightedReporter_eq_frequencyPolynomial
routeETernaryWeightedHistoryCoefficient_energy
routeETernaryWeightedReporter_meanValue_le
routeETernaryWeightedMeanSquareMass_le_exp
routeETernaryWeightedLocalFactor_norm_eq_one_iff
exists_gt_routeETernaryWeightedReporter_norm_gt_one_sub
tendsto_routeETernaryWeightedMeanSquareMass_criticalPrimePacket_zero

routeETernaryProducts_coprime
routeETernaryHistoryCoefficient_eq_moebiusProducts
```

Module is imported by `GaloisForLFunctions.RHTower`.  Targeted build and direct module check pass.
Kernel axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.  No `sorry`,
`admit`, new `axiom`, `opaque`, `unsafe`, route premise, or numerical computation occurs.

## Exact frontier consequence

Finite ternary marker analysis is closed.  Prime-frequency injectivity, finite-height spacing,
alternating signs, reciprocal weights, antiscale saturation, and canonical weighted dissipation are
not Route E gaps.

Still open:

- tensoring the finite marker with actual sharp-cutoff `Q`-rough cofactor blocks;
- the centered diffuse codiagonal/all-reporter strict-half estimate in the moving Gallagher range;
- normalized physical seam and recurrence transport for the same marker allocation.

The formerly open integer-incidence recombination is now closed in
`GaloisForLFunctions.RHTower.Sieve.RouteERamareIntegerIncidence`.

No theorem here proves `OffDiagonalSmall`, Route E, or RH.

## Log

- 2026-08-12 — exact ternary arithmetic, unweighted and reciprocal-Gibbs mean squares, antiscale
  escape classification, canonical dissipation, and actual Möbius-product bridge proved in Lean;
  umbrella import added; targeted build and kernel axiom audit passed.
