# Route U global complementary Nyquist-current exchange

- **ID:** `route-u-global-nyquist-current-exchange`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md`, `U-DYC-global`; successor to
  `route-u-nyquist-null-form-rigidity`
- **Statement:** The native shifted-resolvent-weighted signed dyadic Nyquist current has an
  absolutely summable complete-Xi divisor expansion at every scale, and its full divisor sum tends
  to zero with explicit rate coefficient `O((k+1)^-2)`, without Riemann--von Mangoldt asymptotics
  or a zero-location hypothesis.

## Status labels

`[LEAN-PROVED] [BRIDGE] [NOVELTY UNVERIFIED]`

## Conjecture--attack--pivot loop

### U-PN-PSD — positive ultraviolet-safe covariance

`[FALSIFIED]` The preceding card proves that every positive-semidefinite quadratic channel
observable annihilating the parabolic `(1,-1)` mode collapses to reconstructed fine energy.  No
nontrivial positive cross-scale covariance survives.

### U-PN-NULL-global — signed current needs a zero-count majorant

Initial conjecture: summing the signed current over all Xi copies requires a
Riemann--von Mangoldt asymptotic because the pointwise endpoint limits are not uniform.

`[FALSIFIED]` Exact complementary alias factorization exposes fourth-order Paley--Wiener decay
uniformly across the entire moving Nyquist cell.  The native resolvent supplies the already-formal
summable reciprocal-square divisor atom.  No zero count is needed.

### Positive survivor

Let `P_f(k,q)` be the fine hard-edge sample, `P_c(k,q)` the coarse periodization evaluated at the
fine phase, and `J_k(q)` the signed Nyquist current.  Lean proves exactly

```text
J_k(q) = P_f(k,q) * (P_c(k,q)-P_f(k,q)).                (1)
```

For `L_k=pi*(k+1)`, there is an explicit source-dependent `K>=0`, independent of `k,q`, such that

```text
norm(J_k(q)) <= K/L_k^4.                                (2)
```

With native weight `W_(2k+1)(q)`, the complete divisor current satisfies

```text
sum_q W_(2k+1)(q) J_k(q) -> 0.                          (3)
```

## Complete paper proof

Fix compact-support approximation index `n`, Schwartz source `f`, scale `k`, and Xi divisor copy
`q`.  Put

```text
z = fine Cayley phase,
L = coarse alias period = pi*(k+1),
B = routeUComplexTiltUniformDecay n f 0,
D = routeUComplexHardEdgeUniformAliasTailConstant n f 1,
C = routeUComplexTiltUniformDecay n f 2 * (4*pi)^4.
```

The fine hard-edge mass is exactly twice the coarse mass, hence its alias period is `2L`.  Exact
even/odd lattice recombination gives

```text
E = P_c/2,       O = P_f-E,
E+O=P_f,         E-O=P_c-P_f.
```

Therefore `J=(E+O)(E-O)` is exactly (1).

The Cayley phase always obeys `|Im z|<=1` and `|Re z|<=L`.  Split its fine central cell into two
regions.

### Inner coarse cell: `|Re z|<=L/2`

Both periodizations admit the same central entire extension `F(z)` plus their respective alias
tails:

```text
P_c=F(z)+T_c,       P_f=F(z)+T_f.
```

Uniform fourth-order alias decay gives

```text
norm(T_c)<=D/L^4,
norm(T_f)<=D/(2L)^4<=D/L^4.
```

Thus the central term cancels before taking norms,

```text
norm(P_c-P_f)<=2D/L^4.
```

The zeroth-order extension bound plus tail bound gives `norm(P_f)<=B+D`.  Hence

```text
norm(J)<=2D(B+D)/L^4.                                   (4)
```

### Outer coarse half-cell: `L/2<=|Re z|<=L`

The fourth-order weighted Fourier estimate and
`L/(4*pi)<=kgFreq(-Re z/(2*pi))` give

```text
norm(F(z))<=C/L^4.
```

Adding the fine alias tail yields

```text
norm(P_f)<=(C+D)/L^4.                                   (5)
```

Exact alias periodicity folds `z` by `+L` or `-L`, according to its sign, into the coarse central
cell.  The coarse packet therefore has the uniform bound `B+D`; the fine packet has the same
zeroth-order bound.  Consequently

```text
norm(P_c-P_f)<=2(B+D).                                  (6)
```

Multiplying (5) and (6) gives the outer estimate

```text
norm(J)<=2(B+D)(C+D)/L^4.                               (7)
```

Equations (4) and (7) are both bounded by (2) with

```text
K=2(B+D)(D+C).
```

Now retain the native shifted-resolvent weight.  The corpus bound is

```text
norm(W_r(q)) <= mass(r)^2 * norm(xiZeroCopyReciprocalSquare(q)).
```

At `r=2k+1`, fine mass is `2(k+1)`.  Combining this with (2) gives

```text
norm(W_(2k+1)(q) J_k(q))
 <= A_k * norm(xiZeroCopyReciprocalSquare(q)),

A_k = (2(k+1))^2 K / (pi*(k+1))^4
    = 4K/(pi^4*(k+1)^2) -> 0.                           (8)
```

The reciprocal-square norm family is summable over `XiZeroCopy`.  Equation (8) proves absolute
summability at each `k`, bounds the norm of the complete sum by `A_k` times one fixed finite sum,
and squeezing proves (3).  Every theorem is premise-free.  No RH assumption, zero count,
Riemann--von Mangoldt asymptotic, numerical computation, or unproved exchange is used.  QED.

## Novelty and significance audit

- `[CORPUS]` The exact dyadic reconstruction, complex Paley--Wiener tail estimates, native
  resolvent reciprocal-square bound, and reciprocal-square divisor summability were already
  formalized separately.
- `[NEW COMPOSITION]` The inner/outer cell decomposition, complementary coarse/fine alias
  factorization, uniform signed-current `L^-4` law, and its complete-divisor `O((k+1)^-2)` exchange
  were not found in the internal corpus.
- `[LITERATURE]` Classical two-channel perfect-reconstruction theory explains alias folding but
  not this Xi hard-edge resolvent-weighted current; see P. P. Vaidyanathan,
  <https://authors.library.caltech.edu/records/j1cr6-qe046>, and the polyphase sampling context
  <https://authors.library.caltech.edu/records/2z8vr-55q86>.

Higher principle: the earlier zero-count obstruction was a shadow of estimating either scale
before forming the complementary null product.  Central extension cancels in the inner chart;
Fourier escape suppresses the fine factor in the outer chart.  One factor is small everywhere,
but which factor is small changes at the Nyquist wall.  This two-chart null-product principle is
the universal source of the global bound.

## Successor closure and exact open core

`route-u-prime-gamma-nyquist-flux.md` closes the requested finite-scale source identity before
divisor aggregation.  Actual even/odd physical channels have coefficient-faithful Chebyshev
polynomials; common-degree padding places both in one literal completed prime--Gamma Laplace
filter; the canonically renormalized source-capital difference equals this weighted current and
tends to zero.

The remaining obstruction is diagonal, not an unidentified source remainder.  Perform the
common-filter polarization of the false-RH full-packet capital and prove a fixed-carrier sign/lower
bound for its actual even/detail diagonal, or show that any negative diagonal forces a labelled
prime--Gamma anomaly incompatible with the degree-free Cauchy density.  Universal diagonal
positivity is RH itself and cannot be used as producer.

## Lean formalization

Module:
`formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgeGlobalNyquistCurrentExchange.lean`.

Key closed theorems:

- `routeUHardEdgeAliasPeriod_fineIndex`
- `routeUComplexHardEdgePeriodizationAt_add_aliasPeriod`
- `routeUDyadicXiNyquistCurrent_eq_fine_mul_complementaryAlias`
- `norm_routeUComplexPositiveFourierExtension_outer_le`
- `norm_routeUDyadicXiComplementaryAlias_inner_le`
- `norm_routeUDyadicXiNyquistCurrent_le`
- `summable_routeUDyadicXiWeightedNyquistCurrent`
- `norm_tsum_routeUDyadicXiWeightedNyquistCurrent_le`
- `tendsto_routeUDyadicXiWeightedNyquistMajorantCoefficient_zero`
- `tendsto_tsum_routeUDyadicXiWeightedNyquistCurrent_zero`

Scratch and checked-in source passed `lake env lean`.  Exact module `.olean` was compiled directly;
umbrella import was wired without building umbrella or project.  Axiom audit of the key algebra,
uniform bound, summability, and global limit reports only
`[propext, Classical.choice, Quot.sound]`.  Source contains no `sorry`, `admit`, new `axiom`,
`opaque`, `unsafe`, `native_decide`, `#eval`, or `#reduce`.

## Gates

- [x] 0 → 1: exact falsifiable global exchange target and hostile alternatives
- [x] 1 → 2: dependency-closed proof above
- [x] 2 → 3: checked-in Lean theorem, exact `.olean`, axiom audit, umbrella wiring
- [ ] 3 → 4: independent novelty/significance audit and standalone exposition

## Log

- 2026-08-14 — Riemann--von Mangoldt-majorant conjecture falsified by complementary alias
  factorization and inner/outer Nyquist-cell split.
- 2026-08-14 — Uniform `L^-4` signed-current bound and native weighted complete-divisor
  `O((k+1)^-2)` exchange proved in Lean.
