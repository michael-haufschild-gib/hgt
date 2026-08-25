# Route-P irregular-RH weak-trace mixing no-go

- **ID:** IRH-P-WEAK-TRACE-MIXING-NOGO
- **Stage:** 3-formalized
- **Type:** FALSIFIED
- **Source:** source-native Route-P depth-zero balanced Stokes carrier; Bertola--Bothner Fredholm/RH transport
- **Statement:** No bounded non-diagonal mixing of the Route-P depth-zero carrier can be relocated to ordered Xi reciprocal spectrum by a Schatten-one correction.

## Goal

Close arbitrary-mixing loophole left by canonically diagonal relocation no-go. Replace coordinatewise
comparison by basis-independent approximation-number ideal boundary. Test full additive
trace-class Fredholm/IIKS escape allowed by irregular Riemann--Hilbert tau-function machinery.

## Gates

- [x] 0 → 1 in-progress: exact operators and ideal boundary fixed; no fitted Xi coefficient
- [x] 1 → 2 fully-proven: complete paper proof below; `[PROVED HERE]`; no open dependency
- [x] 2 → 3 formalized: Lean theorem, direct check, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone note and external novelty review pending

## Audit

- `[CORPUS]` `routePPrimitiveGammaJuliaDepthZeroStokesMultiplier_eq` identifies positive
  depth-zero Route-P Stokes multiplier as `2/p`.
- `[CORPUS]` `routeKSignedPrimeEquiv` orders two signed prime sectors with multiplicity two.
- `[CORPUS]` `approxNumber_ellTwoDiagonal_reindex_eq` computes approximation numbers of an
  ordered diagonal operator.
- `[CORPUS]` `approxNumber_add_le` gives Ky Fan subadditivity with additive indices.
- `[CORPUS]` `xiOrderedSignedPrimeOperator_not_memWeakSchattenClass_one` proves ordered Xi
  reciprocal operator lies strictly above ordinary weak `S₁`.
- `[CORPUS]` Searches for `RouteP prime harmonic operator weak Schatten class one`, `weak
  Schatten class one stable addition`, `trace class implies weak Schatten class one`, and
  `RouteP weak trace non diagonal mixing Xi` found ingredients but no source-specific
  basis-independent relocation theorem.
- `[LITERATURE]` Bertola, *The Malgrange Form and Fredholm Determinants*, SIGMA 13 (2017),
  realizes analytic matrix-RH tau functions as IIKS Fredholm determinants. It supplies the
  trace-class deformation mechanism, not a Route-P/Xi ideal comparison.
- `[LITERATURE]` Bothner, *A Riemann-Hilbert approach to Fredholm determinants of Hankel
  composition operators: scalar-valued kernels* (2022/2023), treats additive and multiplicative
  Hankel compositions and rank-one perturbations through matrix RH problems. It does not identify
  the prime-harmonic Stokes carrier with Xi or cross this weak-ideal boundary.
- `[LITERATURE]` Searches for weak-Schatten, trace-class-perturbation, prime-spectrum, and
  Riemann--Hilbert combinations found standard ideal theory and unrelated zeta spectral models,
  not this arithmetic obstruction.
- `[NOVELTY STATUS]` `[BRIDGE]`: operator-ideal ingredients are standard; their exact application
  closes a corpus open core. No exhaustive external-priority claim.

## Exact claim

Let `H` be the signed prime Hilbert space and let `P₀` be diagonal in its two prime sectors with
eigenvalues

```text
+2/p  and  -2/p.
```

Let `X` be the corpus's ordered signed Xi reciprocal operator. Then:

```text
P₀ ∈ S_{1,∞},
there is no S ∈ S_{1,∞} with X-S ∈ S₁,
for every bounded A,B : H → H, X-A P₀ B ∉ S₁.
```

All quantifiers are unconditional. No RH assumption, Xi fitting parameter, diagonal correction,
or preferred basis for `A` and `B` appears.

## Complete paper proof `[PROVED HERE]`

Order signed prime indices with multiplicity two. Absolute multipliers of `P₀` are

```text
r_n = 2 / p_floor(n/2).
```

They are positive and nonincreasing, so diagonal approximation-number theorem gives
`a_n(P₀)=r_n`. Put `k=floor(n/2)`. Elementary inequalities give

```text
n+1 <= 2(k+1),
k+1 <= 2 p_k,
```

the second following from `k<=p_k` and `p_k>=1`. Hence `n+1<=4p_k`, and therefore

```text
a_n(P₀) = 2/p_k <= 8/(n+1).
```

Thus `P₀ ∈ S_{1,∞}`.

Next prove two ideal facts directly from approximation numbers. If `T∈S₁`, monotonicity gives

```text
(n+1) a_n(T) <= sum_{j=0}^n a_j(T) <= sum_{j>=0} a_j(T),
```

so `T∈S_{1,∞}`. If `S,T∈S_{1,∞}`, Ky Fan inequality gives

```text
a_{2k}(S+T) <= a_k(S)+a_k(T).
```

For `k=floor(n/2)`, monotonicity gives `a_n(S+T)<=a_{2k}(S+T)`, while
`n+1<=2(k+1)`. Hence `S+T∈S_{1,∞}`. Therefore weak `S₁` is additive and contains `S₁`.

Assume some `S∈S_{1,∞}` satisfies `X-S∈S₁`. Then `X-S∈S_{1,∞}`, so

```text
X = S + (X-S) ∈ S_{1,∞},
```

contradicting the corpus theorem `X∉S_{1,∞}`. This proves the basis-independent existential
obstruction.

Finally weak `S₁` is preserved by bounded left and right composition, since approximation numbers
satisfy

```text
a_n(A P₀ B) <= ||A|| a_n(P₀) ||B||.
```

Thus `A P₀ B∈S_{1,∞}` for every bounded, possibly non-diagonal `A,B`; applying the existential
obstruction yields `X-A P₀ B∉S₁`.

## Hostile audit

- Reordering/unitary escape: closed. Approximation numbers are basis-independent; arbitrary
  unitary conjugation is a special case of bounded left/right mixing.
- Non-diagonal escape: closed for every additive Schatten-one correction after arbitrary bounded
  pre/post mixing.
- Infinite-rank mixing: allowed. No finite-rank or matrix-band restriction occurs.
- Source purity: `P₀` uses only literal `2/p` depth-zero Stokes weights. Xi enters only as target
  operator through its independently proved weak-ideal boundary.
- Genus escape: open by design. A Hilbert--Schmidt/non-trace-class correction or regularized
  `det₂` transport need not lie in `S₁`.
- Nonlinear escape: open by design. Claim concerns additive operator relocation underlying
  Fredholm/IIKS perturbation, not arbitrary nonlinear transforms of monodromy data.
- Full-depth carrier: depth-positive Route-P tail is expected to be trace class, but this card does
  not use or claim that decomposition. Exact proved obstruction already applies to every weak-`S₁`
  source operator.

## No-go closure

- **Exact killing theorem/mechanism:** Route-P depth-zero carrier stays in weak `S₁` under every
  bounded non-diagonal mixing, whereas ordered Xi is outside weak `S₁`; an additive trace-class
  correction cannot cross this ideal boundary.
- **Strongest positive survivor:** `[BRIDGE] [PROVED HERE]` Any additive irregular-RH source that
  is trace-class-relocatable to Xi must itself lie outside weak `S₁`. It must already carry the
  logarithmically enhanced scale `a_n ≍ log(n)/n`, or the RH correction must be non-trace-class.
- **New insight:** Genuine mixing alone cannot supply missing arithmetic density. Viable wild
  operator must encode Xi-scale density before Fredholm correction, or use genus-one/nonlinear
  transport.
- **Status:** `[LEAN-PROVED]` in
  `RoutePPrimitiveGammaJuliaLogWeakTraceMixingNoGo.lean`; capstone
  `routePPrimitive_GammaJulia_depthZero_weakTraceMixingNoGo`.

## References

- Marco Bertola, SIGMA 13 (2017), 046, https://doi.org/10.3842/SIGMA.2017.046
- Thomas Bothner, arXiv:2205.15007, https://arxiv.org/abs/2205.15007

## Log

- 2026-08-24 — corpus/literature audit, exact conjecture, hostile audit, and complete proof;
  moved to `2-fully-proven`.
- 2026-08-24 — formalized exact weak-ideal boundary and arbitrary bounded-mixing no-go; direct
  Lean check and targeted module build pass; all new theorem declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`; moved to `3-formalized`. Repository-wide lint remains
  blocked by four unrelated pre-existing umbrella-reachability errors.
