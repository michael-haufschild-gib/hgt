# Route I — square-aperture positive-excess dual bound

- **ID:** `route-i-square-aperture-positive-excess-dual-bound`
- **Stage:** `5-failed`
- **Type:** `RETIRED PIVOT / EXACT ZERO-WIDTH COLLISION`
- **Status:** `[PAPER-PROVED COLLISION] [LEAN TRANSFER PROVED] [NOT AN INDEPENDENT ROUTE]`
- **Route:** Route I

## Retired conjecture

With

```text
d_m = W(m^2)-2(1-1/sqrt(2))m,
P_M = sum_(1<=m<=M) (d_m)_+^2,
```

conjecture that, for every `delta>0`,

```text
P_M = O_delta(M^(1+delta)).
```

Equivalently, for every nonnegative aperture vector `u` supported on `1<=m<=M`,

```text
sum_(m<=M) (2u_m d_m-u_m^2) <= C_delta M^(1+delta).
```

Exact duality certificate:
`../3-formalized/not_new_scientific_knowledge/square-aperture-positive-excess-convex-duality.md`.

## Why this looked like a surviving pivot

The retired full-correlation pivot controlled `d_m^2` and therefore spent analytic strength on
negative deviations irrelevant to Route I. This conjecture is the exact Hilbert-space form of the
positive overshoot already known to imply RH, while its dual exposes a source-facing linear prime
functional for arbitrary nonnegative aperture weights.

Earlier audit found no coefficient-level map to retired C2, Route E, or scalar response. The
missing comparison was quantitative rather than algebraic: generalized von Koch transfers the
intrinsic Xi half-plane width to the Chebyshev error, and exact Abel summation transfers that width
to this square-energy abscissa.

Exact normalization gives

```text
4P_M=sum_(m<=M)(dyadicSharpPrimeSourceCoefficient(m^2)^-)^2.
```

Therefore the pivot is not a new route: it is the square-sampled Hilbert form of Route I's existing
sharp-source negative part. The new width theorem now retires it for a stronger reason: its
Dirichlet abscissa is exactly `1+4*xiRightTransverseSup` off the critical line, and its critical
summatory endpoint is RH. That is the zero-width invariant already exhausted by C2.

## Competing mechanisms and hostile verdicts

1. **Positive Selberg majorant:** rejected unless it achieves the exact density-one main term.
   Standard parity-barrier loss leaves order `sum m u_m`, far above the quadratic penalty for
   diffuse small weights.
2. **Continuous PNT mean square:** bridge only. A restriction theorem may transfer its scale to
   square apertures, but the critical continuous bound is itself RH-equivalent.
3. **Signed aperture dispersion:** retired as an independent mechanism. A critical bound uniform
   over all nonnegative `u` is exactly the zero-width endpoint; generalized von Koch supplies it
   from zero width, while the existing zero-by-zero square-energy theorem recovers zero width from
   it.
4. **Finite preset aperture dictionary:** rejected. Exact dual defect equals squared distance from
   the canonical optimizer plus the negative-aperture penalty; a finite fixed dictionary misses
   large positive coordinate rays by a quadratic amount.

## Exact killing theorem

Let `sigma_2` be the absolute-convergence abscissa of

```text
sum_(m>=1) (W(m^2)-2(1-1/sqrt(2))m)_+^2 m^(-s).
```

If the positive-right Xi divisor is nonempty, then

```text
sigma_2 = 1+4*xiRightTransverseSup.
```

At zero width,

```text
RH
<-> sigma_2<=1
<-> for every delta>0, P_M=O_delta(M^(1+delta)).
```

Paper proof:
`../2-fully-proven/not_new_scientific_knowledge/11-rh-zero-divisor-geometry/square-aperture-positive-excess-zero-width-collision.md`.
Lean transfer module:
`formal/GaloisForLFunctions/RHTower/CCM/CCMSharpPrimeWindowSquareEnergyWidthCollision.lean`.

## External frontier

- Friedlander--Iwaniec's asymptotic sieve breaks the classical parity barrier only after adding a
  bilinear axiom: <https://arxiv.org/abs/math/9811186>. No verified instance supplies that axiom
  uniformly for the aperture weights `A_u(k)` at the critical density-one error scale.
- Green--Tao restriction theory controls `L^p` norms of normalized Selberg majorants:
  <https://arxiv.org/abs/math/0405581>. A positive majorant retains the sieve density loss and does
  not prove the signed dual inequality above.
- Brent--Platt--Trudgian prove the continuous PNT-error mean square is `O(X^2)` under RH and that
  its normalization is unbounded if RH is false: <https://arxiv.org/abs/2008.06140>. Therefore a
  reduction to the critical continuous mean square is a classical RH-equivalent collision, not an
  unconditional source estimate.

**Hostile verdict:** `EXACT COLLISION WITH RETIRED C2 WIDTH`. Exact normalization and finite-mode
attacks narrowed the mechanism to uniform signed aperture dispersion; quantitative Abel transfer
then shows that its optimal exponent is merely the classical rightmost-zero exponent in a new
coordinate.

## No-go closure

- **Exact killing mechanism:** generalized von Koch plus exact Abel summation gives
  `sigma_2<=1+4alpha` from `XiZeroHalfPlaneBound alpha`; the formalized zero-by-zero lower theorem
  gives the converse width bound and equality at intrinsic width.
- **Strongest positive survivor:** exact spectral identity
  `sigma_2=1+4*xiRightTransverseSup` when the positive-right divisor is nonempty, plus the
  unconditional Lean theorem that every Chebyshev error width transfers to the square-energy
  abscissa and back to Xi half-plane width.
- **New insight:** coefficient-nonlocal convex duality does not create a new cancellation channel.
  Its entire positive cone measures the same transverse divisor width as C2.
- **Status:** dependency-closed paper proof complete; all new Abel and abscissa steps are
  unconditional in Lean. The shared formal generalized-von-Koch library theorem remains absent,
  so the collision is not advertised as a single assumption-free Lean equivalence.

## Gates

- [x] exact one-sided quantity isolated
- [x] exact finite duality paper-proved
- [x] full-square circularity absorbed
- [x] preliminary collision and parity-barrier audit
- [x] exact zero-width collision
- [x] dependency-closed paper proof
- [x] unconditional Lean proof of Chebyshev-to-energy transfer
- [x] unconditional Lean proof that the transfer recovers Xi half-plane width
- [ ] generalized von Koch formalized in Lean (shared infrastructure gap)

## Disposition

Square-aperture positive-excess dual pivot is retired. This does **not** close Route I's separate
pointwise sharp-window source-acquisition endpoint; it only removes the last coefficient-nonlocal
correlation survivor as an independent pivot.

## Log

- 2026-08-01 — exact intrinsic-width collision found, paper-proved, and downstream transfer
  formalized; pivot moved from in-progress to failed.
