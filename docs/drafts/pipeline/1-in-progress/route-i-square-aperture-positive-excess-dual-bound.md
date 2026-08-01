# Route I — square-aperture positive-excess dual bound

- **ID:** `route-i-square-aperture-positive-excess-dual-bound`
- **Stage:** `1-in-progress`
- **Type:** `CONJECTURE / SOURCE ACQUISITION`
- **Status:** `[CONJECTURE] [OPEN CORE] [SOURCE-PURE] [COEFFICIENT-NONLOCAL]`
- **Route:** Route I

## Exact conjecture

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
`../2-fully-proven/not_new_scientific_knowledge/square-aperture-positive-excess-convex-duality.md`.

## Why this is the surviving pivot

The retired full-correlation pivot controlled `d_m^2` and therefore spent analytic strength on
negative deviations irrelevant to Route I. This conjecture is the exact Hilbert-space form of the
positive overshoot already known to imply RH, while its dual exposes a source-facing linear prime
functional for arbitrary nonnegative aperture weights.

It does not map to retired C2, Route E, or scalar response. It remains within Route I and is open.
Schoenfeld proves it under RH, so restating or conditionally deriving it is not progress; a proof
must supply an unconditional source mechanism.

Exact normalization gives

```text
4P_M=sum_(m<=M)(dyadicSharpPrimeSourceCoefficient(m^2)^-)^2.
```

Therefore the pivot is not a new route: it is the square-sampled Hilbert form of Route I's existing
sharp-source negative part. This normalization does not retire it because it does not map into a
different route or a known unconditional estimate.

## Competing mechanisms and hostile verdicts

1. **Positive Selberg majorant:** rejected unless it achieves the exact density-one main term.
   Standard parity-barrier loss leaves order `sum m u_m`, far above the quadratic penalty for
   diffuse small weights.
2. **Continuous PNT mean square:** bridge only. A restriction theorem may transfer its scale to
   square apertures, but the critical continuous bound is itself RH-equivalent.
3. **Signed aperture dispersion:** survives preliminary attack. It would need a source-pure
   bilinear or spectral cancellation estimate uniform over all nonnegative `u`, with no imported
   zero-width or continuation premise.
4. **Finite preset aperture dictionary:** rejected. Exact dual defect equals squared distance from
   the canonical optimizer plus the negative-aperture penalty; a finite fixed dictionary misses
   large positive coordinate rays by a quadratic amount.

## First open lemma

Produce an explicit signed source decomposition of the dual functional whose off-diagonal part has
a coercive bound sharp enough to absorb the exact density-one main term and the penalty
`sum u_m^2`. Merely expanding the von-Mangoldt pair correlation or invoking a positive sieve does
not meet this requirement.

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

**Hostile verdict:** `SURVIVES PRELIMINARY ATTACK`. Exact normalization and finite-mode attacks
narrow the mechanism to uniform signed aperture dispersion; no primary theorem found supplies it.

## Gates

- [x] exact one-sided quantity isolated
- [x] exact finite duality paper-proved
- [x] full-square circularity absorbed
- [x] preliminary collision and parity-barrier audit
- [ ] signed source decomposition
- [ ] unconditional dual upper bound
- [ ] dependency-closed proof
- [ ] exact unconditional Lean proof of source estimate
