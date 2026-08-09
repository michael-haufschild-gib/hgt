# Mass-shifted stochastic-order null-flag collapse

- **ID:** `mass-shifted-stochastic-order-null-flag-collapse`
- **Stage:** 2-fully-proven
- **Type:** FALSIFIED / THEOREM (paper)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · §9.3 exact open core
- **Statement:** Ordinary likelihood-ratio or first stochastic order cannot orient a shifted-Xi
  boundary crossing: the visible null face fixes mass and first moment, which saturates every
  nonnegative monotone-likelihood kernel, while the actual adaptive root-threshold observable is
  neither monotone nor antitone.
- **Novelty:** `[CORPUS-SYNTHESIS][NOVELTY UNVERIFIED]`

## Goal

Test whether new monotone-likelihood-ratio and total-positivity infrastructure can replace the
missing source-conditioned root-incidence theorem in §9.3. A valid reduction must produce the
strict sign of the first omitted coupling; it may not assume a higher-order stochastic inequality
that is merely the same quadrature error under another name.

## Gates

- [x] 0 → 1 in-progress: exact MLR consumer, adaptive carrier, and hostile common-face pair fixed
- [x] 1 → 2 fully-proven: kernel saturation, tail crossing, and nonmonotone-test proofs complete
- [ ] 2 → 3 formalized: Lean theorems and targeted audit pending
- [ ] 3 → 4 publication-ready: standalone novelty and parent-theory audit incomplete

## Conjecture/proof loops

### Conjecture 31 — likelihood-ratio order orients the adaptive crossing

Conjecture: compare two positive realizations of one visible singular face by monotone-likelihood-
ratio order. The induced first stochastic order should then orient the first omitted coupling.

**FAIL 1: exact equality-case saturation.** Let `f,h,g` be real integrable functions on a measure
space, with `g*f` and `g*h` integrable, and define

```text
K(x,y) = (g(y)-g(x)) (h(x)f(y)-h(y)f(x)).
```

Fubini and expansion into four product terms give the exact identity

```text
∫∫ K = 2 ((∫ g f)(∫ h) - (∫ g h)(∫ f)).                 (1)
```

If the two carriers have the same mass and the same `g`-moment, the right side is zero. If in
addition `K≥0` almost everywhere—the integrated MLR hypothesis—then integrability of `K` and the
zero-integral criterion for nonnegative functions force

```text
K = 0 almost everywhere.                                (2)
```

Thus MLR on the visible statistic is saturated, not strict. For `g(t)=t`, this is the precise
equality-case obstruction behind the standard fact that distinct integrable probability laws with
equal mean cannot be strictly ordered by first stochastic order.

**FAIL 2: the actual test is outside first-order duality.** In the hostile squared-factorial face,

```text
P^sharp(t) = (t-9)/36,
G(t) = t^2 P^sharp(t).
```

Exact values show

```text
0 < 3,   G(0)=0 > G(3)=-3/2,
6 < 9,   G(6)=-3 < G(9)=0.
```

Hence `G` is neither monotone nor antitone on `[0,∞)`. First stochastic order has no sign rule for
this adaptive observable.

**FAIL 3: the common-face carriers are not stochastically comparable.** For the exact carriers

```text
mu+ = (48/49) delta_(3/4) + (1/49) delta_13,
mu- = (12/13) delta_(1/2) + (1/13) delta_7,
```

both total masses and raw first moments equal one. Their strict upper-tail masses cross:

```text
mu+((5/8,∞)) = 1       > 1/13 = mu-((5/8,∞)),
mu+((1,∞))   = 1/49    < 1/13 = mu-((1,∞)).
```

Therefore neither carrier first-order stochastically dominates the other. This is not a generic
counterexample detached from the route: these are the already proved carriers with the same
positive singular squared-factorial face and opposite exact Krein crossings.

### Conjecture 32 — higher-order stochastic order repairs the loss

Conjecture: replace first stochastic order by a higher-order convex/Peano-kernel order adapted to
the visible moment constraints.

**FAIL AS A PROOF-BURDEN REDUCTION.** On a positive flat size-`n+1` Hankel face, the existing exact
quadrature theorem gives

```text
monic boundary remainder
  = s_(2n+1) - canonical boundary quadrature of X^(2n+1).
```

This monic remainder is the first omitted Krein coordinate. Consequently a higher-order order
hypothesis that signs the first unseen monomial has assumed precisely the missing extension sign.
A genuinely stronger order on all higher-convex tests could imply the target, but the corpus has no
source theorem producing it; as currently typed it moves rather than reduces the open core.

## Paper proof

Identity (1) follows by distributing `K` into

```text
h(x) g(y) f(y) - f(x) g(y) h(y)
  - g(x) h(x) f(y) + g(x) f(x) h(y)
```

and applying the product-integral identity to each term. Equal masses and equal `g`-moments make
the resulting cross-multiplied gap zero. Under `K≥0` almost everywhere, the Bochner integral
zero criterion gives (2). The polynomial values and tail masses above follow by direct exact
substitution into the displayed finite atomic laws. The higher-order classification is the
existing first-unseen-moment theorem
`finiteHankelBoundaryMonicRemainder_eq_firstUnseenMomentError`.

No unproved mathematical dependency remains.

## No-go closure

- **Exact killing theorem/mechanism:** matched visible mass and first moment force every nonnegative
  monotone-likelihood kernel to vanish almost everywhere; the adaptive crossing test is not in the
  monotone-observable cone, and the exact common-face carriers have crossing upper tails.
- **Strongest positive survivor:** equality-case MLR saturation (1)–(2) is a general integral
  rigidity law. It classifies why ordinary stochastic order cannot be a strict boundary producer.
- **New insight:** stochastic-order hierarchy has a sharp type boundary here. First order collapses
  on visible null data; higher order, when specialized to the first unseen monomial, is exactly the
  open extension coordinate. Required input remains source-native occupation across roots of the
  adaptive `P^sharp`, not generic order of positive carriers.
- **Status:** paper proof dependency-closed; Lean formalization pending.

## Literature boundary

- Duembgen and Moesching, [*On Stochastic Orders and Total Positivity*
  (arXiv:2209.07868)](https://arxiv.org/abs/2209.07868), treats usual and likelihood-ratio orders
  and their TP2 relation. These orders act on monotone observables and require an ordered positive
  pair; neither property holds for the adaptive discrepancy.
- Derbazi, [*Stochastic Ordering under Weaker Likelihood-Ratio Shape Conditions*
  (arXiv:2605.11973)](https://arxiv.org/abs/2605.11973), weakens likelihood-ratio shape assumptions
  while retaining endpoint criteria for usual stochastic order. It does not overcome equal-moment
  saturation or sign a nonmonotone adaptive polynomial.
- The route-specific saturation/tail-crossing synthesis is `[CORPUS-SYNTHESIS][NOVELTY
  UNVERIFIED]`; no external priority claim is made.

## Log

- 2026-08-09 — conjecture 31 killed by exact MLR equality-case saturation, adaptive-test
  nonmonotonicity, and two-threshold tail crossing on the common face.
- 2026-08-09 — conjecture 32 classified as circular at the first unseen monomial by the existing
  exact quadrature-extension theorem.
