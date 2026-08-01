# Route I — square-aperture von Mangoldt correlation bound

- **ID:** `route-i-square-aperture-von-mangoldt-correlation-bound`
- **Stage:** `5-failed`
- **Type:** `CONJECTURE`
- **Status:** `[CIRCULAR] [EXACT RH EQUIVALENT] [BRIDGE] [NOT AN INDEPENDENT SOURCE]`
- **Route:** Route I
- **Lean predicate:** `SquarePrimeWindowCorrelationEnergySubpower`

## Conjecture

With the exact overlap correlation energy `C_M` from
`../2-fully-proven/not_new_scientific_knowledge/square-aperture-von-mangoldt-correlation-energy.md`,

```text
for every delta>0, C_M = O_delta(M^(1+delta)).
```

Equivalently,

```text
sum_{m<=M} (W(m^2)-2(1-1/sqrt(2))m)^2
  = O_delta(M^(1+delta))
```

for every `delta>0`.

## Killing theorem

Schoenfeld's RH-conditional estimate

```text
|psi(x)-x| < sqrt(x) log(x)^2/(8 pi),  x>73.2,
```

inserted into Route I's exact Abel identity gives

```text
|W(n)-2(1-1/sqrt(2))sqrt(n)| = O(log(n)^2).
```

Consequently RH implies `C_M=O(M log(M)^4)`, hence the displayed all-subpower estimate. The
existing Lean theorem proves the converse. Thus the conjecture is paper-equivalent to RH and does
not supply an independent arithmetic producer. Paper certificate:
`../2-fully-proven/not_new_scientific_knowledge/square-aperture-von-mangoldt-correlation-energy.md`.

## Why the independent-producer interpretation fails

- It controls literal von-Mangoldt coefficients before analytic continuation.
- It is nonlocal in coefficients, so first-mode scalar-germ sign rigidity does not apply.
- It does not normalize into `logDeriv XiC`; retired C2 does not own it.
- It is not Möbius/squarefree cancellation and does not map to Route E.
- Existing Lean proves this exact conjecture implies RH through square-sampled positive-excess
  `L^2` energy, while Schoenfeld plus exact Abel summation proves RH implies the conjecture.

## Hard problem

Prove cancellation between the pair term, centered first moment, and deterministic main square.
Their separate bounds are far too large. Required input resembles a sparse square-trace Selberg
variance estimate for a discontinuous dyadic window, not ordinary continuous mean square.

## Conjecture ladder

1. **Strong pointwise parent:** all-`epsilon` subpower upper bound for every large aperture.
2. **Square pointwise parent:** same bound only at `m^2`.
3. **Active correlation core:** near-linear centered `L^2` energy on `m^2`.
4. **Weak downstream gate:** every-abscissa square-sampled positive-excess Dirichlet energy.

Step 3 implies step 4 unconditionally. RH implies steps 1--3 by the classical
von Koch--Schoenfeld error bound, so step 3 does not create an independent source mechanism.

## Representation lesson and positive survivor

Full centered square energy pays for negative deviations that Route I does not need. The strongest
survivor is the one-sided Hilbert energy

```text
P_M = sum_(m<=M) (W(m^2)-2(1-1/sqrt(2))m)_+^2.
```

Its finite convex dual ranges over nonnegative aperture weights, retaining coefficient-nonlocal
testing without the irrelevant negative channel. This was initially retained as Route I's open
source problem. Subsequent quantitative Abel audit proved its Dirichlet abscissa is exactly the C2
Xi-width coordinate, so it is now retired. Successor card:
`route-i-square-aperture-positive-excess-dual-bound.md`.

## Anti-theatre boundary

Not progress:

- assuming RH, a zero-width bound, or an RH-equivalent continuation theorem to prove the variance;
- replacing sparse square samples by a continuous integral without a trace theorem;
- bounding three correlation terms separately;
- another formal restatement of the already-proved implication.

First progress must bound the centered kernel itself or prove a source theorem that implies that
bound without importing another RH-equivalent route.

## Gates

- [x] exact kernel and conjecture formalized
- [x] exact implication to RH formalized
- [x] RH-to-correlation implication paper-proved from Schoenfeld and exact Abel summation
- [x] exact RH-equivalence and circularity classification
- [x] route-collision and anti-theatre audit
- [ ] reverse implication formalized in Lean (formal von Koch--Schoenfeld theorem absent)

## Log

- 2026-08-01 — promoted as active Route-I pivot after full scalar analytic postcomposition no-go.
- 2026-08-01 — retired as independent producer after proving exact paper equivalence to RH;
  one-sided positive-excess convex dual survives.
