# Route I — square-aperture von Mangoldt correlation bound

- **ID:** `route-i-square-aperture-von-mangoldt-correlation-bound`
- **Stage:** `1-in-progress`
- **Type:** `CONJECTURE`
- **Status:** `[CONJECTURE] [OPEN CORE] [SOURCE-PURE] [COEFFICIENT-NONLOCAL]`
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

## Why this pivot survives

- It controls literal von-Mangoldt coefficients before analytic continuation.
- It is nonlocal in coefficients, so first-mode scalar-germ sign rigidity does not apply.
- It does not normalize into `logDeriv XiC`; retired C2 does not own it.
- It is not Möbius/squarefree cancellation and does not map to Route E.
- Existing Lean proves this exact conjecture implies RH through square-sampled positive-excess
  `L^2` energy.

## Hard problem

Prove cancellation between the pair term, centered first moment, and deterministic main square.
Their separate bounds are far too large. Required input resembles a sparse square-trace Selberg
variance estimate for a discontinuous dyadic window, not ordinary continuous mean square.

## Conjecture ladder

1. **Strong pointwise parent:** all-`epsilon` subpower upper bound for every large aperture.
2. **Square pointwise parent:** same bound only at `m^2`.
3. **Active correlation core:** near-linear centered `L^2` energy on `m^2`.
4. **Weak downstream gate:** every-abscissa square-sampled positive-excess Dirichlet energy.

Step 3 implies step 4 unconditionally. No reverse implication is claimed.

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
- [x] route-collision and anti-theatre audit
- [ ] unconditional near-linear correlation estimate
- [ ] dependency-closed proof of the conjecture

## Log

- 2026-08-01 — promoted as active Route-I pivot after full scalar analytic postcomposition no-go.
