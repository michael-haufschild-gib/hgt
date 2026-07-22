# Infinite semimetric graph-inverse and exact incidence law

- **ID:** `infinite-semimetric-graph-inverse-incidence-law`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[UNIVERSAL INFINITE LAW] [CCM CARRIER]`
- **Scientific status:**
  `[PROVED IN LEAN] [EXTERNAL NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/InfiniteSemimetricGraphInverse.lean`
- **Parent:** `infinite-semimetric-symmetrization-closed-range-law.md`

## Frontier corrected

Finite rank-two completion cannot detect CCM cofinal topology: finite-dimensional ranges are
closed. Previous parent theorem proved bounded support inversion exists exactly at closed range.
That diagnosis leaves nonclosed branch, which natural CCM exterior carrier is expected to occupy.

This theorem constructs unconditional arbitrary-Hilbert-space replacement. No finite type,
dimension, rank, compactness, trace, positivity, or closed-range assumption occurs in graph inverse
theorem.

## Universal graph-inverse law

For bounded `T : H ->L H`, restrict `T` to `(ker T)^perp` and invert it as partially defined linear
operator:

```text
G_T : range T -> (ker T)^perp.
```

Lean proves:

```text
domain G_T = range T,
T (G_T y) = y,
G_T y = unique preimage of y orthogonal to ker T,
graph G_T is closed.
```

The graph is coordinate swap of closed graph of bounded restriction `T|(ker T)^perp`. Thus
nonclosed range does not destroy canonical inversion; it forces inverse into closed partial
operator category. If range is nonclosed, Lean proves domain of `G_T` is nonclosed. If `T` is
self-adjoint, Lean proves `G_T` is formally symmetric on its exact domain.

## Exact incidence symmetrizer

Let `T=T*`, let `D` be arbitrary bounded operator, and let `P` be orthogonal projection onto
`(ker T)^perp`. Define exact incidence domain

```text
I(T,D) = {x | D* (T x) in range T}.
```

On `I(T,D)` define partially defined operator

```text
GraphSymm(T,D) x = (1/2) (P D P x + G_T (D* T x)).
```

Lean proves, unconditionally:

```text
domain GraphSymm(T,D) = I(T,D),
T (GraphSymm(T,D) x) = (1/2) (T D P x + D* T x),
<T GraphSymm(T,D) x, y> = <T x, GraphSymm(T,D) y>,
ker T <= I(T,D),
GraphSymm(T,D) x = 0 for x in ker T.
```

Incidence condition is exact typing condition, not hypothesis pasted onto theorem: it is operator's
defined domain. Defect rank and radical rank are unrestricted.

## Scientific content

Universal law replaces false dichotomy "bounded inverse or no inverse" with three exact objects:

```text
algebraic inverse: always exists on range T;
closed graph inverse: always exists with domain range T;
bounded everywhere support inverse: exists exactly when range T is closed.
```

For semimetric symmetrization, nonclosed branch reduces exactly to range incidence
`D*Tx in range T`. This is structural connector absent from finite rank-two treatment.

## Claim-to-Lean closure

| Claim | Declaration |
|---|---|
| injective support restriction | `supportRestriction_toFun_ker_eq_bot` |
| restriction graph closed | `supportRestriction_isClosed` |
| inverse graph closed | `closedSupportInverse_isClosed` |
| exact domain | `closedSupportInverse_domain` |
| nonclosed phase has nonclosed domain | `not_isClosed_closedSupportInverse_domain_of_not_isClosed_range` |
| exact right inverse | `closedSupportInverse_rightInverse` |
| agreement with algebraic inverse | `closedSupportInverse_apply_eq_algebraicSupportRangeEquiv_symm` |
| formal symmetry | `closedSupportInverse_formalSymmetric` |
| exact incidence domain | `mem_graphSemimetricSymmetrization_domain_iff` |
| pointwise metric formula | `metric_graphSemimetricSymmetrization_apply` |
| radical lies in domain | `graphSemimetricSymmetrization_mem_domain_of_mem_ker` |
| radical annihilation | `graphSemimetricSymmetrization_apply_eq_zero_of_mem_ker` |
| metric symmetry | `graphSemimetricSymmetrization_metricSymmetric` |

## Novelty audit

Closed inverses of injective closed operators and graph norms are classical. No priority claim is
made for those ingredients. Primary-source audit found current work on Moore--Penrose inverses of
unbounded closable operators and closed linear relations:

- https://arxiv.org/abs/2405.11480
- https://arxiv.org/abs/2502.07361
- https://arxiv.org/abs/1510.01534

No exact match was found for `GraphSymm(T,D)` with domain `D*Tx in range T`, metric symmetry, and
radical annihilation. Potential contribution is exact universal incidence symmetrizer and its
placement as nonclosed branch of CCM semimetric completion. Search non-detection is not proof of
novelty; external priority for full formula and fixed-domain law remains unverified.

## Exact remaining CCM/RH bridge

Abstract graph relation now exists. Still missing:

1. instantiate `T` and `D` with actual CCM boundary weight and Weil clock;
2. prove source vectors satisfy exact incidence `D*Tx in range T` on required core;
3. prove resulting graph-domain Evans/Feshbach operator has appropriate closed/Fredholm behavior;
4. prove divisor-preserving cofinal transfer to `Xi`;
5. RH.

No item is assumed or claimed.

## Gates

- [x] arbitrary Hilbert-space carrier
- [x] no finite-rank restriction
- [x] closed graph inverse without closed range
- [x] exact inverse domain and right-inverse law
- [x] exact graph-symmetrizer incidence domain
- [x] metric symmetry and radical annihilation
- [x] direct Lean check
- [x] axiom audit (`propext`, `Classical.choice`, `Quot.sound` only)
- [ ] independent operator-theory audit
- [ ] external priority audit
- [ ] actual CCM connector
- [ ] divisor-preserving cofinal transfer

## Log

- 2026-07-22 -- Rejected finite theorem as universal endpoint.
- 2026-07-22 -- Proved bounded closed-range phase law.
- 2026-07-22 -- Constructed canonical closed partial inverse on exact range domain.
- 2026-07-22 -- Constructed exact incidence graph symmetrizer.
- 2026-07-22 -- Proved metric symmetry and radical annihilation in Lean.
- 2026-07-22 -- Axiom audit passed with standard Lean quotient/classical axioms only.
