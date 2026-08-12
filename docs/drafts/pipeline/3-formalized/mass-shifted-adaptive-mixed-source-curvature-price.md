# Mass-shifted adaptive-mixed source curvature price

- **ID:** `mass-shifted-adaptive-mixed-source-curvature-price`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3 exact open core
- **Statement:** At every higher odd shifted-Xi contact, square of literal adaptive mixed/completed `P^sharp` arithmetic source is exact numerator of a positive terminal-frontier curvature price.

## Goal

Join existing source-first adaptive arithmetic producer to actual integral Lipschitz frontier law.
Producer must remain inside rational--Gamma/von-Mangoldt formation before aggregation. No
orientation map, fixed reporter, numerical estimate, or RH premise is allowed.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, hostile alternatives isolated
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, direct check, target build, axiom audit
- [ ] 3 → 4  publication-ready: not attempted

## Conjecture loop

1. `[CONJECTURE]` Source sign alone yields a uniform frontier increment. **Failed.** Existing
   singular landing gives source value but no degree-uniform lower bound on source magnitude,
   transverse conditioning, or integral Lipschitz denominator.
2. `[CONJECTURE]` Scalar Riccati contraction controls every unpriced positive-chamber gap.
   **Failed.** Positive solutions of `U' < -U^2` may decay hyperbolically on a complete right ray;
   Riccati sign gives no finite positive lifetime.
3. `[CONJECTURE]` Literal source magnitude is exactly the missing curvature numerator at odd
   contact. **Survives.** Existing source law gives `S=2δ`; parity-complete null-pair energy uses
   `δ^2`. Substitution yields exact source price `S^2/4`.

## Paper proof

Let `P` be degree-`n` monic null polynomial, assume Padé defects vanish below
`2*n+(2*m+1)`, and let first odd defect `δ` be nonzero. Put

```text
U=P*X^m,  V=P*X^(m+1),
a=L(V^2), A=U-δ/(|a|+1)V,
S=nondegenerateNullFlagCompletedArithmeticSource(w,n+m,U,B).
```

Existing singular source landing proves `S=2δ` for every adjacent polynomial `B`. Existing
adaptive null-pair identity gives

```text
L(A^2) = -δ^2 * (2*(|a|+1)-a) / (|a|+1)^2 < 0.
```

Actual integral Lipschitz theorem then gives

```text
w^2 + ((S/2)^2 * (2*(|a|+1)-a) / (|a|+1)^2) / Lip(A)
  <= terminalFrontier(n+m).
```

This is `[PROVED HERE]` once the two corpus identities are substituted. Every factor in `S` was
formed before arithmetic aggregation. Result is exact but does not lower-bound price uniformly.

## Literature and novelty boundary

Broad arXiv audit found model-specific ladder/Toda/Riccati/Painlevé laws for deformed Laguerre and
Freud weights, large-degree Hankel asymptotics, and fixed-support Christoffel estimates. No audited
source identifies a completed prime--Gamma adaptive polynomial source with a terminal-frontier
Lipschitz curvature price. Novelty remains unverified.

Audited primary sources:

- Lyu--Lyu, [perturbed Laguerre Hankel determinant and generalized Painlevé III'](https://arxiv.org/abs/2603.00391);
- Mu--Lyu, [multivariable deformed Laguerre Hankel determinants and generalized Painlevé V](https://arxiv.org/abs/2410.22780);
- Min--Ding, [sextic Freud Hankel determinant and orthogonal polynomials](https://arxiv.org/abs/2412.10815);
- Henrion--Lasserre, [infinite-dimensional Christoffel function](https://arxiv.org/abs/2407.02019).

## Exact remaining burden

False RH already forces cofinal strict priced renewals. Remaining quantitative theorem must prevent
the dimensionless source efficiency

```text
(S/2)^2 * (2*(|a|+1)-a) / ((|a|+1)^2 * Lip(A))
```

from becoming summably negligible along every cofinal renewal schedule, or replace this scalar
efficiency by a stronger conserved aggregate.

## Log

- 2026-08-12 — created in `1-in-progress`; two false scalar routes killed; exact source-squared
  curvature bridge isolated for Lean.
- 2026-08-12 — `[PROVED HERE]`; formalized exact source/defect identity, positivity of actual
  integral-Lipschitz price, frontier payment, and closed conjunction in
  `XiShiftedAdaptiveMixedFrontierPrice.lean`; umbrella wired.

## Lean certificate

- `xiShiftedAdaptiveMixedOddContactFrontierPrice`;
- `xiShiftedAdaptiveMixedOddContactFrontierPrice_eq_firstOddDefect`;
- `xiShiftedAdaptiveMixedOddContactFrontierPrice_pos`;
- `add_xiShiftedAdaptiveMixedOddContactFrontierPrice_le_terminalFrontier`;
- `xiShiftedAdaptiveMixedOddContactFrontierPrice_pos_and_le_terminalFrontier`.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/XiShiftedAdaptiveMixedFrontierPrice.lean` — PASS;
- `lake build GaloisForLFunctions.RHTower.XiShiftedAdaptiveMixedFrontierPrice` — PASS;
- `#print axioms` for all four theorems — only `propext`, `Classical.choice`, `Quot.sound`;
- `scripts/formal_tools.py research` indexes all four declarations;
- `scripts/formal_tools.py lint` reports only unrelated pre-existing/concurrent unreachable-module
  debt; new module is umbrella-reachable and absent from error list.
