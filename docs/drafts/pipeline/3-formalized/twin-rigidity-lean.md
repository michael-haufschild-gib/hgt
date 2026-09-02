# Twin rigidity: every twin factorization of ξ is a square root dressed by a unit

- **ID:** LADDER-LEAN-TWINRIG
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/multiplicity-parity-ladder-route.md`, gate 7 ("Next move" rigidity branch)
- **Statement:** for any twin factorization `(a, d)` of ξ on `Re s > ½` there are an analytic
  square root `g` of ξ and an analytic nonvanishing `v` with `a = g v`, `g = d v`; conversely
  `(g v, g/v)` is a twin for every such `g, v`; the twin set is empty or a torsor under analytic
  units over the diagonal twin.

## Lean
| module | declarations |
|---|---|
| `GaloisForLFunctions.RHTower.TwinRigidity` | `isSimplyConnected_rightHalf`, `twin_analyticOrderAt_ne_top` (via the corpus`s `xi_order_ne_top`), `twin_eq_sqrt_mul_unit`, `twinFactorization_of_sqrt_mul_unit`, `twinFactorization_iff_exists_sqrt` |

Inputs reused: `TwinFactorization`, `rhLadder_one_iff_twinFactorization`,
`rhLadder_one_iff_sqrt_rightHalf`, `localQuotientOn_analytic_nonvanishing_factorization`,
`Bottcher.exists_differentiableOn_pow_eq`, `xi_ne_zero_of_one_le_re`. Axioms:
`propext, Classical.choice, Quot.sound`. Wired into `GaloisForLFunctions.RHTower`.

## Log
- 2026-09-02 — created at stage 3.
