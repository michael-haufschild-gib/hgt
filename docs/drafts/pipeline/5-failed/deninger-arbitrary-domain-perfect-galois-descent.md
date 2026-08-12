# Failed: arbitrary-domain perfect Galois descent for rational Witt vectors

- **ID:** `deninger-arbitrary-domain-perfect-galois-descent`
- **Stage:** 5-failed
- **Type:** FALSIFIED WITH LEAN-FORMALIZED POSITIVE SURVIVOR
- **Source:** Christopher Deninger, *Rational Witt vectors and associated sheaves*,
  arXiv:2508.05329v1, displayed Theorem 1.2 (source label `t1.1`, equation label `eq:4`)
- **Statement:** For every integral domain `A` with perfect quotient field, the source claims that
  `W_rat(A)` equals the absolute-Galois fixed part of the reduced monoid algebra of the absolute
  normalization.

## Goal

Determine whether the published arbitrary-domain descent theorem can be used as Route L source
infrastructure and formalize it without importing its conclusion.

## No-go closure

- **Exact killing mechanism:** Set
  `A=ℚ[X²,X³]={P∈ℚ[X] | coeff_X(P)=0}` and `t=X³/X²∈Frac(A)`.  The fraction field is perfect,
  `t²=X²` makes `t` integral over `A`, and the equation `aX²=X³` would force the forbidden linear
  coefficient of `a` to be one, so `t∉A`.  The absolute-normalization Teichmüller class `[t]` is
  absolute-Galois fixed because `t` belongs to the base fraction field.  If `[t]` descended from
  `W_rat(A)`, its first power-series coefficient would force `t` into the image of `A`, a
  contradiction.
- **Strongest positive survivor:** If every integral `x∈Frac(A)` has a Teichmüller preimage from
  `W_rat(A)`, then `x` lies in `A`.  Consequently the claimed descent property forces `A` to be
  integrally closed.
- **New insight:** Normality is logically necessary for the rational-Witt Galois-descent layer.
  Route L cannot use the source theorem for arbitrary domains; its valid replacement frontier is
  a corrected normal-domain theorem, with the imperfect-field divisibility condition handled
  separately.
- **Status:** Counterexample and survivor are unconditional Lean theorems in
  `GaloisForLFunctions.RHTower.DeningerRationalWittDomainDescentCounterexample`.  Direct Lean check,
  targeted module build, and axiom audit pass.  Final declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`.

## Formal certificate

- `deningerRationalWittTeichmullerPreimage_exists_coefficient`
- `deningerRationalWittTeichmullerDescent_implies_integralClosedness`
- `deningerCuspT_isIntegral`
- `deningerCuspT_not_in_base`
- `deningerCuspNormalization_intersection_strict`
- `deningerCuspPerfectGaloisFixed_counterexample`

## Log

- 2026-08-12 — source claim refuted; exact cusp counterexample and normality survivor formalized.
