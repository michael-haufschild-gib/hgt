# Strict-frontier bounded-gauge obstruction

- **ID:** rh-strict-frontier-bounded-gauge-obstruction
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `XiShiftedStrictFrontierAllContactArithmeticSource.lean`
- **Statement:** A contact `N(u) ~ C u^d`, `d > 0`, cannot be normalized to a nonzero finite limit by any gauge bounded on the right germ; every normalizing gauge has forced scaled limit `u^d g(u) → L/C`.

## Goal
Test the synthesis that strict-frontier integer holonomy is an obstruction to admissible bounded trivialization, rather than another zero detector.

## Gates
- [x] 0 → 1  well-posed and coefficient-faithful
- [x] 1 → 2  dependency-closed paper proof
- [x] 2 → 3  formalized as `tendsto_xiShiftedStrictFrontier_scaledGauge_of_normalizedAdmission` and `xiShiftedStrictFrontier_normalizingGauge_not_bounded`; targeted build and axiom audit pass
- [ ] 3 → 4  publication-ready

## Proof
From `N(u)/u^d → C ≠ 0` and `g(u)N(u) → L`, division gives
`u^d g(u) = (g(u)N(u))/(N(u)/u^d) → L/C` on the punctured right germ. Also `d > 0` gives `N(u) → 0`. If `g` is germ-bounded, bounded-times-vanishing tends to zero, so uniqueness of limits forces `L = 0`. Hence `L ≠ 0` forces an unbounded gauge.

## Falsification
Framework claim would fail if a bounded right-germ gauge normalized a positive-order contact to nonzero finite value. The theorem excludes that possibility exactly. It does not provide the missing global arithmetic law excluding cofinal contacts.

## Log
- 2026-08-24 — paper proof closed after corpus novelty search found contact asymptotics and integer residues, but no bounded-gauge consequence.
- 2026-08-24 — formalized in `XiShiftedStrictFrontierBoundedGaugeObstruction.lean`; axioms only `propext`, `Classical.choice`, `Quot.sound`.
