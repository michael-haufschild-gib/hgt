# Nested static-local literal complexity monotonicity

- **ID:** nested-static-local-literal-complexity-monotonicity
- **Stage:** 5-failed
- **Type:** FALSIFIED / POSITIVE SURVIVOR FORMALIZED
- **Source:** user-directed strengthening of the nested static-local ramp--return law
- **Statement:** At fixed operator-norm resolution, actual two-qubit-gate complexity of the nested inverse-power chain is nondecreasing throughout its claimed laboratory growth window.

## Goal

Upgrade two-sided linear envelopes to literal pointwise growth of circuit complexity, while keeping
one autonomous nearest-neighbour Hamiltonian, arbitrary support-certified one/two-qubit circuits,
and operator-norm approximation.

## Gates

- [x] 0 → 1 in-progress: statement frozen; exact-return and phase-folding attacks identified
- [x] 1 → 2 fully-proven: explicit counterexample and positive survivor have a complete paper proof
- [x] obstruction/bridge formalized: targeted Lean theorem, targeted build green, axiom audit clean
- [x] 3 → 4 manuscript integration: standalone theorem and proof with calibrated priority

## Approach

1. Separate global-cycle monotonicity from monotonicity restricted to the laboratory ramp window.
2. Attack global monotonicity using exact return and the positive ramp lower bound.
3. Search for a comparison map taking every circuit for a later laboratory time to a circuit of no
   greater two-qubit cost for every earlier time. Linear lower and upper envelopes alone do not
   provide such a map.
4. If the literal claim fails or remains unsupported, close the no-go with the sharp exact-return
   rigidity theorem and record the remaining half-cycle/laboratory-window core without weakening it
   into envelope monotonicity.

## No-go closure

- **Exact killing theorem/mechanism:** global-cycle monotonicity is false. Exact return makes both
  endpoint complexities zero, while every claimed laboratory-ramp point has complexity at least
  eight. A nondecreasing history on the full return cycle would be bounded above by its zero right
  endpoint and hence vanish identically; the dual left-endpoint argument kills global antitonicity.
- **Strongest positive survivor:** folded phase-tail mass, not elapsed time, controls finite-
  resolution path complexity.  General tree-cut obstruction survives arbitrary nonlocal and
  non-diagonal approximating gates.  Concrete nested path has scale-separated ordering but also
  strict nearby reversal `C(2π)≤1513<1514≤C(2π-10^-6)` inside same ramp window.
- **New insight:** linear complexity envelopes coexist with literal local backtracking.  A single
  bond crossing its `2π` cut locus can make a cheaper centered approximation available even while
  elapsed time increases.
- **Status:** `[FALSIFIED]`.  The paper proof in
  `docs/drafts/pipeline/3-formalized/path-phase-tail-capacity-and-monotonicity-counterexample.md`
  gives `L=16384`, `epsilon=1/1024`, `s=2pi-10^-6`, and `t=2pi`, all in the laboratory window, with
  `C(s)≥1514>C(t)` and `C(t)≤1513`.  The positive survivor is the path phase-tail capacity law,
  which combines a general arbitrary-circuit lower obstruction with a constructive centered upper
  circuit.  Exact lower, upper, strict reversal and laboratory-window nonmonotonicity are formalized.

## Log

- 2026-08-17 — created in 1-in-progress; literal pointwise claim frozen before proof search.
- 2026-08-17 — global reading falsified; exact rise/drop and scale-separated actual-complexity
  comparison formalized. All-pairs laboratory-window conjecture remains open.
- 2026-08-17 — all-pairs laboratory-window conjecture paper-falsified by an explicit one-gate
  downward spike at the first bond return.  Dependency-closed positive survivor and exact rational
  certificates recorded in Stage 2; Lean gate not yet started.
- 2026-08-17 — formal closure complete.  Exact early lower bound `1514`, constructive late upper
  bound `1513`, strict reversal and `not MonotoneOn` capstone pass targeted checks and axiom audit.
  Result integrated into unified manuscript; failed conjecture retired to Stage 5.
