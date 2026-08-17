# Nested static-local literal complexity monotonicity

- **ID:** nested-static-local-literal-complexity-monotonicity
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / PARTIALLY CLOSED
- **Source:** user-directed strengthening of the nested static-local ramp--return law
- **Statement:** At fixed operator-norm resolution, actual two-qubit-gate complexity of the nested inverse-power chain is nondecreasing throughout its claimed laboratory growth window.

## Goal

Upgrade two-sided linear envelopes to literal pointwise growth of circuit complexity, while keeping
one autonomous nearest-neighbour Hamiltonian, arbitrary support-certified one/two-qubit circuits,
and operator-norm approximation.

## Gates

- [x] 0 → 1 in-progress: statement frozen; exact-return and phase-folding attacks identified
- [ ] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] obstruction/bridge formalized: targeted Lean theorem, targeted build green, axiom audit clean
- [ ] 3 → 4 publication-ready: standalone theorem and proof with calibrated priority

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
- **Strongest positive survivor:** actual complexity has a literal strict rise from zero and a
  literal strict return drop. Within the laboratory window it is also genuinely ordered at large
  scale separation: `t ≥ 1024πs` implies `C(s) ≤ C(t)`.
- **New insight:** recurrence converts any valid deterministic monotonicity law into a necessarily
  one-sided or pre-return statement. Linear envelopes already exclude large scale-separated
  backtracking, but do not compare arbitrarily close times.
- **Status:** obstruction and scale-separated bridge are paper-proved and formalized in
  `StaticLocalComplexityMonotonicityRigidityLaw.lean`. Full all-pairs monotonicity for arbitrary
  laboratory times `s≤t` remains the frozen open core; no circuit comparison map or exact
  complexity classification in the corpus discharges it.

## Log

- 2026-08-17 — created in 1-in-progress; literal pointwise claim frozen before proof search.
- 2026-08-17 — global reading falsified; exact rise/drop and scale-separated actual-complexity
  comparison formalized. All-pairs laboratory-window conjecture remains open.
