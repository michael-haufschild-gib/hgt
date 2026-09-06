# Eventual cellwise sign for the ordinary arithmetic remainder

- **ID:** EDQ-CELL-S
- **Stage:** 5-failed
- **Type:** FALSIFIED — exact symbolic source counterexample
- **Scope:** the all-parameter cellwise sign strategy S, not the whole-tail conjecture R or RH.

## Frozen assertion

For each `sigma>0` and `t>0`, all sufficiently late unit-cell contributions to the imaginary part of the Bernoulli-tail representation are nonpositive. The source cells are

`J(sigma,t;m)=integral_(m..m+1) ((fract(x)^2-fract(x))/2) x^(-sigma-2) sin(t log x) dx`.

The intended use was to prove a whole-tail sign without estimating cancellation between cells.

## Exact killing mechanism

Set `t=pi/log(2)`. On the interior of `[2^k,2^k+1]`, the phase is strictly between `k*pi` and `(k+1)*pi`; this follows from `2^k+1<=2^(k+1)`. The periodic quadratic is strictly negative there, and the power weight is strictly positive for every real `sigma`. Hence

`(-1)^k J(sigma,pi/log(2);2^k)<0`.

Odd depths provide positive cells beyond every proposed cutoff. The parameter is literal and fixed, but is not asserted to be a zeta zero. This therefore does not refute a different condition restricted to zeros.

## Strongest positive survivor and source connection

S+ is the exact alternating sign classification, including both signs arbitrarily far out and all real `sigma`. Its paper proof is the phase-window argument above followed by strict positivity of an integral on an interval. No numerical data or unproved lemma is needed.

`ArithmeticSuccessorCellPhase` formalizes this law. Its complex cell equals the normalized difference of the actual ordinary remainders at adjacent cutoffs. Finite cell sums preserve the final endpoint exactly, and ordinary infinite cutoffs converge to the initial normalized remainder for `Re(s)>0`, `s!=1`. This connection rules out treating the example as an arbitrary coefficient perturbation.

**New insight for this attempt:** local cells keep both signs indefinitely even at one fixed low height; a conjectured eventual sign of the *complete tail* cannot be derived from eventual signs of its individual cells. Aggregation, phase transport, and inter-cell cancellation remain available. The elementary sign classification itself is not claimed as literature-new mathematics.

**Status:** dependency-closed paper proof; scratch and source checks passed. Final leaf build and axiom/lint audit are recorded in the [formal certificate](../3-formalized/arithmetic-successor-cell-phase.md). The separate [whole-tail conjecture R](../1-in-progress/arithmetic-successor-phase-threshold.md) remains open. RH remains unproved.
