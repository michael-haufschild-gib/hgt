# Xi reflection-incidence positive cofinal regularization no-go

- **ID:** TRACE1-PREG
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `XiReflectionIncidenceTraceOneSourceConvergence.lean`; corpus searches for trace-one source landing, positive regularization, cofinal damping, and bounded prime-prefix budgets
- **Statement:** Any nonnegative coefficient-recovering cofinal regularization of the literal trace-one reflection-incidence source has even one cofinal family of bounded-return scales exactly when the undamped source is nuclear; globally this is exactly RH.

## Goal

Kill proof chain

`positive Abel/heat/Cesaro/source-dependent damping of literal trace-one cyclic residues`
`=> cofinally recurring bounded ordinary-prime prefix budgets`
`=> trace-one reflection-incidence source landing`
`=> endpoint nuclear incidence admission`
`=> every Xi divisor lies on the critical line`
`=> RH`.

This closes positive cofinal regularization as an independent producer route. Regularization does
not reduce the RH burden even when its weights may depend on the source, need not be monotone, and
are required to return below one common budget only on an arbitrarily sparse cofinal subsequence.

## Gates

- [x] 0 → 1 in-progress: exact corpus-derived source and RH chain; competing ordinary, uniformly bounded, and bounded-return formulations attacked
- [x] 1 → 2 fully-proven: dependency-closed paper proof below
- [x] 2 → 3 formalized: Lean module, targeted build, axiom audit, umbrella wiring
- [ ] 3 → 4 publication-ready

## Conjecture and hostile audit

For a nonnegative ordered source `f(n)`, let `w(N,n)` be arbitrary nonnegative weights such that
`w(N,n) → 1` for every fixed `n`. Suppose one real `C` has the following weak recurrence property:
above every scale threshold `N₀`, some `N ≥ N₀` makes every ordinary prefix satisfy

`Σ_{n<M} w(N,n) f(n) ≤ C`.

Then `f` is summable. Conversely, summability supplies the constant regularization `w=1`.

Hostile weakening removed uniform boundedness in `N`, monotonicity of `w`, uniform convergence in
`n`, a fixed damping formula, and arbitrary-finset control. Only increasing-prime prefixes and
sparse cofinal bounded returns remain. The theorem still holds.

## Paper proof

Fix a prefix length `M`. Pointwise recovery on its finitely many coefficients gives a scale `N₀`
such that `w(N,n) ≥ 1/2` for every `n<M` and every `N≥N₀`. Choose one bounded-return scale
`N≥N₀`. Nonnegativity of `f` gives

`(1/2) Σ_{n<M} f(n) ≤ Σ_{n<M} w(N,n)f(n) ≤ C`.

Thus every undamped prefix is bounded by `2C`; the nonnegative series is summable. The converse is
the constant family `w(N,n)=1`, whose prefixes are bounded by the undamped total mass.

For the literal source

`f_rho(n) = xiReflectionIncidencePrimeTraceOneSourceMass rho (nthPrimeEquiv n)`,

the corpus proves nonnegativity, coefficient-faithful identification with the endpoint Schatten-one
incidence mass times the nonzero first Xi jet, enumeration-invariant summability, and

`Summable f_rho ↔ Re(rho)=1/2`.

Hence positive cofinal regularization at `rho` is equivalent to critical-line placement, and the
universal landing is equivalent to RH.

The contrapositive is strengthened. If `rho` is off line, then for every coefficient-recovering
weight family and every budget `C`, there is `N₀` such that every `N≥N₀` has some increasing-prime
prefix whose weighted literal source mass exceeds `C`. Transient weights need not even be positive
for this escape theorem; finite coefficient recovery alone eventually exposes the divergent
positive prefix.

## No-go closure

- **Exact killing theorem/mechanism:** finite-prefix coefficient recovery transfers every sufficiently large undamped positive prefix into every late regularized scale. Therefore even sparse cofinal bounded returns force the original trace-one source to be summable and hence force RH.
- **Strongest positive survivor:** `xiReflectionIncidenceTraceOnePositiveRegularizedPrefixes_eventually_exceed_of_offLine` proves eventual, every-scale escape above every budget for every coefficient-recovering family at every off-line Xi fibre.
- **New insight:** Abel, heat, Cesaro, adaptive source damping, and cofinal subsequence selection cannot soften the shared trace-one incidence producer while retaining coefficient fidelity and norm positivity. A surviving producer must introduce signed cancellation before norms are taken; coefficient loss or cofinal evacuation does not close the stated RH chain.
- **Status:** dependency-closed and formalized. Connes--Consani analyze limits of a positive semilocal cutoff attempt (`arXiv:1910.14368`); Leonetti studies abstract regular summability matrices (`arXiv:2012.03311`). The bounded search found no trace-one Xi reflection-incidence theorem, no coefficient-faithful prime-residue application, and no every-late-scale off-line escape law. Priority remains `[NOVELTY UNVERIFIED]` pending expert review.

## Lean certificate

- Module: `formal/GaloisForLFunctions/RHTower/XiReflectionIncidencePositiveCofinalRegularizationNoGo.lean`
- General classification: `positiveCofinalOrderedRegularizationFrequentlyBounded_iff_summable`
- Closed RH capstone: `riemannHypothesis_iff_xiReflectionIncidenceTraceOnePositiveCofinalRegularizationLanding`
- Sharp survivor: `xiReflectionIncidenceTraceOnePositiveRegularizedPrefixes_eventually_exceed_of_offLine`
- Direct `lake env lean`: PASS
- Targeted `lake build GaloisForLFunctions.RHTower.XiReflectionIncidencePositiveCofinalRegularizationNoGo`: PASS, 11,435 jobs, 33s
- Axioms: only `propext`, `Classical.choice`, `Quot.sound`
- Formal lint: no forbidden declaration or reachability defect in this module; global lint remains blocked by unrelated pre-existing umbrella omissions.
- Wired into `formal/GaloisForLFunctions/RHTower.lean`; no umbrella build run.

## Log

- 2026-08-29 — D2 direct lower bound rejected as already exactly RH; shared trace-one incidence producer selected from corpus topology.
- 2026-08-29 — ordinary convergence, arbitrary positive damping, and uniform-budget formulations weakened to sparse cofinal bounded returns and proved equivalent to undamped nuclearity.
- 2026-08-29 — paper theorem formalized, axiom-audited, target-built, and promoted to Stage 3.
