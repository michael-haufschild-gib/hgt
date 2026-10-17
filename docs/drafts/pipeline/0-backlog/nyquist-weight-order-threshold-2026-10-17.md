# Nyquist weight order and the threshold for an integrable residual

- **ID:** nyquist-weight-order-threshold-2026-10-17
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Scope:** Infinite-Grid Tail Rigidity Beyond Trap 5; explicit weight producers.
- **Source:** The integrable polar residual package and the field guide
  `formal/GaloisForLFunctions/BiScaleUncertainty/README.md` (read-only).
- **Statement:** For beta>0 and Taylor degree m>=0, the logarithmic-cell
  Taylor producer for cosh(beta x) has an integrable residual exactly when
  beta<m+1.
- **Status:** Candidate only; no completed paper proof, new Lean or contribution count.

## Goal

Determine the exact exponential weights for which cell-average polar production
admits a bounded correction on arbitrary bounded continuous signed inputs.
Identify the least explicit weight-producer order that restores a summable error.
This changes the weight approximation, without assuming a bound on derivatives
or spectral second moments of the source.

## Candidate construction

On I_n=[log n,log(n+1)], let w_beta(x)=cosh(beta x), and set

    p_(beta,m,n)(x)=sum_(j=0..m) w_beta^(j)(log n) (x-log n)^j/j!.

The proposed residual kernel is w_beta-p_(beta,m,n) on each half-open cell.
The conjectured cell-mass asymptotic for beta>0 is

    alpha_(beta,m,n) / n^(beta-m-2) -> beta^(m+1)/(2(m+2)!).

Consequently, below the threshold, the actual all-tail residual operator should
have exact norm A_N with

    A_N ~ beta^(m+1)/(2(m+2)!(m+1-beta)) * N^(beta-m-1).

At and above the threshold, the positive kernel should have infinite mass and
unbounded action on compactly supported continuous inputs of supremum norm one.
The beta=0 case has zero residual. Actual source witnesses, if available, would
strengthen the obstruction; they must be constructed, not assumed.

## Approach and prior-corpus gate

Taylor's integral remainder and the two cell-width bounds expose a positive
power-series comparison. Check all exponent endpoints, positivity, infinite-tail
summation and the precise leading coefficient before promoting this candidate.
Then reuse the actual partition and operator construction from the preceding
package, with all new analytic bounds derived from the explicit weight.

Focused current-corpus search `/tmp/nyquist-exponent-frontier-deep.json`
completed without errors or unfinished stages. All 20 candidate statements and
20 source arguments were inspected. Inventory coverage was complete and current;
semantic coverage was unmeasured, refresh deferred to the background indexer,
and every candidate was source-only. The suggested ingredient set concerns
decaying Levy weights, not growing-weight Taylor residuals. Existing results
found here include the preceding beta=1/2, m=0 construction and its inputs;
they do not establish the proposed threshold classification. A focused lexical
cross-check is `/tmp/nyquist-exponent-taylor-lexical.txt`.
The previous point-sample search
`/tmp/nyquist-point-producer-deep.json` found derivative-free cell and dyadic
quadrature bounds retaining the polar-density cost. A derivative bound on the
source is not a resolution of that remaining uniform-control problem.

## Gates

- [ ] Current corpus inspected; exact novelty boundary established.
- [ ] Dependency-closed paper proof and sharp positive-survivor audit.
- [ ] Actual positive kernel, bounded operator and threshold formalized in Lean.
- [ ] All direct leaves, axioms, API entries, imports and formal lint checked.
- [ ] Count once only if the complete classification adds a substantive tool.

## No-go closure

If the proposed threshold or asymptotic fails, extract the exact corrected
classification or replacement producer. Do not retire the route with a negation
alone. This candidate is presently unproved, not falsified.
