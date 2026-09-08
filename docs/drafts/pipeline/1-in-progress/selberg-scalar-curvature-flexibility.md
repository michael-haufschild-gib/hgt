# Scalar modular curvature versus the quarter bound

- **ID:** SELBERG-SCALAR-CURVATURE-FLEXIBILITY
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Parent:** [Selberg conjecturing loop](selberg-quarter-conjecturing-loop.md), cycle 39.
- **Previous goal turn:** progress: uniform original-source tails and exact compact-orbit mass proved and audited.
- **Goal:** Test whether scalar modularity, positive curvature, cusp decay, and finite amplitude mass can force a spectral quarter lower bound; preserve the full Maass goal.

## Corpus evidence and first attempt

Explicit --any congruence/finite-quotient/nodal discovery reached 1737 declarations in 362 modules; gap/Poincare/Hecke discovery reached 1660 in 275. WeightedGraphSpectralGap explicitly assumes its gap estimate. The actual SelbergMaassTraceDirection source supplies modular permutation covariance and amplitude-weighted horizontal zero means, not a finite-quotient spectral gap. SelbergMaassChordEnergy retains its actual inverse-amplitude resistance; previous nodal proofs prevent simply dropping that cost. A follow-up Hecke/expander/nonbacktracking/Cayley-graph query returned 3 declarations in one quadratic-Hecke-base module, not an operator estimate for the Maass source. These are coverage counts and selected source inspections.

## Second conjecture and proof attempt

The scalar package may admit non-Maass examples for arbitrarily small positive spectral parameters. The corpus's actual absolutely convergent Eisenstein Poincare series has proved modular generator invariance and literal first and second derivative identities. At real parameter s=2 its summands should be positive, and its identity-row terms should imply E(z)>=y². Its positive-sign hyperbolic Laplacian is 2E.

For t>0, try the literal function a=E^(-t). The chain rule predicts

y²*Delta(a)+lambda*a = t*(t+1)*E^(-t-2)*y²*|grad E|² + (lambda-2t)*a.

Thus t=lambda/4 would make curvature strictly positive for any lambda>0. E>=y² would give cusp decay of a. Modular continuity and the standard finite-volume cell would then give finite amplitude mass; the complete Stokes limit must still be justified before claiming the same total-curvature budget as the actual Maass source. This is a candidate countermodel to the scalar shortcut, not to Selberg. Positivity, exact chain-rule transport, source regularity, and tail integration all remain to be proved for the literal series.

## Positive survivor required before closure

If the candidate succeeds, formalize the exact power-transform identity and actual modular family, not merely a logical statement about arbitrary scalar data. The surviving lesson must identify which vector or arithmetic Maass constraint remains essential. Do not retire the full curvature route or infer a counterexample to Selberg from these scalar models.

## Audit

No new Lean module or build yet. The explicit --any Eisenstein/power-Laplacian/positive-supersolution/reciprocal-curvature/ground-state-transform search reached 1736 declarations in 106 modules. Inspected actual Eisenstein convergence, derivative/eigen-equation, and generator-invariance sources; positivity and the power transform remain under investigation.
