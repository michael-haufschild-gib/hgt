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

Thus t=lambda/4 makes curvature strictly positive for any lambda>0. E>=y² gives cusp decay of a. The first four modules below now prove these claims for the literal series. The complete Stokes limit must still be checked before claiming the same total-curvature budget as the actual Maass source. This is a candidate countermodel to the scalar shortcut, not to Selberg. The models have power-law cusp decay; stronger exponential or vector-valued Maass constraints are not supplied.

## Source-derived proof progress

1. `SelbergPositiveEisenstein`: two actual primitive identity rows prove E>=y²>0. Real projections of the original differentiated series give the original eigen-equation.
2. `SelbergEisensteinPlane`: the corpus's global Fourier uniqueness identifies the same original series with the smooth full Fourier–Bessel sum. This establishes actual Frechet derivatives and y²*Delta(E)=2E, rather than relying only on named formal jets.
3. `SelbergPowerCurvature`: complete real-power chain rule, exact positive curvature decomposition for a=E^(-lambda/4), positive model values, original S/T invariance, and uniform power-law cusp decay.
4. `SelbergEisensteinBounds`: actual derivative summands give |E_x|<=4E/y and |E_y|<=6E/y, hence y²|grad E|²<=52E². Curvature is bounded by [52(lambda/4)(lambda/4+1)+lambda/2]a. The actual vertical model derivative is bounded by (3lambda/2)y^(-lambda/2-1).

Each of these four completed scratch proofs and needed source oleans has passed. The boundary scratch extends S/T to the full modular group and differentiates the actual invariance; its geometric simplifications are being checked. The mass scratch uses the corpus's proved finite full-domain hyperbolic area, followed by literal Stokes and exhaustion. It has not yet been checked.

## Positive survivor required before closure

If the candidate succeeds, formalize the exact power-transform identity and actual modular family, not merely a logical statement about arbitrary scalar data. The surviving lesson must identify which vector or arithmetic Maass constraint remains essential. Do not retire the full curvature route or infer a counterexample to Selberg from these scalar models.

## Audit

Final single-module audits, umbrella wiring, axiom checks, refreshed index, and lint remain pending. The explicit --any Eisenstein/power-Laplacian/positive-supersolution/reciprocal-curvature/ground-state-transform search reached 1736 declarations in 106 modules. A broad continuous-partial/negative-power search reached 166 declarations in 108 modules and exposed the actual joint-smoothness bridge. An additional OR search for modular potentials, full domains, power integrals, and positive measures reached 271 declarations in 125 modules; inspected the existing literal full-domain area and source exhaustion proofs. These are discovery counts, not claims that every hit's proof was read.
