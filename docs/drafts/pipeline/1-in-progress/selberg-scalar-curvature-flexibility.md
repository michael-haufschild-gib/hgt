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

5. `SelbergEisensteinBoundary`: original S/T invariance extends to every modular matrix. Differentiation gives the reciprocal-square Jacobian; translation cancels side currents and inversion cancels the oriented unit-circle currents. The literal planar Green theorem then leaves only the actual top current.
6. `SelbergEisensteinMass`: full-domain mass and curvature are integrable. The actual Laplacian integral is zero by the proved top-current limit and domain exhaustion. Hence integral(q)=lambda*integral(a), with strictly positive finite amplitude mass.

7. `SelbergScalarCurvatureFamily`: the actual hyperbolic Laplacian and curvature are modular invariant; both full integrals transport to the standard hyperbolic cell. The curvature/mass ratio is exactly lambda for every lambda>0. `no_positive_uniform_comparison` and `no_scalar_quarter_comparison` are closed negative statements about this literal family.

All seven complete scratch proofs and all seven needed source oleans have passed without new warnings. The exact source family, its modularity, integrability, positive mass, and complete Stokes budget are now proved in Lean. Final build audits remain in progress below.

## Dependency-closed paper argument

Write E=(1/2)sum_(c,d primitive) [y/((cy)^2+(cx+d)^2)]^2. Every summand is nonnegative; the two pairs (0,1) and (0,-1) contribute y² after the half factor. The already-proved original series/jet identities and the globally equal smooth Fourier–Bessel representative give E>0, actual smoothness, modular invariance, and y²*Delta(E)=2E.

For arbitrary lambda>0 put t=lambda/4 and a=E^(-t). The actual second chain rule gives

q=y²*Delta(a)+lambda*a=t(t+1)E^(-t-2)y²|grad E|²+(lambda/2)a>0.

The original summand derivative bounds imply y²|grad E|²<=52E², so 0<q<=C_lambda*a, where C_lambda=52t(t+1)+lambda/2. E>=y² implies a<=y^(-lambda/2). On the full closed modular domain y>=1/2, so a is bounded above by (1/2)^(-lambda/2). The corpus proves integrability of the hyperbolic density 1/y² on this actual domain. Continuous positive a and q therefore have integrable weighted densities. A rectangle in the domain has positive area, so integral(a/y²)>0.

The actual derivative rule and |E_y|<=6E/y imply |a_y|<=(3lambda/2)*a/y<=(3lambda/2)y^(-lambda/2-1). Its unit-width top integral tends to zero. Original modular invariance gives exact differentiated side and oriented arc cancellations. The actual Green formula on each truncated standard cell therefore identifies integral(Delta a) with the top current. Since Delta a=q/y²-lambda*a/y² is integrable on the full domain, actual exhaustion passes to the limit and gives integral(Delta a)=0. Thus integral(q/y²)=lambda*integral(a/y²).

Conformal covariance of the actual C² Laplacian and modular invariance of a imply modular invariance of q. The corpus's exact full-domain change of variables transfers both weighted integrals to the standard hyperbolic modular cell. Consequently the actual curvature-to-amplitude mass ratio is exactly lambda, for every positive lambda. For any proposed uniform positive constant c, selecting lambda=c/2 contradicts c*mass<=curvature; c=1/4 is a particular case. This is a closed result about the constructed scalar family, not a conditional Selberg wrapper.

## Scope and surviving direction

Only the scalar shortcut using smooth modularity, positive curvature, vanishing cusp values/current, finite positive mass, and the exact total-curvature identity is excluded. Exponential Maass cusp decay, the common component eigen-equation, permutation-equivariant source directions, amplitude-weighted component mean zero, and nodal constraints are not supplied by this family. No Maass eigenfunction or Selberg counterexample is asserted. A route retaining those source constraints remains active.

## Positive survivor required before closure

If the candidate succeeds, formalize the exact power-transform identity and actual modular family, not merely a logical statement about arbitrary scalar data. The surviving lesson must identify which vector or arithmetic Maass constraint remains essential. Do not retire the full curvature route or infer a counterexample to Selberg from these scalar models.

## Audit

All seven modules are wired exactly once into RHTower. The refreshed corpus index contains the new capstones; there are 91 public declarations and 105 declarations including private helpers. The complete scratch axiom audit passed with only `propext`, `Classical.choice`, and `Quot.sound`, or none. Task whitespace checks passed. The initial repository lint failed only on nine unrelated unwired Fokas–Lenells modules; details are in `/tmp/selberg_eisenstein39_lint.log`. Those concurrent files were not edited or wired by this task.

Final targeted audits are still running. The first invocation, `LEAN_NUM_THREADS=1 lake build GaloisForLFunctions.RHTower.SelbergPositiveEisenstein`, **passed** (12320 graph jobs, mostly cached, with needed transitive rebuilds). Its tool session **34342** is terminal exit 0. Log: `/tmp/selberg_eisenstein39_positive_build.log`. The second target, `SelbergEisensteinPlane`, is now being audited; the final five named-module audits remain pending. Builds are serial, with one Lean worker observed; no full or umbrella build is used. Re-poll exact live handles after interruptions, never restart based on elapsed time. Because the final audit rebuilt dependencies, repeat the axiom audit against final artifacts after the builds finish. Its scratch/log are `/tmp/selberg_eisenstein39_axioms.lean` and `/tmp/selberg_eisenstein39_axioms.log`. Seven source hashes are saved in `/tmp/selberg_eisenstein39_source_hashes.json`.

The explicit --any Eisenstein/power-Laplacian/positive-supersolution/reciprocal-curvature/ground-state-transform search reached 1736 declarations in 106 modules. A broad continuous-partial/negative-power search reached 166 declarations in 108 modules and exposed the actual joint-smoothness bridge. An additional OR search for modular potentials, full domains, power integrals, and positive measures reached 271 declarations in 125 modules; inspected the existing literal full-domain area and source exhaustion proofs. These are discovery counts, not claims that every hit's proof was read.
