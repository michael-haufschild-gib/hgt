# Scalar modular curvature versus the quarter bound

- **ID:** SELBERG-SCALAR-CURVATURE-FLEXIBILITY
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Selberg conjecturing loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 39.
- **Previous goal turn:** progress: uniform original-source tails and exact compact-orbit mass proved and audited.
- **Goal:** Test whether scalar modularity, positive curvature, cusp decay, and finite amplitude mass can force a spectral quarter lower bound; preserve the full Maass goal.

## Corpus evidence and first attempt

Explicit --any congruence/finite-quotient/nodal discovery reached 1737 declarations in 362 modules; gap/Poincare/Hecke discovery reached 1660 in 275. WeightedGraphSpectralGap explicitly assumes its gap estimate. The actual SelbergMaassTraceDirection source supplies modular permutation covariance and amplitude-weighted horizontal zero means, not a finite-quotient spectral gap. SelbergMaassChordEnergy retains its actual inverse-amplitude resistance; previous nodal proofs prevent simply dropping that cost. A follow-up Hecke/expander/nonbacktracking/Cayley-graph query returned 3 declarations in one quadratic-Hecke-base module, not an operator estimate for the Maass source. These are coverage counts and selected source inspections.

## Second conjecture and proof attempt

The scalar package may admit non-Maass examples for arbitrarily small positive spectral parameters. The corpus's actual absolutely convergent Eisenstein Poincare series has proved modular generator invariance and literal first and second derivative identities. At real parameter s=2 its summands should be positive, and its identity-row terms should imply E(z)>=y². Its positive-sign hyperbolic Laplacian is 2E.

For t>0, try the literal function a=E^(-t). The chain rule predicts

y²*Delta(a)+lambda*a = t*(t+1)*E^(-t-2)*y²*|grad E|² + (lambda-2t)*a.

Thus t=lambda/4 makes curvature strictly positive for any lambda>0. E>=y² gives cusp decay of a. The modules below prove these claims for the literal series and justify the complete Stokes limit and exact total-curvature budget. This is a proved countermodel to the stated scalar shortcut, not to Selberg. The models have power-law cusp decay; stronger exponential or vector-valued Maass constraints are not supplied.

## Source-derived proof progress

1. `SelbergPositiveEisenstein`: two actual primitive identity rows prove E>=y²>0. Real projections of the original differentiated series give the original eigen-equation.
2. `SelbergEisensteinPlane`: the corpus's global Fourier uniqueness identifies the same original series with the smooth full Fourier–Bessel sum. This establishes actual Frechet derivatives and y²*Delta(E)=2E, rather than relying only on named formal jets.
3. `SelbergPowerCurvature`: complete real-power chain rule, exact positive curvature decomposition for a=E^(-lambda/4), positive model values, original S/T invariance, and uniform power-law cusp decay.
4. `SelbergEisensteinBounds`: actual derivative summands give |E_x|<=4E/y and |E_y|<=6E/y, hence y²|grad E|²<=52E². Curvature is bounded by [52(lambda/4)(lambda/4+1)+lambda/2]a. The actual vertical model derivative is bounded by (3lambda/2)y^(-lambda/2-1).

5. `SelbergEisensteinBoundary`: original S/T invariance extends to every modular matrix. Differentiation gives the reciprocal-square Jacobian; translation cancels side currents and inversion cancels the oriented unit-circle currents. The literal planar Green theorem then leaves only the actual top current.
6. `SelbergEisensteinMass`: full-domain mass and curvature are integrable. The actual Laplacian integral is zero by the proved top-current limit and domain exhaustion. Hence integral(q)=lambda*integral(a), with strictly positive finite amplitude mass.

7. `SelbergScalarCurvatureFamily`: the actual hyperbolic Laplacian and curvature are modular invariant; both full integrals transport to the standard hyperbolic cell. The curvature/mass ratio is exactly lambda for every lambda>0. `no_positive_uniform_comparison` and `no_scalar_quarter_comparison` are closed negative statements about this literal family.

All seven complete scratch proofs, seven needed source olean checks, and seven final single-module build audits passed without new module warnings. The exact source family, its modularity, integrability, positive mass, and complete Stokes budget are proved and audited in Lean.

## Dependency-closed paper argument

Write E=(1/2)sum_(c,d primitive) [y/((cy)^2+(cx+d)^2)]^2. Every summand is nonnegative; the two pairs (0,1) and (0,-1) contribute y² after the half factor. The already-proved original series/jet identities and the globally equal smooth Fourier–Bessel representative give E>0, actual smoothness, modular invariance, and y²*Delta(E)=2E.

For arbitrary lambda>0 put t=lambda/4 and a=E^(-t). The actual second chain rule gives

q=y²*Delta(a)+lambda*a=t(t+1)E^(-t-2)y²|grad E|²+(lambda/2)a>0.

The original summand derivative bounds imply y²|grad E|²<=52E², so 0<q<=C_lambda*a, where C_lambda=52t(t+1)+lambda/2. E>=y² implies a<=y^(-lambda/2). On the full closed modular domain y>=1/2, so a is bounded above by (1/2)^(-lambda/2). The corpus proves integrability of the hyperbolic density 1/y² on this actual domain. Continuous positive a and q therefore have integrable weighted densities. A rectangle in the domain has positive area, so integral(a/y²)>0.

The actual derivative rule and |E_y|<=6E/y imply |a_y|<=(3lambda/2)*a/y<=(3lambda/2)y^(-lambda/2-1). Its unit-width top integral tends to zero. Original modular invariance gives exact differentiated side and oriented arc cancellations. The actual Green formula on each truncated standard cell therefore identifies integral(Delta a) with the top current. Since Delta a=q/y²-lambda*a/y² is integrable on the full domain, actual exhaustion passes to the limit and gives integral(Delta a)=0. Thus integral(q/y²)=lambda*integral(a/y²).

Conformal covariance of the actual C² Laplacian and modular invariance of a imply modular invariance of q. The corpus's exact full-domain change of variables transfers both weighted integrals to the standard hyperbolic modular cell. Consequently the actual curvature-to-amplitude mass ratio is exactly lambda, for every positive lambda. For any proposed uniform positive constant c, selecting lambda=c/2 contradicts c*mass<=curvature; c=1/4 is a particular case. This is a closed result about the constructed scalar family, not a conditional Selberg wrapper.

## Scope and surviving direction

Only the scalar shortcut using smooth modularity, positive curvature, vanishing cusp values/current, finite positive mass, and the exact total-curvature identity is excluded. Exponential Maass cusp decay, the common component eigen-equation, permutation-equivariant source directions, amplitude-weighted component mean zero, and nodal constraints are not supplied by this family. No Maass eigenfunction or Selberg counterexample is asserted. A route retaining those source constraints remains active.

## Audited positive survivor

The positive survivor is the literal globally smooth modular Eisenstein power family, its exact pointwise curvature identity, actual source derivative bounds, full Stokes budget, and all-positive curvature/mass ratio classification. The closed negative theorem is supported by that complete construction. The full curvature route remains active with the original component, nodal, cusp, and arithmetic constraints; the next [source-current candidate](../1-in-progress/selberg-original-source-conserved-currents.md) retains the actual common eigen-equations and regulator forcing. The [failed-route record](../5-failed/selberg-scalar-quarter-comparison.md) retires only the stated scalar shortcut.

## Audit

All seven modules are wired exactly once into RHTower. The refreshed corpus index contains the new capstones; there are 91 public declarations and 105 declarations including private helpers. The complete scratch axiom audit passed with only `propext`, `Classical.choice`, and `Quot.sound`, or none. Task whitespace and research-card links passed. **Final repository lint passed**, retaining existing large-file warnings (`/tmp/selberg_eisenstein39_lint_final.log`). The earlier nine unrelated Fokas–Lenells wiring errors no longer occur; those concurrent files were not edited or wired by this task.

All seven `LEAN_NUM_THREADS=1 lake build <module>` final audits passed, serialized. PositiveEisenstein rebuilt 104 needed transitive dependencies and its target; EisensteinPlane rebuilt five needed dependencies and its target. The remaining five audits rebuilt only their own target. Existing dependency warnings were retained; no new module warnings occurred. Target compilation times were respectively 3.4s, 3.6s, 4.6s, 4.5s, 6.0s, 5.1s, and 6.7s; these exclude dependency graph/rebuild time. Logs are `/tmp/selberg_eisenstein39_{positive,plane,power,bounds,boundary,mass,family}_build.log`, summarized in `/tmp/selberg_eisenstein39_build_audit.json`. No full or umbrella build ran. Every build handle is terminal.

The post-build scratch audit again checked all 91 public declarations against final artifacts, with only standard axioms or none and no errors/warnings. Scratch: `/tmp/selberg_eisenstein39_axioms.lean`; final log: `/tmp/selberg_eisenstein39_axioms_final.log`. All seven source hashes still match `/tmp/selberg_eisenstein39_source_hashes.json`. No task commit or push occurred. Repository-wide lint status is recorded separately from the passing task proof/build audits.

The explicit --any Eisenstein/power-Laplacian/positive-supersolution/reciprocal-curvature/ground-state-transform search reached 1736 declarations in 106 modules. A broad continuous-partial/negative-power search reached 166 declarations in 108 modules and exposed the actual joint-smoothness bridge. An additional OR search for modular potentials, full domains, power integrals, and positive measures reached 271 declarations in 125 modules; inspected the existing literal full-domain area and source exhaustion proofs. These are discovery counts, not claims that every hit's proof was read.
