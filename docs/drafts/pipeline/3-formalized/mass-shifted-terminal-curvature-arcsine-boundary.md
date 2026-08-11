# Mass-shifted terminal-curvature arcsine boundary

- **Route:** `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3 exact open core
- **Status:** formalized in Lean 4
- **Opened:** 2026-08-11
- **Formalized:** 2026-08-11

## Hard target

For every fixed positive degree `n`, prove the source-native terminal Riccati defect has exact
far-right boundary value

\[
 \lim_{y\to\infty}y^2\mathcal D_n^{\rm term}(y)={4n+3\over4}>0,
 \qquad
 \lim_{y\to\infty}{y^2\mathcal D_n^{\rm term}(y)\over4n+3}={1\over4}.
\]

Consequently `I_n'(y)<0` on a complete far-right subray.  This is a boundary-curvature theorem,
not a fixed reporter or orientation map.

## Conjecture loop

1. **C1 — recession only controls admission trace.** Failed: exact dilation transfers first two
   admission jets, hence scaled Jacobi diagonal and edge coefficients.
2. **C2 — terminal defect may have sign-indefinite arcsine boundary.** Failed on paper: shifted
   Chebyshev recurrence has `alpha=1/2`, `beta_1=1/8`, `beta_k=1/16` for `k>=2`, giving exact
   defect `(4n+3)/4`.
3. **C3 — fixed-degree positivity closes RH.** Failed: convergence thresholds may escape with
   degree.  Positive survivor is universal normalized boundary value `1/4`; remaining core is
   uniform/cofinal control of convergence to this value.

## Paper dependency plan

- coefficientwise normalized admission recession;
- exact actual/normalized admission gauge identity;
- shifted-Chebyshev Jacobi constants;
- exact terminal-defect formula;
- finite limit algebra and positivity transfer.

## Theatre audit

Passing condition: formal theorem must yield a new sign for actual odd-current derivative on a
terminal subray and expose exact degree normalization.  Merely restating coefficient convergence
or adding a reporter fails.

**Passed.**  Lean proves both the exact curvature limit and eventual strict negativity of actual
raw odd-current derivative.  Admission selects amplitude first; completed arithmetic source is
formed through adaptive bilinear shear before any reflection aggregation.

## New exact source law

For normalized and actual Jacobi data, Lean proves

\[
 \widetilde\alpha_n(w)=w^2\alpha_n(w^2),\qquad
 \widetilde\beta_n(w)=w^4\beta_n(w^2),
\]

and therefore

\[
 \widetilde{\mathcal D}_n^{\rm term}(w)
   =w^4\mathcal D_n^{\rm term}(w^2).
\]

Shifted-Chebyshev recurrence has `alpha=1/2`, `beta_1=1/8`, and `beta_n=1/16` for `n>=2`.
Consequently, for every `n>0`,

\[
 y^2\mathcal D_n^{\rm term}(y)\longrightarrow {4n+3\over4},\qquad
 {y^2\mathcal D_n^{\rm term}(y)\over4n+3}\longrightarrow {1\over4}.
\]

Actual terminal defect is eventually positive and actual odd-current derivative is eventually
strictly negative.

## Lean artifact

- `formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionTerminalCurvatureRecession.lean`
- umbrella: `formal/GaloisForLFunctions/RHTower.lean`

Principal capstones:

- `dimensionlessTerminalJacobiRiccatiDefect_eq_fourth_mul_actual`
- `tendsto_dimensionlessTerminalJacobiRiccatiDefect`
- `tendsto_degreeNormalized_xiShiftedCanonicalAdmissionTerminalCurvature`
- `tendsto_square_mul_xiShiftedCanonicalAdmissionTerminalJacobiRiccatiDefect`
- `xiShiftedCanonicalAdmissionTerminalJacobiRiccatiDefect_eventually_pos`
- `deriv_xiShiftedCanonicalAdmissionOddCurrent_eventually_neg`

## Stronger principle exposed by formalization

Terminal defect is homogeneous weight-four curvature of mass/degree admission connection.
Extensive factor is exactly `4n+3`; curvature per effective degree has universal far boundary
`1/4`.  Fixed-degree sign obstruction is closed.

## Remaining open core

This does not prove RH.  Separate terminal threshold for each fixed degree has no cofinal force.
Need either:

1. convergence to `1/4` uniform along actual first-contact degree schedule; or
2. adjacent-degree curvature budget preventing terminal thresholds from escaping.

## Verification

- direct `lake env lean`: passed without warnings;
- targeted module build: passed (`11787/11787`);
- six capstone axiom audits: only `propext`, `Classical.choice`, and `Quot.sound`;
- forbidden-declaration scan: clean;
- `git diff --check`: passed;
- formal lint: new module is umbrella-reachable and clean; repository lint remains red only on
  unrelated pre-existing/concurrent umbrella-reachability gaps in Deninger, Sieve, Suzuki,
  source-horizontal, Xi-resolvent, and HTGeometry modules.
