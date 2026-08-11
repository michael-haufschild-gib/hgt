# Mass-shifted terminal-curvature arcsine boundary

- **Route:** `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3 exact open core
- **Status:** in progress
- **Opened:** 2026-08-11

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
