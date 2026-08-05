# Mass-Xi oblique co-moving phase transition

- **Stage:** 3 — formalized in Lean 4
- **Date opened:** 2026-08-05
- **Parent:** `mass-xi-comoving-exponential-flatness`
- **Target:** `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3

## Frozen conjecture C19

Let `F` be any admissible abstract spectral family.  Write an original point
as `R+iJ` and its mass image as `M+iK`.  Suppose

\[
 a\ge2,\qquad v>0,\qquad v|u|\le a-\frac12,
 \qquad \sigma>0,\qquad 1<4\sigma v.
\]

Define

\[
 \kappa_{\sigma,v}
 =\frac12\left(\sigma-\frac1{4v}\right)>0.
\]

Then

\[
 \|\Theta_F^{(a)}(\sigma+iu)\|
 \le e^{-\kappa_{\sigma,v}(a-1/2)}
       \Theta_F(\kappa_{\sigma,v}).
\]

For the oblique Xi schedule `A_v(u)=v|u|+2`, prove a matching exponential
bound for the complete literal von-Mangoldt source and for its contribution to
the fixed-minus-oblique mass high-pass.

## Exact proof plan

1. Principal-root geometry gives
   `M^2 >= R^2 + (a-1/2)^2`, hence `a-1/2+R <= 2M`.
2. Charge conservation gives `M|K|=R|J|<=R/2`.  Combine
   `v|u|<=a-1/2` and `2(a-1/2)R <= (a-1/2)^2+R^2 <= M^2` to obtain
   `4v|u||K|<=M`.
3. Thus `uK<=M/(4v)` and
   `-sigma M+uK <= -kappa_(sigma,v)((a-1/2)+R)`.
4. Sum against the positive-time weight at `kappa_(sigma,v)`.
5. Apply the existing Gamma exponential mass-gap law with
   `delta=kappa_(sigma,v)` and the exact Euler-source identity.

## Hostile phase-boundary audit

High-precision grids confirm positive theorem margin immediately above
`4 sigma v=1`, including `sigma=0.500001`, `v=0.5001`.  Below the boundary,
the balanced regime `R~a~v|u|`, `|J|~1/2` has asymptotic decay coefficient

\[
 \sqrt2\sigma-\frac1{2\sqrt2v},
\]

which is negative exactly when `4 sigma v<1`; numerical witnesses diverge.
Thus the boundary is not an artifact of the proof's constants.  Formalizing
the universal upper chamber is the present exact claim; a dependency-closed
fixed-family sharpness construction is a separate conjecture.

## Significance test

This is not another RH-equivalent zero-side restatement.  It gives an
unconditional source theorem for every positive real-time line and identifies
the first exact aperture-velocity phase diagram.  The old unit-slope cone is
one interior point.  Critical oblique slope `v=1/(4 sigma)` is the first
adaptive boundary not killed by exponential flatness and becomes the next
cofinal observable to audit.

## Status

Numerically pre-certified; paper inequalities dependency-closed; Lean proof complete.

Formal modules:

- `formal/GaloisForLFunctions/HTGeometry/AbstractSpectralObliqueComovingExponential.lean`
- `formal/GaloisForLFunctions/RHTower/XiMassObliqueComovingPrimeExponential.lean`

Universal capstone:

`HTGeometry.AbstractSpectralFamily.norm_mass_traceC_le_oblique_comoving_exponential`

Xi capstones:

- `RHTower.norm_xiMassBottomPrimeIntegral_oblique_comoving_le_exponential`
- `RHTower.norm_xiMassPrimeObliqueHighPass_sub_fixedSource_le_exponential`
- `RHTower.riemannHypothesis_iff_xiMassPrimeObliqueHighPassLineBound`

Verification on 2026-08-05:

- `lake env lean` passes on both modules;
- targeted abstract build passes `[2751/2751]`;
- targeted Xi build passes `[9396/9396]`;
- both modules are wired into their umbrellas;
- axiom audit of six geometric/source/RH capstones reports only `propext`,
  `Classical.choice`, and `Quot.sound`.

## Verdict

`PROVED`.  Every aperture ray strictly above `4 sigma v = 1` is an
exponentially blind chamber.  The exact critical boundary is now the first
unclassified adaptive scale; no open-chamber estimate can cross it by loss of
constants.
