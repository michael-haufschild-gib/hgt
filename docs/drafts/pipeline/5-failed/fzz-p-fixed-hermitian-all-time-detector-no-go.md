# FZZ-P fixed Hermitian all-time detector

- **ID:** FZZ-P-HC7-NG
- **Stage:** 5-failed
- **Type:** SHARP UNIFORM DYNAMICAL NO-GO WITH POSITIVE SURVIVOR
- **Route:** Choose one fixed Hermitian quadratic reporter whose pullback under the HC5 stabilized
  flow remains a reciprocal-radius detector for every nonnegative time.
- **Lean:** `GaloisForLFunctions.RHTower.FZZCigarParityFixedReporterUniformConeEscape`

## Failed premise

HC6 showed unit diagonal energy has a finite detector horizon.  A natural repair is to choose a
different fixed Hermitian reporter, or modify its first-coordinate energy, so its entire orbit stays
inside HC3's detector cone.

## Exact killing theorem

At every positive source scale there is one positive time

`U_beta=log(2(Q/R)/(Q/R-1))/P`

such that every initially separating fixed Hermitian reporter is nonseparating after pullback to
`U_beta`.  This time is uniform over all four reporter coefficients.  Arbitrary real changes to the
first-coordinate coefficient at that time do not help.

The obstruction is forced by literal Fermi monotonicity `Q/R>1`, not by a selected Mellin mode or
divisor.

## Strongest positive survivor

The failed route exposes:

- exact affine coefficient-space action of the stabilized semigroup;
- a source-native uniform escape multiplier and positive escape time;
- the necessary cone-survival inequality `alpha(e-1)<=e+1`;
- a simultaneous no-go for every fixed Hermitian reporter;
- complete invariance of the result under first-coordinate counterterms.

Paper proof and unconditional Lean formalization are complete in
`../3-formalized/fzz-p-fixed-reporter-uniform-cone-escape.md`.

## New insight

Fixed quadratic reporter optimization cannot cure late-time cone loss.  Remaining FZZ-P dynamics
must alter off-diagonal/chiral coefficients with time, reset or compose the reporter, or introduce
nonlinear, singular, or nonlocal mode-sensitive data.  Static reporter search under this stabilized
finite block is retired.

## Status

- exact no-go and positive survivor proved on paper;
- all coefficient, source-ratio, time, and uniform-escape claims formalized in Lean;
- direct Lean, targeted build, forbidden-token scan, diff check, and axiom audit passed;
- literature search found no exact collision; independent priority audit remains.

## Log

- 2026-08-28 — Fixed all-time Hermitian detector route retired after uniform source-time escape;
  positive survivor formalized before retirement.
