# FZZ-P selection by covariant reporter conservation

- **ID:** FZZ-P-HC8-NG
- **Stage:** 5-failed
- **Type:** SHARP CONSERVATIVE NO-GO WITH POSITIVE SURVIVOR
- **Route:** Move the Hermitian reporter contragrediently with the stabilized source flow and use
  its conserved energy to force reflected parity-Mellin matching.
- **Lean:** `GaloisForLFunctions.RHTower.FZZCigarParityCovariantReporterConservationRigidity`

## Failed premise

HC7 excludes every fixed reporter but leaves time-dependent source compensation open.  The strongest
canonical repair is the unique moving reporter whose pullback is unit diagonal energy.  One might
hope its all-time conservation supplies the missing FZZ-P orientation law.

## Exact killing theorem

The unique compensator is `(q^2,q,0,1)` with `q=k/exp(Pt)`.  It satisfies exact conservation, but
the complete reflected reading defect is constant in time.  Hence:

- every off-critical Mellin carrier stays unmatched for all time;
- no relaxation or wall selection occurs;
- universal moving-reporter matching is exactly equivalent to RH.

Covariance transports detector information; it does not produce divisor matching.

## Strongest positive survivor

The failed route exposes:

- a unique source-native moving reporter;
- exact all-time conserved quadratic energy;
- exact all-time pointwise critical-line detection;
- complete conservation of reflected mismatch;
- an RH-equivalent covariant matching endpoint with no extra proof burden hidden.

Paper proof and unconditional Lean formalization are complete in
`../3-formalized/fzz-p-covariant-reporter-conservation-rigidity.md`.

## New insight

Moving reporters do repair finite-time cone escape, but only through inverse-flow kinematics.  Any
surviving selection mechanism must change reflected defect rather than conserve it.  Pure covariant
or Lyapunov-style conservation under this stabilized finite block is retired.

## Status

- exact no-go and positive survivor proved on paper;
- conservation, uniqueness, pointwise detection, and global RH rigidity formalized in Lean;
- direct Lean, targeted build, forbidden-token scan, diff check, and axiom audit passed;
- literature search found no exact collision; independent priority audit remains.

## Log

- 2026-08-28 — Covariant-conservation selection retired after exact defect invariance; positive
  survivor formalized before retirement.
