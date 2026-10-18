# Compensating signed arithmetic repair with the complete source fixed

- **ID:** CHMD-SIGNED-REWEIGHTING-NOGO-2026-10-18
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** CHMD signed source-rigidity research, 2026-10-18.
- **Statement:** No nontrivial signed reweighting of the arithmetic coefficients preserves both complete Euler–Poisson parity readouts in the convergent arithmetic class.

## Goal

Test whether signed compensating changes to prime weights can repair the reflected-prime energy obstruction while leaving the theta, Gamma, and polar source identities fixed. Existing coefficientwise-order rigidity does not exclude that possibility.

## Exact killing theorem

`RHTower.CHMDArithmeticTheta.signed_parity_source_rigidity` proves that any real weights `w`, supported on integers at least two, with convergent symmetric source at each nonnegative integer sample, equal `vonMangoldtAtom` whenever both parity readouts agree with the original readouts on an unbounded sample set.

The closed theorem `RHTower.CHMDArithmeticTheta.unique_signed_parity_source` also discharges existence and convergence for the actual arithmetic weights. Neither theorem assumes RH or any coefficientwise comparison.

## Strongest positive survivor

Exact signed coefficient recovery, with the explicit squared-index exponential separation bound, and a complete lexicographic order law for late integer source samples. The first nonzero coefficient of a perturbation fixes its eventual sampled sign; arbitrary unbounded sets of integer samples are uniqueness sets. These conclusions apply to every signed sequence whose arithmetic source is absolutely convergent at zero.

The full dependency-closed proof is recorded in [the source-rigidity theorem card](../3-formalized/chmd-signed-euler-poisson-rigidity-2026-10-18.md).

## New insight

The two parity identities jointly leave no signed freedom in the arithmetic weights. Their difference isolates the forward source, whose separated theta scales expose every coefficient despite cancellations. This identifies precisely why a source-preserving reweighting cannot pay the reflected-prime collar. It also supplies a recovery invariant, rather than merely restating the negative conclusion.

This does not retire CHMD. Positivity of the original primitive energy, and the resolvent bound at `1/2`, remain open. Neither parity identity alone is claimed to determine the weights.

## Status

- Paper proof: dependency-closed.
- Lean: four targeted modules and all four actual source-file checks passed.
- Scoped axiom audit: passed with exit 0; all 61 new declarations use only standard axioms. All four compiled artifacts are fresh.
- Global formal lint: three unrelated repository findings are recorded on the linked theorem card.
- External novelty audit: intentionally omitted under the task instructions.

## Log

- 2026-10-18 — Signed compensation conjecture disproved. Positive recovery and order classification formalized; targeted builds, actual-file checks, and complete scoped axiom audit passed.
