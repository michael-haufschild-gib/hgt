# Correct theta readers have superexponential condition number

- **ID:** xi-theta-reader-superexponential-conditioning
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), [PROVED]
- **Date:** 2026-07-10
- **Module:** GaloisForLFunctions.RHTower.XiThetaReaderConditioning
- **Paper proof:** ../../2-fully-proven/new/xi-theta-reader-superexponential-conditioning.md

## Formal surface

- thetaPositiveSquareLogAtom: the actual strict positive-half square atom.
- thetaSquareL1Majorant: integrable bound with total mass exp(-pi m squared).
- thetaSquareLogAtom_le_exp_majorant: pointwise exponential domination.
- thetaPositiveSquareLogAtom_integrable: concrete L1 hypothesis discharge.
- integral_norm_thetaPositiveSquareLogAtom_le: L1 mass at most exp(-pi m squared).
- norm_fourier_thetaPositiveSquareLogAtom_le: uniform critical Fourier bound.
- thetaFiniteSample_reader_condition_number_lower: every normalized finite sampler has total
  weight at least exp(pi m squared).
- thetaPositiveSquareLogAtomL1: the concrete L1 vector.
- thetaL1_reader_condition_number_lower: every normalized continuous L1 reader has operator norm at
  least exp(pi m squared).

## Certificate

- Direct source check passed.
- Targeted module build passed through job 8601 of 8601.
- Axiom audit: propext, Classical.choice, Quot.sound only.
- Full and umbrella builds are deliberately excluded.
- No sorry, admit, axiom, opaque, or unsafe declaration.
- Generated API refreshed; formal lint passed.

## Scope

The theorem rules out uniformly stable finite critical samplers and L1-continuous readers. It does
not rule out a fixed-index composite heat/Hardy reader; XiThetaHeatReparametrization identifies its
exp(pi m squared) cost as the exact heat-boundary normalization.
