# FZZ-P chiral Riesz stabilization

- **ID:** FZZ-P-HC4-NG
- **Stage:** 5-failed
- **Type:** SHARP DYNAMICAL NO-GO WITH POSITIVE SURVIVOR
- **Route:** Stabilize the literal FZZ two-scale Krein generator by adding the metric Riesz
  representative of its source-native chiral grade reporter.
- **Lean:** `GaloisForLFunctions.RHTower.FZZCigarParityChiralRieszInstability`

## Failed premise

Because HC2 identifies the literal grade crossing with the unique chiral Hermitian reporter, its
source-metric Riesz representative is the most direct local interaction candidate for converting
formal Krein self-adjointness into spectral reality.

## Exact killing theorem

For every positive scale and every real coupling `gamma`, the perturbed generator remains formally
Krein-self-adjoint but has an explicit nonzero neutral eigenvector with eigenvalue

`i sqrt(Delta_0+gamma^2/E)`,

where `Delta_0>0` and `E=Q^2-PR>0`.  Hence

`not_fzzCigarParityDilatedChiralPerturbedSpectrallyReal`

holds at every real coupling.  For `gamma!=0`, the positive imaginary part is strictly larger than
that of the unperturbed source pair.  Chiral strength moves the spectrum away from, not toward, the
real axis.

## Strongest positive survivor

The positive survivor is the exact source-native Riesz interaction and its monotone instability
invariant:

`Delta_gamma=Delta_0+gamma^2/E`.

It proves coefficient-faithful dynamical meaning for HC2's reporter, preserves formal
self-adjointness, and classifies the entire real coupling line.  Paper proof and unconditional Lean
formalization are complete in `../3-formalized/fzz-p-chiral-riesz-instability.md`.

## New insight

The missing FZZ-P stability producer cannot be the local chiral Riesz interaction at any strength.
Any successor must change coefficient geometry by adding a diagonal cone component or leave this
finite local family through a nonlocal, nonlinear, independent-channel, or singular interaction.

## Status

- exact no-go and positive survivor proved on paper;
- Riesz identity, perturbation family, characteristic law, nonreal eigenpair, neutrality, and
  strict gap growth formalized in Lean;
- direct Lean, targeted build, and axiom audit passed;
- literature search found no exact collision; independent priority audit remains.

## Log

- 2026-08-28 — Chiral Riesz stabilization route retired after exact all-coupling anti-stability
  theorem; positive survivor formalized before retirement.
