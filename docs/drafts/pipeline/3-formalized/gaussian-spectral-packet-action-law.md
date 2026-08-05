# Gaussian spectral-packet action law

- **ID:** `gaussian-spectral-packet-action-law`
- **Stage:** 3-formalized
- **Status:** `[FORMALIZED] [BRIDGE]`
- **Parent paper theorem:**
  `../2-fully-proven/gaussian-radial-observer-spectral-action-law.md`
- **Lean module:**
  `HTGeometry/GaussianSpectralPacketActionLaw.lean`
- **Date:** 2026-08-05

## Exact theorem

For every finite coefficient packet `c_i`, every real detuning packet
`Delta_i`, every real time `t`, and a standard scalar Gaussian clock `X`,

\[
 \int\sum_i c_i e^{itX\Delta_i}\,d\gamma(X)
 =\sum_i c_i\exp\!\left[-{(t\Delta_i)^2\over2}\right].
\]

As `t -> +infinity`, the integral converges exactly to

\[
 \sum_{\Delta_i=0}c_i.
\]

This is the finite spectral-packet layer of the observer--spectral action
law: every character depends only on the dimensionless action `t Delta_i`,
and exactly the zero-action sector survives completion.

## Formal theorem surface

- `gaussianObserverActionKernel_eq_charFun`
- `integral_gaussian_observer_character`
- `tendsto_gaussianObserverActionKernel_atTop_zero`
- `integral_gaussianSpectralPacket`
- `tendsto_integral_gaussianSpectralPacket_atTop`

## Scope boundary

This module proves the scalar-Gaussian finite-packet identity and limit.  It
does not yet formalize Gaussian polar disintegration, angular mixing, the
weak endpoint-law mixture, circuit-easy indicators, or the selector-uniform
complexity estimate.  In particular it is not a formalization of Conjecture
A in the parent observer--spectral shortcut card.

## Verification

- Targeted foreground check:
  `lake env lean GaloisForLFunctions/HTGeometry/GaussianSpectralPacketActionLaw.lean`
  passed.
- `scripts/formal_tools.py lint` passed.
- Axiom audit of both load-bearing packet declarations reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
