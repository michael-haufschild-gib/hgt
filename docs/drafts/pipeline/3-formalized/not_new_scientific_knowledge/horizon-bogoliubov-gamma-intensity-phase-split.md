# Horizon Bogoliubov Gamma intensity--phase observability split

- **ID:** `horizon-bogoliubov-gamma-intensity-phase-split`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** `[PROVEN]` exact Carlitz--Willey Gamma intensity--phase--delay differential split; `[BRIDGE]` opposite-orientation product, reflection quotient, Wigner--Smith/digamma clock, and finite-circuit non-recovery
- **Sources:** M. R. R. Good, P. R. Anderson, and C. R. Evans, *Time Dependence of Particle Creation from Accelerating Mirrors*, arXiv:1303.6756, Table IV; G. Gianfelici and S. Mancini, *Quantum channels from reflections on moving mirrors*, arXiv:1704.04635, equations (18) and (27)
- **Statement:** In the dimensionless complex-frequency coordinate `z=iω/κ`, the Gamma core of a thermal moving-mirror Bogoliubov coefficient is `Gamma(z)`.  Its conjugate-frequency intensity core `Gamma(z)Gamma(-z)` is DA, but its oriented phase quotient `Gamma(z)/Gamma(-z)` is HT.

## Goal

Formalize the exact loss of differential information caused by passing from a complex horizon
amplitude to an intensity-only readout, including the logarithmic Wigner--Smith delay obtained by
differentiating the amplitude.  This is a theorem about which parts of the frequency clock are
observable; it does not claim that mirror motion or cosmological time evolution is HT.

## Gates

- [x] 0 → 1 in-progress: primary-source coefficient and existing Gamma APIs identified
- [x] 1 → 2 fully-proven: exact product/quotient relations and DA/HT split
- [x] 2 → 3 formalized: direct Lean check and axiom audit
- [ ] 3 → 4 publication-ready: standalone exposition not written

## Exact physics value

The Carlitz--Willey family has a Bogoliubov coefficient whose non-elementary core is
`Gamma(iω/κ)`.  Its squared magnitude gives a Planck factor.  The quantum-channel formulation
also records `arg Gamma(iω/κ)` explicitly in the channel phase.  The remaining powers and
exponentials are nonzero DA gauges in the complex-frequency clock.

## Exact theorem surface

Let

- `A(z)=Gamma(z)`,
- `I(z)=Gamma(z)Gamma(-z)`,
- `P(z)=Gamma(z)/Gamma(-z)`,
- `Q(z)=A'(z)/A(z)=digamma(z)`.

The Lean certificate proves unconditionally:

1. `I` is exactly the zero-shift opposite-orientation Gamma product.
2. Euler reflection rewrites `I` as a sine gauge times the adjacent Gamma ratio, so `I` is DA.
3. `P` is the inverse zero-center Gamma reflection clock, so `P` is HT.
4. No DA multiplicative phase calibration turns `Gamma(-z)` into `Gamma(z)`.
5. No scalar-aware finite differential circuit with intensity-core atoms reconstructs `P`.
6. The Wigner--Smith/logarithmic clock of `A` is exactly `Q`, and `Q` is HT.
7. No scalar-aware finite differential circuit with intensity-core atoms reconstructs `Q`.

The fifth and seventh items are the nontrivial positive statements: intensity-only observation is
not merely noninjective at one value.  Even after adjoining arbitrary rational clocks and closing
under any finite sequence of field operations and differentiations, it can recover neither the
oriented phase nor the logarithmic delay.  Any realization of either observable needs an HT source
outside the intensity sector.

## Existing-corpus value

The module closes three previously separate APIs:

- the exact DA boundary for opposite-orientation Gamma products;
- unconditional HT for reflected Gamma quotients;
- unconditional HT for Gamma logarithmic derivatives/Wigner--Smith clocks;
- HT-source extraction from scalar-aware finite differential circuits.

It also supplies a reusable warning for every thermal, scattering, black-hole, and cosmological
consumer: an exact modulus-square or conjugate-frequency product can erase the oriented HT datum
even when the complex amplitude retains it.

## RH pressure test

This is potentially useful for auditing spectral or thermal RH proposals: positivity or modulus
squares of archimedean Gamma amplitudes may be DA even when the oriented amplitude is HT.  Hence an
intensity-only construction cannot be assumed to preserve the Gamma orientation data needed by
the HT corpus.  This supplies a route discriminator, not a zero-location source.

For `RHTower`, this means a proposed positive thermal or spectral measure derived only from a
Gamma modulus square does not inherit the archimedean orientation or logarithmic-delay information
automatically.  A route that needs either datum must expose a phase-sensitive source or prove an
independent recovery theorem; the finite differential recovery class is now ruled out.

## Lean certificate

- `formal/GaloisForLFunctions/HTGeometry/HorizonBogoliubovGammaObservability.lean`
- The exact module `:olean` target completed successfully with all dependencies cached.
- The direct single-file Lean check completed successfully.
- The capstone axiom audits, including the three Wigner--Smith additions, report only `propext`,
  `Classical.choice`, and `Quot.sound`.
- The Lean source contains no active `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` token.

## Log

- 2026-07-17 -- literature value and disjoint corpus interfaces isolated; formalization started.
- 2026-07-17 -- DA intensity, HT phase, DA-calibration obstruction, and finite-circuit
  non-recovery formalized and narrowly verified; promoted to stage 3.
- 2026-07-17 -- identified the Wigner--Smith clock exactly with the digamma source; proved its HT
  and finite-differential non-recoverability from the DA horizon intensity; narrowly verified.
