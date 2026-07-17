# Sauter in/out Bogoliubov carrier has an exact two-orbit boundary

- **ID:** `sauter-bogoliubov-gamma-orbit-boundary`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** S. P. Kim, H. K. Lee, and Y. Yoon, *Effective Action of QED in Electric Field Backgrounds*, arXiv:0807.2696, equations (59), (62), and (63)
- **Statement:** The scalar Sauter in/out four-Gamma carrier, on its incoming-frequency spectral slice, is DA exactly when its two denominator translation orbits match the half- and unit-shift numerator orbits in either order; every other orbit configuration is HT, and both elementary exponential readout phases and the Wigner--Smith logarithmic delay preserve the boundary.

## Goal

Apply the commensurable-scale Gamma normal form to an exact strong-field QED observable.  Separate
the in/out observable from temporal propagation and obtain a reusable theorem for the `2:1:1`
Gamma pattern of hypergeometric connection coefficients.

## Gates

- [x] 0 → 1 in-progress: primary-source coefficient and parameter dependence extracted
- [x] 1 → 2 fully-proven: Gauss normal form and exact orbit exceptional set proved
- [x] 2 → 3 formalized: exact module build, direct file check, and axiom audit pass
- [ ] 3 → 4 publication-ready: application note not yet written

## Source relation

For the scalar Sauter pulse `E(t)=E_0 sech^2(t/tau)`, equation (62) gives

`mu_k = phase * sqrt(omega_out/omega_in)
  * Gamma(gamma_k) Gamma(beta_k-alpha_k)
    / (Gamma(beta_k) Gamma(gamma_k-alpha_k))`.

Writing the incoming-frequency coordinate as `z=-i*tau*omega_in/2`, the nonconstant Gamma
carrier is

`C_{a,b}(z)=Gamma(2z+1)/(Gamma(z+a)Gamma(z+b))`.

The source explicitly states that the prefactor is removed in renormalization and that the
effective action is independent of the dynamical phase.  The formal theorem therefore classifies
the observable spectral carrier, not the time evolution of the quantum field.

## Exact positive statement

Gauss duplication gives

`C_{a,b}=G * [Gamma(z+1/2)/Gamma(z+a)]
                 * [Gamma(z+1)/Gamma(z+b)]`,

with `G` nonzero and DA.  Hence `C_{a,b}` is DA exactly on

`(a-1/2 in Z and b-1 in Z) or (a-1 in Z and b-1/2 in Z)`.

This is the positive residue behind the generic HT no-go: the complete exceptional set is two
explicit orbit matchings, not an undifferentiated failure statement.  Arbitrary elementary
exponential phase/readout gauges leave the same selector.  Moreover, off the exceptional set, any
finite differential circuit with arbitrary rational-function scalars that exactly realizes the
readout must already contain a genuinely HT non-scalar atom.

The logarithmic scattering delay supplies a direct positive readout.  Restoring the elementary
phase `exp(lambda*z)` adds exactly the constant `lambda` to the bare Gamma delay.  The complete
delay is therefore HT on exactly the same orbit-mismatch locus as the Sauter coefficient itself.

## Corpus value

The result is a strict mixed-scale consumer of `MeromorphicGammaNatScale` and the Gamma-orbit
superselection theorem.  It adds an exact `2:1:1` classification not previously exposed by the
single-ratio or opposite-shift modules, and is reusable for other Gauss-hypergeometric connection
coefficients with the same scale pattern.

## Lean certificate

Module: `GaloisForLFunctions.HTGeometry.SauterBogoliubovGammaBoundary`

- `sauterBogoliubovGammaCarrierMero_normalForm`
- `not_halfShift_and_oneShift_integerSeparated`
- `differentialAlgebraicOver_sauterBogoliubovGammaCarrierMero_iff_orbitMatching`
- `hypertranscendentalOver_sauterBogoliubovGammaCarrierMero_iff_orbitMismatch`
- `differentialAlgebraicOver_sauterBogoliubovReadoutMero_iff_orbitMatching`
- `hypertranscendentalOver_sauterBogoliubovReadoutMero_iff_orbitMismatch`
- `exists_hypertranscendental_atom_of_sauterBogoliubovReadoutCircuit`
- `sauterBogoliubovReadoutWignerSmithLogClockMero_eq_carrier_add_const`
- `hypertranscendentalOver_sauterBogoliubovReadoutWignerSmithLogClockMero_iff_orbitMismatch`

The audited capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## RH pressure test

This gives a sharper normalization/cancellation diagnostic: a four-Gamma physical coefficient can
be HT generically while possessing a completely explicit DA exceptional locus.  That is useful for
archimedean-factor bookkeeping in completed L-functions, but it supplies no prime source, zero-free
region, sign theorem, or RH implication.

## Log

- 2026-07-17 — exact source relation extracted; mixed-scale normal form, exceptional orbit locus,
  complementary HT theorem, and readout-gauge stability formalized and verified.
- 2026-07-17 — applied logarithmic-delay observability: exact constant phase-calibration law and
  exact HT orbit selector.  Direct file check, standard-only axiom audit, and source scan pass.
