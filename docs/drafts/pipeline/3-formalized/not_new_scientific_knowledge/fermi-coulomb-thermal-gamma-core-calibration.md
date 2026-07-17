# The beta-decay Fermi Gamma core is a calibrated thermal KMS clock

- **ID:** `fermi-coulomb-thermal-gamma-core-calibration`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** R. J. Hill, R. Plestid, *Field Theory of the Fermi Function*, arXiv:2309.07343, equations (1), (4), and (5); J. C. A. Barata, L. F. Canto, M. S. Hussein, *The Coulomb Phase Shift Revisited*, arXiv:0912.3189, equation (1)
- **Statement:** The Gamma--Boltzmann core of the relativistic beta-decay Fermi function is exactly the thermal-CFT KMS Gamma response under `kappa=2*pi*xi`; charge reversal produces `exp(-2*pi*xi)`, and at partial-wave weights its product with the Coulomb scattering phase reconstructs the squared positive-orientation Gamma amplitude.

## Goal

Connect weak-decay, electromagnetic scattering, and thermal/holographic response values through an
exact shared Gamma clock.  The relation should identify complementary observable channels rather
than introduce another temporal flow.

## Gates

- [x] 0 → 1 in-progress: exact Fermi-function primary formula and existing thermal/Coulomb values matched
- [x] 1 → 2 fully-proven: clock calibration, charge reversal, and magnitude--phase reconstruction
- [x] 2 → 3 formalized: exact module build, direct check, and standard-only axiom audit pass
- [ ] 3 → 4 publication-ready: not a standalone novelty claim

## Exact value relations

Write the Gamma-dependent Fermi core as

`F_core(eta,xi) = exp(pi*xi) Gamma(eta+i*xi) Gamma(eta-i*xi)`.

Then

`F_core(eta,xi) = thermalCFTKMSResponseValue(eta, 2*pi*xi)`

and therefore

`F_core(eta,-xi) = exp(-2*pi*xi) F_core(eta,xi)`.

At `eta=ell+1`, the Coulomb partial-wave phase is the quotient of the same two Gamma legs.  Hence

`F_core(ell+1,xi) * CoulombPhase(ell,xi)`

equals

`exp(pi*xi) Gamma(ell+1+i*xi)^2`.

The magnitude-type weak-decay observable and the phase-type scattering observable are thus
complementary: together they recover one oriented Gamma amplitude up to a square.

## Scope

The source's full Fermi function also contains a fixed Gamma denominator and kinematic/nuclear-size
factors.  The Lean object is explicitly only the Gamma--Boltzmann core.  No claim is made about
nuclear corrections or the complete decay rate.

## Lean certificate

Module: `GaloisForLFunctions.HTGeometry.FermiCoulombGammaCore`

- `fermiCoulombGammaCoreValue_eq_thermalCFTKMSResponseValue`
- `fermiCoulombGammaCoreValue_neg`
- `fermiCoulombGammaCoreValue_mul_coulombPhaseValue`

All three declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Corpus and RH value

The theorem connects two previously separate consumers of the Gamma reflection API and gives a
concrete magnitude--phase reconstruction law.  It strengthens the observability interpretation of
HT clocks but adds no prime carrier, zero-free statement, or `RHTower` hypothesis discharge.

## Log

- 2026-07-17 — weak-decay/thermal clock calibration, charge-orientation balance, and
  Fermi-core/Coulomb-phase reconstruction formalized and verified.
