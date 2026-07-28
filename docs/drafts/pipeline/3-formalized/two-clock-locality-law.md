# Two-clock locality law

- **ID:** `two-clock-locality-law`
- **Stage:** 3-formalized
- **Type:** UNIVERSAL NULL TEST / CONTINUUM GRAVITY / CLOCKS / HYPERTRANSCENDENCE
- **Paper proof:** `../2-fully-proven/new_scientific_knowledge/two-clock-locality-law.md`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/ClockPropagatorSelfCalibration.lean`
- **Status:** unconditional operator cancellation and differential-algebraic residual obstruction.

## Formalized theorem

For two mass-shifted operator presentations with common endpoint gains, Lean proves in an arbitrary
noncommutative algebra

\[
  Q_{\mu_1}-Q_{\mu_2}
  =
  (\mu_1-\mu_2)B^{-1}A^{-1}.
\]

The proof does not commute the geometric operator through either gain.

In a differential field, Lean defines the scalar locality residual

\[
  R=(\mu_1-\mu_2)\kappa
\]

and proves:

\[
  \kappa\ \text{differentially algebraic}
  \quad\Longrightarrow\quad
  R\ \text{differentially algebraic}
  \quad\Longrightarrow\quad
  R\ \text{is not hypertranscendental}.
\]

Therefore an HT inverse residual is incompatible with the simultaneous assumptions of a pure
mass shift and DA common calibration.

## Unconditional declarations

- `twoClockLocalityResidual`
- `differentialAlgebraicOver_twoClockLocalityResidual`
- `not_hypertranscendentalOver_twoClockLocalityResidual`

The underlying operator declarations are listed in
`two-mass-self-calibrating-clock-metric-law.md`.

## Exact boundary

This does not prove experimental access to complete inverse propagators, nor that a nonlocal/HT
residual uniquely identifies quantum gravity. Interactions, nonminimal coupling, species-dependent
gain, unresolved mixing, and inverse regularization can all violate the model premises.

