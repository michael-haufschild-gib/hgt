# Two-clock locality law

- **ID:** `two-clock-locality-law`
- **Stage:** 3-formalized
- **Type:** UNIVERSAL NULL TEST / CONTINUUM GRAVITY / CLOCKS / HYPERTRANSCENDENCE
- **Paper proof:**
  `../2-fully-proven/new_scientific_knowledge/other/two-clock-locality-law.md`
- **Lean modules:**
  `formal/GaloisForLFunctions/HTGeometry/ClockPropagatorSelfCalibration.lean`,
  `formal/GaloisForLFunctions/HTGeometry/ClockPrincipalSymbolCalibration.lean`,
  `formal/GaloisForLFunctions/HTGeometry/ClockLocalityDistributionKernel.lean`
- **Status:** unconditional operator cancellation, exact diagonal distribution kernel, and
  differential-algebraic residual obstruction.

## Formalized theorem

For two mass-shifted operator presentations with common endpoint gains, Lean proves in an arbitrary
noncommutative algebra

\[
  Q_{\mu_1}-Q_{\mu_2}
  =
  (\mu_1-\mu_2)B^{-1}A^{-1}.
\]

The proof does not commute the geometric operator through either gain.

Lean additionally represents the geometric inverse as an actual local scalar second-order
operator. Coefficient-by-coefficient subtraction proves that its two-mass difference is exactly a
zeroth-order multiplication operator: every first- and second-order coefficient is zero.

For a finite-dimensional real coordinate space and every event \(x\), Lean constructs the honest
classical-distribution kernel fiber

\[
  (\mu_1-\mu_2)\kappa(x)\,\delta_x.
\]

It proves its action on every compactly supported smooth test, proves distributional support is
contained in \(\{x\}\), and proves equality with \(\{x\}\) for distinct masses and nonzero gains.
This is the literal no-off-diagonal/no-derivative/no-memory conclusion, not a support predicate
supplied as a hypothesis.

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
- `ScalarSecondOrderOperator.measuredClockInverseOperator_difference`
- `ScalarSecondOrderOperator.evalJet_measuredClockInverseOperator_difference`
- `twoMassClockLocalityCoefficient`
- `measuredClockInverseOperator_difference_eq_twoMassClockLocalityCoefficient`
- `twoMassClockLocalityKernel`
- `twoMassClockLocalityKernel_apply`
- `dsupport_twoMassClockLocalityKernel_subset`
- `dsupport_twoMassClockLocalityKernel_eq`

The underlying operator declarations are listed in
`two-mass-self-calibrating-clock-metric-law.md`.

## Exact boundary

This does not prove experimental access to complete inverse propagators, nor that a nonlocal/HT
residual uniquely identifies quantum gravity. Interactions, nonminimal coupling, species-dependent
gain, unresolved mixing, and inverse regularization can all violate the model premises.

## Verification

- All three Lean modules pass `lake env lean <file>`.
- `lake build GaloisForLFunctions.HTGeometry.ClockPropagatorSelfCalibration` passes with both new
  dependencies.
- Exact operator, kernel-support, and HT capstones report only `propext`, `Classical.choice`, and
  `Quot.sound` under `#print axioms`.
- Modules are directly reachable from `formal/GaloisForLFunctions/HTGeometry.lean`.
