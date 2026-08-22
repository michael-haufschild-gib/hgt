# Local-Pauli autonomous observer sublevel law

- **ID:** `local-pauli-autonomous-observer-sublevel-law`
- **Stage:** 3-formalized
- **Type:** theorem / ordinary static-local observer frontier
- **Parent:** `../1-in-progress/oriented-no-shortcut-without-return-law.md`
- **Status:** `[LEAN-PROVED] [FRONTIER ADVANCE] [NOT BROWN--SUSSKIND]`
- **Date:** 2026-08-22

## Result

Fix any qubit count `n` and locality cutoff `q`.  Reindex all nonidentity
Pauli words of weight at most `q` by a canonical finite coordinate set and
assemble the ordinary real-coefficient Hamiltonian

\[
 H(x)=\sum_{P:\,1\le |P|\le q}x_P P.
\]

The unit-time Schrödinger generator dictionary `x ↦ -iH(x)` is injective.
Finite dimensionality therefore supplies a continuous real-linear reporter
`R` with

\[
 R(-iH(x))=x.                                                \tag{1}
\]

For every nonzero real laboratory time `t`, packaged as `t : ℝˣ`, the same
construction applied to `x ↦ -itH(x)` gives a reporter `R_t` whose selected
generator minor is exactly identity:

\[
 \det\bigl[R_t(-itH(e_j))_i\bigr]_{i,j}=1.                  \tag{2}
\]

Consequently the nonlinear autonomous endpoint

\[
 F_t(x)=R_t\!\left(\exp(-itH(x))\right)                     \tag{3}
\]

has a target-independent Gaussian-null critical locus.  Every exact target
carrier restricted to the regular locus has Hausdorff dimension zero.  In
addition, for every `ε>0` there is `g>0` such that

\[
 \gamma\{x:|\det M_t(x)|\le g\}<\varepsilon,               \tag{4}
\]

where `M_t(x)` is the selected observer-Jacobian minor of `(3)` and `γ` is
standard Gaussian coefficient law.

Equation `(4)` is a fixed-confidence qualitative lower tail.  It supplies no
dimension-uniform rate and no growing-replica exponent.

## Lean certification

Modules:

- `formal/GaloisForLFunctions/HTGeometry/AnalyticObserverMinorSublevelLaw.lean`
- `formal/GaloisForLFunctions/HTGeometry/LocalPauliAutonomousObserverLaw.lean`
- `formal/GaloisForLFunctions/HTGeometry/GaussianDeterminantTubeUpperBound.lean`
- `formal/GaloisForLFunctions/HTGeometry/ObserverJacobianActiveMinorGaussianLaw.lean`
- `formal/GaloisForLFunctions/HTGeometry/ObserverJacobianFullGaussianTubeLaw.lean`

Main declarations:

- `analytic_observerMinor_zeroSet_stdGaussian_zero`
- `analytic_observerMinor_exists_small_stdGaussian_sublevel`
- `unitTimeActivePauliGenerator_injective`
- `unitTimeActivePauli_generatorMinor_eq_one`
- `unitTimeActivePauli_universal_exactCarrierLaw`
- `unitTimeActivePauli_exists_small_observerMinor_sublevel`
- `nonzeroTimeActivePauli_universal_exactCarrierLaw`
- `nonzeroTimeActivePauli_exists_small_observerMinor_sublevel`
- `observerJacobianGram_fullGaussianTube_dichotomy`

Targeted Lean checks and module builds pass.  Axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Hostile scope audit

This theorem closes three previously informal steps:

1. physical active-Pauli dictionary injectivity for all `n,q`;
2. one explicit full-rank nonlinear observer jet at every nonzero time;
3. passage from Gaussian-null criticality to a positive fixed-confidence
   determinant threshold.

It does **not** prove complexity growth, a plateau, or first recurrence.  The
reporter is selected from the full matrix endpoint and is not a shallow-circuit
preparation certificate.  Static-orbit adversarial nets show that Jacobian
anti-concentration alone cannot beat the complete circuit target.  Remaining
Brown--Susskind core is quantitative decay of the return-excised,
occupied-image, circuit-structured incidence action at growing replica order.

