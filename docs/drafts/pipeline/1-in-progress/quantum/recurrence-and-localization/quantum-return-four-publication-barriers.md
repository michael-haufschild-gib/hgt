# Quantum-return publication barriers

Date: 2026-07-28  
Status: three formal upgrades complete; moderate-information law remains a
separate research core

## Question

Can four residual weaknesses of “A universal information law for quantum
return” be removed unconditionally?

1. no transfer to a local-Hamiltonian ensemble;
2. no device feasibility study;
3. Hilbert–Schmidt rather than operator-norm probe normalization;
4. weak sharpness when target information is only `O(r)`.

## Current classification

### A. Local-Hamiltonian transfer

An exact transfer is possible for an engineered 1-local ensemble: independent
on-site fields restricted to the vacuum/single-excitation sector realize an
arbitrary finite phase packet, hence independent uniform fields realize Haar
projective phases exactly. This does not establish Haar behavior for generic
interacting local Hamiltonians. Constant-local time-independent Hamiltonian
evolution is known not to form a unitary 2-design, so a blanket
Haar-unitary transfer would be false; phase-marginal transfer is a weaker
question and must be proved for each ensemble.

Formal core completed:

- realize arbitrary phase packets as a diagonal local qubit Hamiltonian on
  the single-excitation sector;
- state exact equality between the field-parameter target and the existing
  phase target;
- do not claim transfer to generic interacting local Hamiltonians.

Module:
`formal/GaloisForLFunctions/RHTower/LocalSpinPhaseEnsembleTransfer.lean`.

### B. Device feasibility

Not a purely mathematical obstruction. Karimi et al. give a superconducting
central-qubit experiment with `N ≈ 5`, a single-excitation sector, tunable
energies/couplings and microsecond observation windows, including a
decohering bath model. A device-specific conclusion still requires measured
tick time, coherent window, leakage, calibration error and shot noise.

Formal theorem completed:

```text
certified horizon × tick duration ≤ coherent observation window
and calibrated probe margin > measurement uncertainty
```

This is an analytic feasibility certificate, not evidence that any named
device satisfies it.

Module:
`formal/GaloisForLFunctions/RHTower/FiniteQuantumObserverDeviceFeasibility.lean`.

### C. Operator-norm probes

A dimension-free conversion from Hilbert–Schmidt displacement to every
operator-norm-one probe is false. Schatten duality gives

```text
|Tr(σ A)| ≤ ‖σ‖op ‖A‖₁ ≤ √d ‖σ‖op ‖A‖HS,
```

and the `√d` loss is optimal in general. The correct upgrade is therefore an
operator-normalized theorem with explicit `√d` (or rank/sparsity) cost, plus
the statement that density-matrix probes already obey the existing
Hilbert–Schmidt normalization.

Formal core completed:

- define operator contraction by its action on finite vectors;
- prove its Hilbert–Schmidt energy is at most `d`;
- transfer the observer recurrence bound with factor `d` in squared form;
- add calibration-error version with factor `√d`.

Module:
`formal/GaloisForLFunctions/RHTower/FiniteQuantumObserverOperationalRecurrence.lean`.

### D. Moderate-information sharpness

The support-linear discrepancy is not only a proof artifact. At
`H = O(r)`, the exact phase target is governed by nonquadratic circular
large deviations. For equal weights its exponential rate is the Legendre
transform of the log moment-generating function of a uniform unit phasor
(equivalently a modified-Bessel expression), not the Gaussian quadratic
water functional.

Two legitimate upgrades have different scope:

1. full-active high-fidelity geometry: replace the inner product box by an
   ellipsoid and expose the exact Euclidean-ball volume correction;
2. moderate-fidelity many-mode geometry: introduce and prove the exact
   phasor large-deviation rate, then show Gaussian water entropy is its
   high-fidelity limit.

The first is finite and tractable. The second is a new probability theorem
and is the only route that genuinely fixes `H = O(r)` sharpness.

Current decision: do not disguise this gap with Gaussian finite-blocklength
dispersion or a smaller box constant. A genuinely sharp moderate-information
upgrade requires the second route and substantial new large-deviation
infrastructure absent from the current proof corpus.

## Literature boundary

- Karimi, Wu, Cleland and Pekola, arXiv:2508.13489v2 (2025).
- Cui, Schuster, Mao, Huang and Brandão, arXiv:2510.08434 (2025).
- Kostina and Verdú, IEEE TIT 58, 3309–3338 (2012): finite-blocklength
  source-coding dispersion does not transfer to phase-target geometry.

## Acceptance rule

No manuscript upgrade is accepted until its mathematical claim has a
dependency-closed Lean theorem and an axiom audit. Empirical device facts may
only be attributed to primary experimental or hardware sources.
