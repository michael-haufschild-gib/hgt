# Pauli XOR incidence hypercontractivity and fixed-locality kurtosis

- **ID:** pauli-xor-incidence-hypercontractivity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** static-local-complexity-law O4 robust-shortcut branch
- **Statement:** Every real `q`-local Pauli Hamiltonian has normalized spectral kurtosis at most `(9^q)^4`, uniformly in qubit count, and Choi infidelity at most `1 / (16 (9^q)^4)` forces every commuting-target shortcut into the half-energy commutator tube.

## Goal

Close the dimension-independent robustness premise left open by the Choi-shortcut energy-defect
law without importing a minimum spectral gap, eigenvector universality, asymptotics, or numerical
computation. This does not prove Brown growth: it localizes all robust shortcut events to the exact
low-defect sector where selector-aware Bellman escape remains necessary.

## Gates

- [x] 0 → 1 in-progress: exact coefficient-space target and counterexample audit
- [x] 1 → 2 fully-proven: elementary XOR-incidence tensorization and Pauli trace bridge
- [x] 2 → 3 formalized: Lean module, module-only build, axiom audit, and formal lint pass
- [ ] 3 → 4 publication-ready: intentionally not claimed; paper work paused

## Approach

For `corr(f,g,u) = sum_x f(x) g(x+u)`, explicit triple reindexing proves

`sum_u corr(f,g,u)^2 = sum_v corr(f,f,v) corr(g,g,v)`.

Two Cauchy--Schwarz steps give a four-linear Hölder law. Tensorization over qubit coordinates then
reduces the full fourth incidence to a one-qubit quartic. Its expansion has no term containing
exactly one nonidentity label; a quartic absorption inequality closes induction uniformly in the
number of qubits.

For the matrix bridge, squaring a real Pauli Hamiltonian gives a phase-twisted XOR convolution.
Pauli orthogonality is kept exactly, while unit-modulus phases are removed only after output labels
have been grouped. Thus

`tr(H^4) <= 2^n fourthIncidence(abs c)`

and `tr(H^2) = 2^n sum_s c_s^2`. Combining these identities yields normalized spectral kurtosis
`<= (9^q)^4`.

## Hostile boundary and novelty status

- Quantitative constant is deliberately nonsharp. Standard quantum hypercontractivity gives a
  stronger `9^q` fourth-moment factor; this card does not claim external novelty for the numerical
  bound.
- New value for the active programme is unconditional elementary closure of the exact coefficient
  and matrix bridge in the current Lean corpus, with a constant independent of qubit count.
- It does not bound the probability that a Hamiltonian-dependent adaptive circuit selector remains
  inside the low-defect tube. No Brown ramp, plateau, or recurrence theorem follows from this card
  alone.
- Correct next target remains quenched selector-aware Bellman escape inside the tube after explicit
  return and fast-forwardable-carrier removal.

## Lean certificate

- Module: `formal/GaloisForLFunctions/HTGeometry/PauliXorIncidenceHypercontractivityLaw.lean`
- Headline theorems:
  - `cube_fourth_hypercontractive`
  - `pauliHamiltonian_eigenKurtosis`
  - `pauliHamiltonian_choiShortcut_commutatorEnergy_le_traceEnergy`
- `lake env lean GaloisForLFunctions/HTGeometry/PauliXorIncidenceHypercontractivityLaw.lean`: pass
- `lake build GaloisForLFunctions.HTGeometry.PauliXorIncidenceHypercontractivityLaw`: pass
- `scripts/formal_tools.py lint`: pass
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only

## Log

- 2026-08-11 — Orthogonality-only conjecture falsified: unrestricted convolution support produces
  dimension dependence.
- 2026-08-11 — Sharp imported hypercontractivity route deferred: formalizing its noncommutative
  Hanner machinery would not move the selector-aware frontier.
- 2026-08-11 — Phase-free XOR incidence conjecture proved, tensorized, connected to exact Pauli
  matrix traces, and formalized. Robust fixed-locality Choi-to-tube bridge closed.
