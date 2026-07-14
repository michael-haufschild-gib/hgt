# Quantum master-constraint spectral sum rule

- **ID:** quantum-master-constraint-spectral-sum-rule
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** [BRIDGE] quantum master constraints, supersymmetric factorization, and compact-operator spectral energy
- **Statement:** The bounded master constraint `C†C` is definitionally the singular-value energy operator; its greedy spectral values are the squared singular values of `C`, and its trace equals the Hilbert–Schmidt constraint energy.

## Goal

Connect the recently added quantum-constraint API to the pre-existing compact spectral and
Hilbert–Schmidt APIs.  This must discharge the compact/symmetric/positive hypothesis triple in the
greedy spectral machinery and expose a trace/singular-value sum rule, rather than reproduce any
spectral proof.

## Gates

- [x] 0 → 1  in-progress: exact definitional bridge and direct consumers identified
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem names checked, targeted Lean check green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Physics relation

The master-constraint and supersymmetric Hamiltonian factorization is

`M_C = C†C`.

For compact `C`, the nonzero eigenvalues of `M_C` are the squared singular values of `C`.  For
Hilbert–Schmidt `C`, the energy sum rule is

`Re Tr(M_C) = ‖C‖_HS² = sum_n s_n(C)²`.

Physics sources: Han–Ma, *Master Constraint Operator in Loop Quantum Gravity*
(arXiv:gr-qc/0510014), which establishes positivity and symmetry of the master operator; and
Markovich–Biamonte–Kouri, *Supersymmetric Quantum Mechanics For Atomic Electronic Systems*
(arXiv:1106.4603), which uses the partner factorization `H_1=Q†Q`, `H_2=QQ†` and the resulting
isospectral transfer.

## Corpus application

- Prove `quantumMasterConstraint C = ContinuousLinearMap.energyOp C`.
- Reuse `energyOp_compact`, `energyOp_symmetric`, `svVal_tendsto_zero`, and the existing greedy
  exhaustion with no separate symmetry or positivity premises.
- Turn orthogonality to every greedy master mode into `C x = 0` via the already-proved exact kernel
  equivalence.
- Reuse `re_opTrace_adjoint_comp_self` and `hsNormSq_eq_tsum_svVal` to obtain the master trace sum
  rule.

## Direct-application audit

This directly joins two existing HTGeometry subsystems that previously had identical definitions
but no named bridge.  It strengthens the reusable compact constraint corpus; it does not establish
compactness or Hilbert–Schmidt membership for any specific Euler/RH source operator.

## Verification boundary

Source-level formalization only.  Per user instruction, no Lean process, build, lint, numerical
experiment, or axiom audit is run during this phase.

## Log

- 2026-07-14 — exact master/energy-operator collision and downstream hypothesis discharge identified before Lean edits.
- 2026-07-14 — source-level Lean bridge added in `HTGeometry/QuantumMasterConstraintSpectrum.lean` and imported by the HTGeometry umbrella: definitional equality with `energyOp`, compact greedy-mode hypothesis discharge, constraint-kernel completeness, squared-singular-value identity, and trace/HS/spectral sum rule.  No computation or build run.
