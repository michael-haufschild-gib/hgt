# Static-local complexity corpus audit — 4 August 2026

## Audit scope

The audit covered the six user-designated corpus surfaces:

- `HTGeometry`
- `RHTower`
- `HilbertMetric`
- `QuantumAlg`
- `QECLean.lean`
- `PNTPlus.lean`

It also checked newly added publication-ready papers for exact mechanisms
that could advance the autonomous complexity goal.

## Results

### HTGeometry — directly useful

This remains the main proof surface. The useful chain is:

- finite spectral Haar recurrence and recurrence-frequency laws;
- canonical maximum-defect/Hall machinery;
- paired-Pauli character decomposition and first-defect selectors;
- one-site doubled-Clifford commutant and quarter-turn Casimir identities;
- arbitrary-register product-Clifford covariance;
- visible-kernel quadratic recovery;
- local identity/swap edge synchronization.

The audit exposed one concrete missing bridge: coefficient synchronization had
not been identified with literal arbitrary-register weight-two Hamiltonian
commutator squares. That bridge is now proved in
`TwoReplicaGlobalSingletEdgeCasimirBridge.lean`.

### QuantumAlg — directly useful infrastructure

The relevant modules are the strict qubit two-design, product-Clifford gate
calculus, doubled finite-group twirl, Pauli-string dynamical Lie algebra and
Casimir interface. They supplied or validated:

- exact Clifford multiplication and unitarity;
- sitewise tensor-product multiplication;
- doubled conjugation/twirl identities;
- Pauli normalization and local Casimir conventions.

They do not already prove the needed global product-twirl range, canonical
Hall-obstruction decomposition or circuit anti-concentration theorem. The
twirl interface explicitly warns that finite-group commutant membership does
not imply the required Lie-algebra invariant statement without a separate
commutant-completeness theorem.

### HilbertMetric — useful later, not for current algebraic gate

The Fano/commutator, Gaussian metric and spectral-bandwidth modules may help
with observable normalization, information bounds and device-facing metrics.
They do not provide the missing static-Hamiltonian ensemble transfer, circuit
union or mixed Hall theorem.

### RHTower — conceptual analogies and device certificates only

Useful exact patterns include source/quotient orientation warnings, canonical
complexity filtrations, coherence-filtered observability and a finite quantum
observer device-window certificate. These reinforce two rules:

- a projected quotient cannot recover orientation information that was never
  retained;
- an analytic recurrence horizon becomes a device statement only after a
  measured coherence-window inequality is supplied.

No RHTower theorem supplies local-Hamiltonian complexity growth, product-
Clifford range classification, circuit anti-concentration or Brown--Susskind
recurrence.

### QECLean.lean — no direct theorem

This is a small umbrella for stabilizer/Pauli and binary-symplectic material.
It provides compatible language but no theorem closing the present frontier.

### PNTPlus.lean — no direct use

Prime-number asymptotics and explicit PNT infrastructure do not advance the
current two-replica Hall/cavity gate. Importing them would be thematic collage.

### New publication-ready papers — no forced merger

The recent source-boundary, Riemann and Stokes papers contain useful general
warnings about lost orientation and global completion, but no theorem that
supplies static local-Hamiltonian plateau input. The two-sided singular
Gelfand-defect paper concerns infinite-dimensional noncoercive dense-range
maps and does not apply to finite-dimensional Hamiltonian matrix space, where
injective dense range is coercive. None should be imported into the recurrence
paper merely to broaden its vocabulary.

## Frontier after audit

Completed:

1. explicit physical embedding and recovery of all global identity/swap
   coefficients;
2. exact weight-two support of each edge generator;
3. global/local edge-extension multiplication;
4. literal physical/coefficient edge-Casimir intertwinement;
5. connected-graph common kernel equal to global identity plus global swap.

Still missing:

1. product-Clifford reducing projection on the canonical greatest Hall
   obstruction;
2. visible quotient detector for the anisotropic zero-character sector;
3. full mixed two-replica Hall expansion;
4. growing-replica extension;
5. planar cavity anti-concentration strong enough to survive the circuit
   union;
6. local-Hamiltonian ensemble transfer;
7. complexity growth, plateau and first low-complexity recurrence.

No paper-level claim beyond item 5 of the completed list is authorized.
