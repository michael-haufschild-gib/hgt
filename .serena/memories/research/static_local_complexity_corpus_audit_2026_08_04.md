# Static-local quantum complexity audit — 2026-08-04

## Master objective
Prove the full Brown–Susskind growth–plateau–recurrence law for ordinary time-independent fixed-locality Hamiltonians, together with maximal complexity while locality remains distinguishable from Haar. No manuscript claim may exceed unconditional mathematics; manuscript must not mention formalization.

## Corpus audit
User-designated surfaces checked:
- HTGeometry: primary recurrence, Pauli, Hall, Clifford, visible-kernel and Casimir machinery.
- QuantumAlg: directly useful strict qubit two-design, product-Clifford, doubled-twirl, Pauli/DLA and Casimir infrastructure; no existing global product-twirl range or circuit anti-concentration capstone.
- HilbertMetric: later metric/observable normalization value, no current Hall closure.
- RHTower: useful quotient/orientation and device-window patterns, no local-Hamiltonian complexity theorem.
- QECLean.lean: umbrella only.
- PNTPlus.lean: irrelevant to current frontier.
Recent publication-ready Riemann/source/Stokes papers do not supply plateau/dynamics input; do not merge them into recurrence paper.

## Completed exact theorems
1. VisibleKernelRecoveryHallExpansion: visible quotient rank plus injective quadratic hidden-kernel recovery.
2. TwoReplicaCliffordTwirlHallSymmetryReduction: one-site strict Clifford commutant range span{I,F}, idempotent split, exact quarter-turn Casimir group algebra.
3. TwoReplicaGlobalCliffordHallSymmetryReduction: arbitrary finite-register product-Clifford covariance, exact Pauli-weight preservation, canonical greatest obstruction fixed by all product Cliffords, one-site Casimir-square preservation.
4. TwoReplicaGlobalSingletEdgeCasimirBridge (new):
   - explicit reassociation of global replica configurations;
   - sitewise tensor multiplication;
   - explicit Möbius coefficient extractor for global I/F words;
   - injective physical global swap embedding;
   - exact edge-extension multiplication;
   - every edge label has Pauli weight exactly 2;
   - literal global edge commutator/Casimir tensor reduction;
   - exact physical/coefficient intertwinement;
   - connected-graph physical common kernel equals global identity plus global swap.
Target source check passes cleanly. Axiom audits of all capstones report only propext, Classical.choice and Quot.sound. Module imported by HTGeometry umbrella. No final lake build yet.

## Modified/added files
- formal/GaloisForLFunctions/HTGeometry/TwoReplicaGlobalSingletEdgeCasimirBridge.lean
- formal/GaloisForLFunctions/HTGeometry.lean
- docs/drafts/pipeline/2-fully-proven/two-replica-global-physical-edge-casimir-law.md
- docs/drafts/pipeline/2-fully-proven/two-replica-singlet-pauli-hall-expansion.md
- docs/drafts/pipeline/2-fully-proven/canonical-symmetry-reduced-hall-gluing-law.md
- docs/drafts/pipeline/1-in-progress/static-local-complexity-law.md
- docs/drafts/pipeline/4-publication-ready/universal-quantum-recurrence-anatomy/hostile-review-static-local-complexity.md
- docs/drafts/pipeline/4-publication-ready/universal-quantum-recurrence-anatomy/static-local-complexity-corpus-audit-2026-08-04.md

## Exact remaining algebraic frontier
Do not call the common-kernel Casimir law Hall expansion. Next:
1. build product-Clifford reducing projection/decomposition of canonical greatest Hall obstruction;
2. identify the zero-twirl anisotropic sector and construct an injective visible quotient detector modulo occupied nonzero paired-Pauli characters;
3. instantiate quadraticHiddenKernelRecovery_of_visibleQuotient using the new literal connected edge Casimir;
4. only then claim full mixed two-replica Hall.
The fixed-orientation single-commutator mismatch/edge-defect Hall theorem is paper-proved but not yet physically formalized.

## Beyond algebraic frontier
Even full two-replica Hall does not prove Nature headline. Still missing growing-replica Hall, planar resummation/cavity contraction, circuit selector and union, static local-Hamiltonian ensemble transfer, complexity growth, plateau density, and doubly exponential low-complexity recurrence.

## Hostile verdict
Current paper must be rejected. New theorem is a rigorous necessary lemma, not a complexity-growth or black-hole result. Do not add it to old weak-coupling manuscript; that would recreate collage.