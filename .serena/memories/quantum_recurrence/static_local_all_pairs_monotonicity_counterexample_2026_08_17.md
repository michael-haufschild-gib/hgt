2026-08-17 all-pairs laboratory monotonicity is formally disproved for explicit nested static nearest-neighbour path.

Exact constants:
- L=16384, epsilon=1/1024
- s=2*pi-1e-6 < t=2*pi
- both lie in [1024*pi*epsilon, epsilon*L/2]
- C_op_epsilon(U(s)) >= 1514
- C_op_epsilon(U(t)) <= 1513
Hence strict nearby-time complexity reversal and not MonotoneOn on laboratory window.

General survivor:
- tree phase-tail obstruction against arbitrary support-certified nonlocal/non-diagonal one/two-qubit circuits, via spanning-forest cut and four diagonal entries.
- free scalar/one-qubit centering leaves residual ZZ phase /4.

Capstone:
formal/GaloisForLFunctions/HTGeometry/NestedMonotonicityCounterexample.lean
Key declarations:
- treePhase_twoGateCount_gt
- counterLateCircuit_approximates
- monotonicityCounterEarly_complexity_lower
- monotonicityCounterLate_complexity_upper
- monotonicityCounter_strict_complexity_reversal
- nestedOperatorTwoGateComplexity_not_monotoneOn_laboratoryWindow

Verification:
- targeted lower/upper/capstone Lean checks passed; capstone olean built.
- #print axioms: only propext, Classical.choice, Quot.sound.
- scripts/formal_tools.py lint has four unrelated umbrella reachability failures (two RHTower, EntirePeriodSiegel, SiegelMeroFieldDependence); no new forbidden declarations.
- Do NOT run full umbrella build; user explicitly forbids it.

Research cards:
- positive theorem: docs/drafts/pipeline/3-formalized/path-phase-tail-capacity-and-monotonicity-counterexample.md
- failed monotonicity conjecture: docs/drafts/pipeline/5-failed/nested-static-local-literal-complexity-monotonicity.md

Unified manuscript:
docs/drafts/pipeline/1-in-progress/geometry-complexity-quantum-recurrence/
Main theorem, appendix proof, claim trace, novelty audit, hostile review updated. Tectonic produced 24-page main.pdf; new result pages 7-8 and appendix 13-14 visually clean. Literature audit found random/stochastic complexity recurrence/jumps and simulation lower bounds, but no exact deterministic nearby-time backtracking theorem for one explicit static nearest-neighbour Hamiltonian; priority remains provisional, no absolute first claim.