# Static ensemble coverage barrier and novelty kill (2026-08-10)

## Proved and formalized
- Paper card: `docs/drafts/pipeline/2-fully-proven/static-ensemble-coverage-time-barrier-law.md`.
- Lean module: `formal/GaloisForLFunctions/HTGeometry/StaticEnsembleCoverageTimeBarrierLaw.lean`, wired into `HTGeometry.lean`.
- `HTGeometry.staticOrbit_targetEntropy_le`: if an m-parameter coefficient-sphere static endpoint image is eps-dense in target S and N <= externalCoveringNumber(2eps,S), then N <= (1+2|t|sqrt(m)/eps)^m.
- `HTGeometry.staticOrbit_booleanReflection_coverage_time`: dense 1/4-coverage of the Boolean reflection carrier in dimension d forces 2^d <= (1+8|t|sqrt(m))^m.
- Module build passed; #print axioms only propext/Classical.choice/Quot.sound; formal lint passed; generated indexes regenerated.

## Paper theorem
Abstract bounded m-parameter L-Lipschitz family covering a target of entropy N must satisfy L >= eps/(2R)(N^(1/m)-1). Pure projective Haar balls have exact trace-radius volume r^(2D-2), yielding |t|B_A >= eps/(2R)((2eps)^(-(2D-2)/m)-1), so an O(n)-parameter local shell needs exp(Omega(2^n/n)) time for fixed-resolution global projective coverage.

## Hostile novelty result
Do NOT count this as headline novelty. Cui–Schuster–Mao–Huang–Brandao, arXiv:2510.08434, prove a stronger permanent physics no-go: every constant-local time-independent Hamiltonian ensemble is efficiently distinguishable from Haar and fails even a 2-design at all times. Our result survives only as a quantitative supporting law applying to arbitrary bounded low-parameter static families/targets, not as master-paper novelty. Projective Haar exponent remains unformalized because the external novelty headline was killed.

## Frontier consequence
Global Haar coverage/design is definitively the wrong Brown-ramp mechanism. Static source/Jacobian/coarea capacity alone supplies at most O(m log t) bits and cannot survive the exp(Theta(D)) circuit union at Brown time. Live mechanism must be one-sided directional avoidance / moving-centralizer undistortion / ballistic first arrival. Do not return to global mixing, source entropy, minimum-gap, or absolute discrepancy norms.

## External adjacent SOTA
- Zlokapa–Allen–Harrow arXiv:2607.19852 proves optimal simulation gate/query lower bounds for worst-case local bounded-degree Hamiltonians; late-time gate theorem uses time dependence and does not prove typical ordinary static-local Brown growth.
- Chia et al. arXiv:2305.12444 gives no-fast-forwarding existence/oracle results, not a quenched plain-model theorem for the ordinary fixed-shell ensemble.

Related memories: `mem:quantum_recurrence/first_entrance_gate_capacity_frontier_2026_08_10`, `mem:quantum_recurrence/centralizer_phase_bandwidth_and_tangent_rigidity_2026_08_10`.
