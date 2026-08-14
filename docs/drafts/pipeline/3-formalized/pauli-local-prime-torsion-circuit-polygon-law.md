# Pauli-local prime-torsion circuit-polygon law

- **ID:** `pauli-local-prime-torsion-circuit-polygon-law`
- **Stage:** 3 -- formalized
- **Type:** THEOREM (Lean)
- **Lean:** `RHTower/PauliLocalPrimeTorsionCircuitPolygonLaw.lean`
- **Extends:** `prime-torsion-autonomous-circuit-polygon-law.md`

## Exact unconditional law

Consider `n>0` qubits and a bounded-weight Pauli Hamiltonian with locality cutoff `q≥2`.  For every
coefficient vector in the proved dense residual full-measure maximal-projective set, every finite
normalized circuit-ray dictionary, and every prime/replica/resolution tuple satisfying the exact
polygon budget, the same fixed Hamiltonian has:

1. syndetically recurring base times whose complete `p-1` nonidentity prime slices are farther than
   `epsilon` from every target;
2. a return within arbitrary `rho>0` of the identity ray at the `p`th slice;
3. at every real time, including every hard slice and return, a product-stabilizer two-query signal
   strictly above the exact Haar benchmark `1/(2^n+1)`, whenever the explicit local-label bound
   `M 3^q < 2^n+1` holds.

The theorem concerns an ordinary time-independent bounded-weight Pauli Hamiltonian.  Hardness does
not imply Haar randomization: a fixed local operational witness remains distinguishable forever.

## Formal theorem

`pauliBounded_completeCircuitPolygon_and_permanentHaarSeparation` composes:

- generic maximal projective rank for bounded-weight Pauli Hamiltonians;
- arbitrary-ray replica-budget prime polygon construction;
- stable-open syndetic autonomous shadowing;
- conserved local-coordinate two-query lower bound;
- exact operator-normalized Haar benchmark.

No ensemble draw occurs in the conclusion: any coefficient vector in the explicitly defined
generic set satisfies the theorem.

## Frontier

This closes “ordinary local Hamiltonian,” “same autonomous cycle,” “complete circuit union,” and
“permanent distinguishability from Haar” for the late hard-polygon law.  It does not prove:

1. Brown-scale depth until the target dictionary is instantiated with the sharper heap count;
2. first-onset growth, monotonicity, a ramp from time zero, or first recurrence timing.

## Gates

- [x] ordinary fixed bounded-weight Pauli Hamiltonian
- [x] genericity proved in the corpus, not assumed from physics
- [x] complete hard prime polygon and return endpoint
- [x] arbitrary finite normalized circuit rays
- [x] permanent same-Hamiltonian operational Haar separator
- [x] exact operator-normalized Haar benchmark
- [x] no computation and no unproved declaration
- [x] RHTower umbrella import
- [ ] Brown-scale heap dictionary instantiation
- [ ] first-onset growth

## Log

- 2026-08-14 -- formalized local-Hamiltonian hard-polygon/permanent-Haar coexistence capstone.
