# Robust static-local circuit-set avoidance law

- **ID:** robust-static-local-circuit-set-avoidance-law
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Brown–Susskind static-local complexity program
- **Statement:** One fixed Hamiltonian in an explicit tube about the inverse-square chain avoids the entire operator-norm circuit set below any prescribed two-gate cutoff throughout a certified laboratory-time window.

## Result

Let `C₂,ε(W)` be infimal two-qubit-gate complexity at operator error `ε`.  For
`0 < ε ≤ 1/200`, self-adjoint `H`, and

`T ‖H-H₀‖ ≤ ε`,

fix any cutoff `s`.  At every time satisfying

`max(2048 π ε, 256 π ε (s+1)) ≤ t ≤ min(εL,T)`,

`exp(-itH)` is not within operator distance `ε` of any circuit containing at most `s` counted
two-qubit gates.  Hence the complete cutoff circuit set has no hit in this interval.  The ordinary
termwise two-local independent Gaussian ensemble has an explicit strictly positive-probability
event on which the same one-draw conclusion holds uniformly in time.

## Gates

- [x] 0 → 1  complete circuit-set target and return-free formulation
- [x] 1 → 2  dependency-closed proof from robust complexity floor
- [x] 2 → 3  Lean source check, targeted module build, axiom audit
- [ ] 3 → 4  blocked on typical fixed-draw growth, plateau, and exponential first-return scale

## Lean certificate

- Module: `GaloisForLFunctions.HTGeometry.RobustStaticLocalCircuitSetAvoidanceLaw`
- Capstones: `perturbed_inverseSquareChain_uniform_circuitSet_avoidance`, `perturbed_inverseSquareChain_no_circuitSet_return_window`
- Ensemble theorem: `measure_ordinaryTwoLocalGaussianCircuitSetAvoidanceEvent_lower`
- Verification: `lake env lean GaloisForLFunctions/HTGeometry/RobustStaticLocalCircuitSetAvoidanceLaw.lean`; targeted `lake build GaloisForLFunctions.HTGeometry.RobustStaticLocalCircuitSetAvoidanceLaw`
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`

## Hostile boundary

This closes first-return avoidance only on the certified laboratory window `t ≤ εL`.  It covers
every fixed cutoff `s` (and therefore any polynomial cutoff once instantiated), but it does not
reach a matching exponential Brown–Susskind first-return scale, high-probability typicality, or a
complexity plateau.  Those require a fixed-time static-local incidence/capacity estimate that is
not implied by norm-tube stability.

## Log

- 2026-08-21 — conjectured as the exact full-set consequence of the robust complexity floor.
- 2026-08-21 — proved pointwise, strengthened to uniform no-hit window, transferred to the ordinary termwise Gaussian ensemble, formalized, targeted-built, and axiom-audited.
