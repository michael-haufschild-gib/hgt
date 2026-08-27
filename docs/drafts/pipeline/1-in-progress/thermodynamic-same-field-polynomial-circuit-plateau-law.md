# Thermodynamic same-field polynomial-circuit plateau law

- **ID:** thermodynamic-same-field-polynomial-circuit-plateau-law
- **Stage:** 1-in-progress
- **Type:** CONJECTURE → THEOREM (Lean target)
- **Source:** corpus-wide recurrence/complexity audit, 2026-08-27
- **Statement:** One countable absolutely summable static nearest-neighbour qubit Pauli field simultaneously has the existing ramp--recurrence-gap--UHF lifecycle and, along all paired finite prefixes, vanishing upper completed-time occupation of every fixed-finite-alphabet polynomial-depth Choi circuit dictionary at one fixed physical resolution.

## Literature boundary

- Oszmaniec--Kotowski--Horodecki--Hunter-Jones prove complexity saturation and recurrence for random local circuits and stochastic local Hamiltonian evolution, not one deterministic time-independent compatible nearest-neighbour field.
- Kotowski--Oszmaniec prove finite-dimensional recurrence-time bounds and random-Hamiltonian saturation; their August 2026 version leaves tight physical local noncommuting recurrence bounds open.
- Dumas--Fischler prove quantitative filling times for torus flows under (possibly truncated) Diophantine conditions; this does not provide one local quantum field, circuit-target occupation, or same-prefix thermodynamic dynamics.
- Corpus has per-size Gaussian same-draw polynomial-circuit plateau and one compatible field with near-Hilbert hard excursions, recurrence deserts/gaps and UHF convergence.  It has no theorem putting completed-time polynomial-circuit occupation extinction on that one compatible field.
- Search found no primary-source theorem with this exact deterministic static-local same-field conjunction.  This is bounded absence evidence, not absolute priority proof.

## Frozen conjecture C1

There exists one coefficient field `p` satisfying `ThermodynamicRecurrenceDesertLifecycle p` such that for every alphabet size `g`, polynomial exponent `r`, and every family of padded target Choi vectors on paired prefixes:

1. each prefix phase orbit has upper completed-time target occupation bounded by its Haar target volume;
2. Haar volume is bounded by `polynomialCircuitChoiEntropyCost g r (L+2)` at pair index `L` and fixed radius `sqrt 2 / 100`;
3. this explicit envelope tends to zero as `L→∞`.

No Hamiltonian is reselected for alphabet, exponent, target family, or system size.

## Attack

1. Define canonical paired-prefix configuration equivalence and relabel selected-prefix eigenvalues into dimension `4^(L+2)`.
2. Transport maximal projectivity of every literal prefix through equivalence.
3. Project arbitrary target pure-state densities to diagonal spectral coordinates.
4. Apply existing completed-time projective Choi plateau theorem at every prefix.
5. Compose existing entropy-cost limit with `L↦L+2`.
6. Package all alphabet sizes, exponents and target families under one existential same-field capstone.

## Proof obligations

- [ ] paired-prefix Hilbert dimension identity
- [ ] paired-prefix eigenvalue maximal projectivity
- [ ] exact per-prefix completed-time occupation/Haar bound
- [ ] thermodynamic entropy envelope tends to zero
- [ ] one-field unconditional capstone
- [ ] targeted source check, module build, axiom audit, umbrella wiring
- [ ] paper integration and literature-bounded positioning

## No-go closure

- **Status:** open
