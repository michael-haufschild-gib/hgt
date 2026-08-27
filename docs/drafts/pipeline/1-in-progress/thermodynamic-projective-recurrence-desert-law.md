# Thermodynamic projective-recurrence desert law

- **ID:** thermodynamic-projective-recurrence-desert-law
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** corpus-wide quantum-recurrence audit, 2026-08-27
- **Statement:** One countable absolutely summable static nearest-neighbour qubit Pauli field has syndetic projective operator-norm recurrence at every finite prefix and every positive resolution, while at one fixed positive resolution every prescribed duration occurs as an arbitrarily late return-free interval for every sufficiently large prefix.

## Goal
Close the missing thermodynamic recurrence-clock question for the same Hamiltonian family already carrying finite-prefix projective recurrence, local complexity growth, excursions, and standard UHF dynamics. The theorem must distinguish three facts without conflating them: every finite prefix returns; return density vanishes with volume; no volume-uniform bound on recurrence-free epoch length survives. Final capstone must discharge locality, compatibility, summability, maximal projective spectrum, speed control, and occupation decay without caller premises.

## Gates
- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, literature boundary recorded
- [ ] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: Lean theorem, targeted `lake build` green, axiom audit and lint pass
- [ ] 3 → 4 publication-ready: standalone theorem and proof integrated into recurrence paper

## Literature boundary
- Kotowski--Oszmaniec, *Tight bounds on recurrence time in closed quantum systems*, arXiv:2601.10409v3 (2026), proves deterministic finite-dimensional upper bounds and random-diagonal lower saturation; it explicitly leaves tight recurrence bounds for physical local noncommuting Hamiltonians open.
- Gupta--Short, *Recurrence Time for Finite Quantum Systems*, arXiv:2604.14995 (2026), gives state-independent finite-dimensional uniform upper bounds via simultaneous Diophantine approximation, not a compatible thermodynamic local-field desert theorem.
- Campos Venuti, *The recurrence time in quantum mechanics*, arXiv:1509.04352 (2015), derives typical recurrence-time scaling under rational-independence/statistical assumptions, not deterministic prescribed-duration projective return deserts for one compatible local field.
- Infinite-volume spin-system ergodicity and hydrodynamic results concern local observables, not global operator-norm recurrence of finite prefixes.
- Audit found no primary-source theorem combining one deterministic compatible static 1D nearest-neighbour noncommuting field, syndetic recurrence for every finite prefix, and arbitrarily long projective operator-norm return deserts as volume grows. This is a documented search boundary, not an absolute absence claim.

## Approach
1. Prove a spectral anchoring inequality: closeness of `e^{-itH}` to any scalar unitary implies closeness within twice the radius to the reference-eigenvalue scalar.
2. Identify anchored operator-norm returns with a closed relative-phase torus target. Maximal projective independence gives its exact completed one-sided occupation: `(2 asin(r/2)/pi)^(D-1)`.
3. Use the uniform generator bound from absolute coefficient summability to thicken every narrow hit into a fixed-width interval inside a wider target.
4. Feed vanishing occupation into the completed occupation-to-hard-gap law. Since `D=2^(k+3)`, for every `W` the packing inequality holds for all sufficiently large `k`.
5. Combine with existing finite-prefix syndetic recurrence and same-field UHF lifecycle in one unconditional capstone.

## Closed target statement
There exist `p`, `eps > 0` such that `p` is an absolutely summable static nearest-neighbour qubit Pauli field and:

- every finite prefix has maximally projective spectrum and projective operator-norm returns inside every interval of a prefix-dependent bounded length at every positive resolution;
- for every `W ≥ 0`, all sufficiently large prefixes admit, after every requested start time, a closed interval of length `W` containing no time `t` for which `e^{-itH_k}` is within `eps` of any scalar unitary;
- the same prefixes converge in operator norm, uniformly on compact time windows at evolution level, to the standard bounded infinite-volume UHF dynamics already constructed for `p`.

## Proof obligations
- [ ] arbitrary scalar return implies anchored return at twice radius
- [ ] general finite-Hermitian completed occupation upper bound for arbitrary projective returns
- [ ] uniform prefix Hamiltonian norm/speed bound from coefficient summability
- [ ] occupation base is strictly between zero and one at chosen radius
- [ ] exponential-in-Hilbert-dimension occupation tends to zero along qubit prefixes
- [ ] eventually satisfy every fixed hard-gap packing inequality
- [ ] same-field unconditional capstone

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** pending
- **Strongest positive survivor:** pending
- **New insight:** pending
- **Status:** active

## Log
- 2026-08-27 — created directly in Stage 1 after corpus and primary-literature audit; conjecture frozen before Lean work.
