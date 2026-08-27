# Thermodynamic consecutive projective-recurrence gap law

- **ID:** thermodynamic-projective-recurrence-desert-law
- **Stage:** 4-publication-ready
- **Type:** THEOREM (Lean)
- **Source:** corpus-wide quantum-recurrence audit, 2026-08-27
- **Statement:** One countable absolutely summable static nearest-neighbour qubit Pauli field has syndetic projective operator-norm recurrence at every finite prefix and every positive resolution, while at one fixed positive resolution actual consecutive-return gaps have an explicit lower bound tending to infinity with prefix size and occur arbitrarily late.

## Goal
Close the missing thermodynamic recurrence-clock question for the same Hamiltonian family already carrying finite-prefix projective recurrence, local complexity growth, excursions, and standard UHF dynamics. The theorem must distinguish three facts without conflating them: every finite prefix returns; return density vanishes with volume; actual consecutive-return gaps cannot remain uniformly bounded with volume. Final capstone must discharge locality, compatibility, summability, maximal projective spectrum, speed control, occupation decay, closedness and recurrence bracketing without caller premises.

## Gates
- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, literature boundary recorded
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, targeted source check/build and axiom audit green
- [x] 3 → 4 publication-ready: standalone theorem and proof integrated into recurrence paper

## Literature boundary
- Kotowski--Oszmaniec, *Tight bounds on recurrence time in closed quantum systems*, arXiv:2601.10409v3 (2026), proves deterministic finite-dimensional upper bounds and random-diagonal lower saturation; it explicitly leaves tight recurrence bounds for physical local noncommuting Hamiltonians open.
- Gupta--Short, *Recurrence Time for Finite Quantum Systems*, arXiv:2604.14995 (2026), gives state-independent finite-dimensional uniform upper bounds via simultaneous Diophantine approximation, not a compatible thermodynamic local-field desert theorem.
- Campos Venuti, *The recurrence time in quantum mechanics*, arXiv:1509.04352 (2015), derives typical recurrence-time scaling under rational-independence/statistical assumptions, not deterministic prescribed-duration projective return deserts for one compatible local field.
- Infinite-volume spin-system ergodicity and hydrodynamic results concern local observables, not global operator-norm recurrence of finite prefixes.
- Audit found no primary-source theorem combining one deterministic compatible static 1D nearest-neighbour noncommuting field, syndetic recurrence for every finite prefix, and diverging actual consecutive projective operator-norm return gaps as volume grows. This is a documented search boundary, not an absolute absence claim.

## Approach
1. Prove a spectral anchoring inequality: closeness of `e^{-itH}` to any scalar unitary implies closeness within twice the radius to the reference-eigenvalue scalar.
2. Identify anchored operator-norm returns with a closed relative-phase torus target. Maximal projective independence gives its exact completed one-sided occupation: `(2 asin(r/2)/pi)^(D-1)`.
3. Use the uniform generator bound from absolute coefficient summability to thicken every narrow hit into a fixed-width interval inside a wider target.
4. Feed vanishing occupation into the completed occupation-to-hard-gap law. Since `D=2^(k+3)`, for every `W` the packing inequality holds for all sufficiently large `k`.
5. Prove projective-return set is closed.  Use same fixed syndetic recurrence bound to choose returns on both sides of each desert, then take last exit and first re-entry; these are consecutive and separated by at least desert width.
6. Combine with same-field UHF lifecycle in one unconditional capstone.

## Closed target statement
There exist `p`, `eps > 0` such that `p` is an absolutely summable static nearest-neighbour qubit Pauli field and:

- every finite prefix has maximally projective spectrum and projective operator-norm returns inside every interval of a prefix-dependent bounded length at every positive resolution;
- for every `W ≥ 0`, all sufficiently large prefixes admit, after every requested start time, a closed interval of length `W` containing no time `t` for which `e^{-itH_k}` is within `eps` of any scalar unitary;
- all sufficiently large prefixes admit, after every requested start time, two consecutive projective returns with no intervening return and separation at least explicit `W_k→∞`;
- the same prefixes converge in operator norm, uniformly on compact time windows at evolution level, to the standard bounded infinite-volume UHF dynamics already constructed for `p`.

## Proof obligations
- [x] arbitrary scalar return implies anchored return at twice radius
- [x] general finite-Hermitian completed occupation upper bound for arbitrary projective returns
- [x] uniform prefix Hamiltonian norm/speed bound from coefficient summability
- [x] occupation base is strictly between zero and one at chosen radius
- [x] exponential-in-Hilbert-dimension occupation tends to zero along qubit prefixes
- [x] eventually satisfy every fixed hard-gap packing inequality
- [x] scalar-unitary return set is closed and deserts bracketed by last exit/first re-entry
- [x] explicit divergent width lower-bounds actual consecutive-return gaps
- [x] same-field unconditional capstone

## Paper proof [PROVED HERE]
Diagonalize finite Hermitian `H`.  For every scalar `c`, one anchored spectral
coordinate satisfies `|exp(-itE_a)-c| ≤ ||exp(-itH)-cI||`; triangle inequality
therefore bounds anchored return distance by twice arbitrary scalar-return
distance.  Maximal projective spectrum identifies anchored return with a
closed product-arc target in relative-phase torus and gives completed
one-sided occupation
`beta_k=(2 asin(1/10)/pi)^(2^(k+3)-1)` at wide anchored radius `1/5`.

Norm convergence of literal prefix Hamiltonians to bounded UHF generator
gives eventual uniform speed `S=||H∞||+2`.  With narrow radius `1/20`, wide
arbitrary-scalar radius `1/10`, and mesh `delta=1/(20S)`, every narrow hit
supplies following interval of length `delta` inside anchored radius-`1/5`
target.  If every interval of length `W` contained narrow hit, disjoint-cell
packing would force completed wide occupation at least `delta/(W+delta)`.
Taking `W_k=delta/(2 beta_k)-delta` makes this lower bound `2 beta_k`,
contradicting exact occupation `beta_k`.  Since `beta_k→0`, `W_k→∞` and is
eventually nonnegative.  Hence every sufficiently large prefix has an
arbitrarily late projective-return-free interval of length `W_k`; restriction
to any prescribed width proves absence of volume-independent clock.  Existing
same-field lifecycle supplies syndetic recurrence for every finite prefix,
absolute summability, locality, complexity clauses and UHF convergence.
Scalar unitaries form compact circle and time evolution is continuous, so
projective-return set is closed.  Apply syndetic recurrence on both sides of
each desert and take last pre-desert return and first post-desert return.
Closedness gives these extrema; desert exclusion and extremality show no
return lies between them.  Their separation is at least `W_k`, turning
return-free intervals into actual diverging consecutive-return gaps.

## Formal certificate
- Module: `GaloisForLFunctions.HTGeometry.ThermodynamicProjectiveRecurrenceDesertLaw`
- Lifecycle capstone: `exists_thermodynamicRecurrenceDesertLifecycle`
- Consecutive-gap capstone: `exists_thermodynamicConsecutiveProjectiveReturnGapLaw`
- Quantitative prefix law: `infinitePathPrefix_quantitativeProjectiveRecurrenceDeserts`
- Consecutive-gap law: `ThermodynamicRecurrenceDesertLifecycle.eventually_quantitativeConsecutiveProjectiveReturnGaps`
- No-uniform-clock corollary: `ThermodynamicRecurrenceDesertLifecycle.eventually_arbitraryWidthProjectiveDeserts`
- Targeted `lake env lean` passed; targeted `lake build` passed.
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- Repository lint reached unrelated umbrella-reachability errors for three `RHTower.Sieve.MatomakiTeravainenHarman*` modules and `HTGeometry.WeightedComplexSumConcentration`; new module contains no forbidden declaration and is wired into `HTGeometry.lean`.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** pending
- **Strongest positive survivor:** pending
- **New insight:** pending
- **Status:** not applicable; conjecture proved

## Log
- 2026-08-27 — created directly in Stage 1 after corpus and primary-literature audit; conjecture frozen before Lean work.
- 2026-08-27 — proved spectral anchoring, exact occupation hard-gap conversion, uniform prefix speed, inverse-density divergent desert scale and no-uniform-clock corollary.
- 2026-08-27 — targeted source check/build and axiom audit passed; theorem integrated into standalone recurrence paper and claim/novelty ledgers.
- 2026-08-27 — strengthened deserts to actual consecutive-return gaps using closed return tube plus same fixed syndetic recurrence certificate; new unconditional capstone, targeted source/build and axiom audit passed.
