# Static local continuous-circuit exponential plateau law

- **ID:** static-local-continuous-circuit-exponential-plateau
- **Stage:** 3-formalized; publication manuscript integrated
- **Type:** THEOREM
- **Source:** corpus frontier audit, 2026-08-28
- **Statement:** One time-independent nearest-neighbour qubit Hamiltonian has the proved laboratory ramp and arbitrarily late fixed-error intervals of exponentially growing width throughout which every arbitrary continuous two-qubit circuit below a near-Hilbert gate budget fails, followed by recurrent re-entry.

## Goal

Upgrade the existing same-draw theorem from unspecified positive-width continuous-circuit hard
episodes to an explicit width at least `2^(L/2)` while retaining one static one-dimensional
nearest-neighbour Hamiltonian, arbitrary `SU(4)` two-qubit gates, fixed operator-norm error,
laboratory-time growth, and recurrence/re-entry. This is the deterministic static-local analogue
not supplied by random-circuit or stochastic-Hamiltonian saturation theorems.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, targeted `lake env lean`, targeted `lake build`, axiom audit
- [x] 3 → 4 publication-ready: standalone theorem, proof, claim trace, literature comparison

## Internal frontier

- `NearestNeighborNearHilbertContinuousCircuitSameDrawLaw.lean` proves one static
  nearest-neighbour draw with a laboratory ramp and syndetic continuous-circuit hard intervals at
  error `1/10`, gate budget `2^(2L)/(64(2L+1))`; interval width is only existential.
- `NearestNeighborNearHilbertContinuousCircuitFirstReturnLaw.lean` adds consecutive re-entry, but
  retains existential width.
- `NearestNeighborPolynomialCircuitQuantitativeFirstReturnLaw.lean` proves explicit
  double-exponential hard blocks, but only for a finite gate alphabet. It kills any novelty claim
  that does not retain the full continuous `SU(4)` gate model.
- `AutonomousWordComplexityConeLaw.lean` proves the abstract backward-cone transfer, but no local
  simulation theorem discharges its increment premise for the same Hamiltonian.

## External frontier audit

- Oszmaniec--Kotowski--Horodecki--Hunter-Jones, *Saturation and recurrence of quantum complexity
  in random local quantum dynamics*, arXiv:2205.09734: random circuits and stochastic local
  Hamiltonian evolution, not one deterministic time-independent Hamiltonian.
- Haah--Hastings--Kothari--Low, *Quantum algorithm for simulating real time evolution of lattice
  Hamiltonians*, arXiv:1801.03922: near-linear local-Hamiltonian simulation and worst-case lower
  bounds, not recurrence-hard plateaux for one autonomous orbit.
- Childs--Su, *Nearly optimal lattice simulation by product formulas*, arXiv:1901.00564:
  simulation upper bounds, not a complexity plateau/recurrence law.
- Brown--Susskind, *Second law of quantum complexity*, arXiv:1701.01107: conjectural
  growth--plateau--recurrence picture rather than this deterministic theorem.

No primary-source result found that combines: one deterministic static 1D nearest-neighbour
Hamiltonian; arbitrary continuous two-qubit gates; fixed operator error; explicit exponentially
wide hard intervals; and recurrent circuit re-entry.

## Conjecture loop

### C0 — finite-alphabet exponential plateau

**Status:** killed as new target. Corpus already proves a stronger double-exponential-width result
for every finite alphabet in `NearestNeighborPolynomialCircuitQuantitativeFirstReturnLaw.lean`.

**Positive survivor:** retain arbitrary continuous two-qubit gates. This is a genuine stronger
metric target and cannot be reduced to the finite-alphabet theorem at fixed error without paying
an uncontrolled net-resolution cost under arbitrarily long words.

### C1 — continuous-circuit exponential plateau

**Conjecture.** Eventually in `L`, one selected `p` from the existing same-draw event satisfies all
existing ramp and non-Haar clauses and, for every `A0 ≥ 0`, admits `u ≥ A0` such that every
`t ∈ [u, u + 2^(L/2)]` is projectively separated by at least `1/40` from every continuous
two-qubit circuit of gate count at most half the near-Hilbert budget. The interval can be bracketed
by later/earlier fixed-error circuit visits using the existing first-re-entry theorem.

**Attack.**

1. Expand the selected path Hamiltonian exactly as scalar identity plus its weight-at-most-two
   Pauli coordinates. Bound each coordinate by the operator norm and use the existing
   `‖H‖ ≤ L+2` event bound; active label count is at most `18(2L)^2`.
2. Prove a quantitative first-order product formula for a finite self-adjoint family. At fixed
   error `1/40`, `r` repetitions approximate every increment `|τ| ≤ 2^(L/2)` with polynomial in
   `L` times `2^L` local Pauli rotations.
3. Compile every weight-one/two Pauli rotation into one literal `SU(4)` two-qubit gate and compile
   products/repetitions with exact gate count. Scalar identity evolution is absorbed by the allowed
   global phase.
4. Show the compiler cost is eventually at most half
   `nearHilbertContinuousCircuitBudget (2L)`, since the latter is order `4^L/L`.
5. Apply the projective autonomous backward-cone argument to one hard endpoint from the existing
   syndetic near-Hilbert hard-interval law. Shift the endpoint search by the target width to obtain
   arbitrarily late full intervals.

## Hostile audit

- Locality alone does not imply hard endpoints; maximal projective spectral action supplies them.
- Hard endpoints alone do not imply wide plateaux; a quantitative same-Hamiltonian increment
  compiler is essential.
- Operator-speed continuity gives only inverse-polynomial width and is insufficient.
- The finite-alphabet double-exponential theorem cannot certify arbitrary continuous gates.
- Global scalar Pauli coordinate must be carried as a projective phase; dropping it would change
  the physical evolution.
- First-order product error must be quantitative, not merely the existing qualitative
  Lie--Trotter limit.
- Gate construction must land in literal local `SU(4)`, not an unconstrained two-site matrix.
- Exponential width claim requires a uniform polynomial coefficient/count bound for the selected
  same draw, not a size-dependent unnamed constant.

## Closed core

`[PROVED HERE]` Quantitative projective local Trotter compiler: every self-adjoint Pauli
weight-two `n`-qubit Hamiltonian with bounded operator norm admits a literal continuous
two-qubit circuit and unit scalar approximating its time evolution, with explicit gate/error
bound polynomial in `n`, `‖H‖`, and `t²/ε`.  Combined with maximal-projective hard endpoints,
the autonomous backward cone yields full pointwise hard intervals of width `2^(L/2)` for one
static nearest-neighbour path Hamiltonian, followed by recurrent circuit re-entry.

Formal capstone:
`RHTower.eventually_exists_nearestNeighborPath_exponentialContinuousCircuitPlateau_capstone`.
Targeted dependency and capstone builds pass.  Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Log

- 2026-08-28 — created in 1-in-progress after corpus-wide search and primary-literature audit.
- 2026-08-28 — C0 killed by existing finite-alphabet quantitative first-return theorem; C1 retained.
- 2026-08-28 — C1 proved, formalized, axiom-audited, literature-positioned, and integrated into the unified recurrence manuscript.
