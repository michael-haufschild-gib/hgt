# Finite-clock orbit asymmetry

- **ID:** finite-clock-orbit-asymmetry
- **Stage:** 3-formalized
- **Type:** PROVED IN LEAN / GENERAL HTGEOMETRY BRIDGE
- **Source:** group twirling and quantum-reference-frame asymmetry
- **Statement:** For an arbitrary finite-period isometric clock, total squared commutator energy over the complete clock orbit is exactly `2N` times star-Kadison observability loss.

## Goal

Extend the corpus's exact two-outcome commutator law to clocks of arbitrary finite period and to
non-self-adjoint observed operators.  The orbit labels available clock perspectives; it is not a
temporal trajectory.

## Gates

- [x] 0 → 1 in-progress: the arbitrary-period gap between commutator values and clock variance was isolated
- [x] 1 → 2 fully-proven: orbit-overlap, orbit-deviation, and commutator Parseval identities proved
- [x] 2 → 3 formalized: scratch certification, exact-module cache build, direct source check, and axiom audit pass
- [ ] 3 → 4 publication-ready: supply analytic estimates on orbit commutators for a concrete hypertranscendental clock

## Physics source

- A.-C. de la Hamette, S. L. Ludescher, and M. P. Mueller, *Entanglement-asymmetry correspondence for internal quantum reference frames*, arXiv:2112.00046, identifies exact asymmetry measures of conditional states with information supplied by an internal quantum reference frame, including imperfect clocks.
- A. K. Hashagen, S. T. Flammia, D. Gross, and J. J. Wallman, *Real Randomized Benchmarking*, arXiv:1801.06121, states that finite-group twirling is the normalized group sum and the Hilbert--Schmidt orthogonal projection onto the commutant.

The exact vector-norm coefficient below is the formalized cyclic-clock transfer; it is not claimed
as a verbatim theorem of either paper.

## Exact relation

Let `U` be an isometry of nonzero period `N`, let `P_U` be its cyclic average, and let `x` be any
vector.  The complete orbit satisfies

```text
sum_{k<N} ||U^k x - x||² = 2 N ||(1-P_U)x||².             (1)
```

Now let `psi` be stationary, `U psi = psi`, and let `X` be an arbitrary bounded operator.  Since

```text
(U^k X-X U^k)psi = U^k(X psi)-X psi,
```

equation `(1)` and the star-Kadison erased-information law give

```text
sum_{k<N} ||(U^k X-X U^k)psi||²
  = 2 N Re <psi,D*_U(X)psi>.                              (2)
```

Thus the static observability loss is exactly the mean squared symmetry-breaking seen across all
clock readings.  No Hamiltonian, derivative in time, or temporal evolution appears.

## Formalization

`formal/GaloisForLFunctions/HTGeometry/FiniteClockOrbitAsymmetry.lean` proves:

- expectation equals retained projection norm for self-adjoint idempotents;
- powers of an isometry preserve squared norm;
- `sum_re_inner_finiteClockOrbit_eq`;
- `sum_finiteClockOrbitDeviation_sq_eq`;
- `sum_finiteClockCommutator_sq_eq_starObservability`.

## Corpus value

The theorem converts arbitrary-period clock observability into a finite sum of commutator values,
generalizing the existing involutive coefficient law and removing self-adjointness of `X`.  Any
future analytic estimate on the orbit commutators now transports without loss of constants to a
star-Kadison energy estimate, while vanishing recovers the existing physicality criterion.

## Status

[PROVED IN LEAN] The exact-module cache build and touched-file check pass.  The three principal
exports depend only on Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.  No
full project build, numerical experiment, or concurrent Lean process was run.
