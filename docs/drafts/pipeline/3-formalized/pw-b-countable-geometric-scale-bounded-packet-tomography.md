# PW-B bounded-packet countable endpoint tomography

## Status

Formalized in Lean 4 on 2026-08-28. Frontier label: HC32.

## Route

Parikh–Wilczek/backreaction (PW-B).

## Problem

Finite endpoint sampling separates finite winding packets, and one explicit infinite dark packet is visible, but neither result excludes a different infinite packet from lying in every physical endpoint kernel. Prove coefficient-faithful tomography for a genuine infinite packet class using only the fixed Schwarzschild energy sequence

\[
  \epsilon_j=\frac1{4(j+1)},\qquad
  q_j=\exp\!\left(-\frac1{4\epsilon_j}\right)=e^{-(j+1)}.
\]

## Result

Let `c : ℕ → ℝ` be uniformly bounded. Then all countably many physical endpoint responses vanish iff every winding coefficient vanishes:

\[
  \left(\forall j,\;\sum_{n\ge0}c_n q_j^{n+1}=0\right)
  \Longleftrightarrow
  \left(\forall n,\;c_n=0\right).
\]

Lean also proves the reusable coefficient-peeling theorem: a bounded real power series whose values vanish on any sequence of positive nodes inside the unit disk converging to zero has every coefficient zero.

## Proof idea

Strong induction peels coefficients at the accumulation point. After the first `m` coefficients vanish, divide the sampled identity by `q_j^m`. The remaining tail is bounded by

\[
  C\frac{q_j}{1-q_j},
\]

which tends to zero. Hence the leading surviving coefficient must be zero. The physical identity `q_j=e^{-(j+1)}` and `q_j→0` then specialize this uniqueness theorem to the Parikh–Wilczek endpoint reporter.

## Lean artifact

- Module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekBoundedPacketCountableTomography`
- File: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekBoundedPacketCountableTomography.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Main endpoint: `schwarzschildParikhWilczekBoundedPacketEndpointResponse_eq_zero_iff`
- Reusable theorem: `boundedPowerSeries_coeff_eq_zero_of_zeroSequence`

## Verification

- `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekBoundedPacketCountableTomography.lean`: passed.
- `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekBoundedPacketCountableTomography`: passed (11,616 jobs).
- `#print axioms` on four public endpoints: only `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/formal_tools.py lint`: no finding in this module; reported only pre-existing unreachable modules elsewhere.

## Corpus audit

Mandatory searches included power-series coefficient uniqueness, vanishing on sequences tending to zero, geometric nodes, and coefficient peeling. Closest reusable corpus results were:

- `GaloisForLFunctions.HTGeometry.coeff_eq_zero_of_tsum_eq_zero`, requiring a neighborhood of zeros;
- `GaloisForLFunctions.HTGeometry.eq_zero_of_tsum_pow_eq_zero`, using an interval and `ℓ¹` coefficients;
- `summable_of_bounded_coeff` and `abs_tsum_shift_tail_le`, which supply convergence and the sharp geometric tail estimate.

No corpus theorem handled merely countably many accumulating zeros for bounded coefficients, and no existing PW-B theorem specialized this principle to the physical scale sequence.

## Literature audit

Primary-source searches covered Parikh–Wilczek tunneling, generalized/dynamical tunneling, black-hole emission tomography, and reconstruction from backreaction scales. The generic analytic fact is classical (identity-theorem territory), so no novelty is claimed for that mathematics in isolation. No source found a coefficient-faithful reconstruction theorem for bounded winding packets from the countable Schwarzschild Parikh–Wilczek endpoint sequence.

## Significance and remaining burden

HC32 closes scalar infinite-packet injectivity for every bounded winding profile, strictly extending finite Vandermonde tomography and the separation of one explicit infinite dark kernel. It does not yet couple the faithful endpoint basis to the oriented recoil factor carrying the critical-wall sign. Next burden: prove a source-derived endpoint-dressed recoil dichotomy whose only global kernel is the critical wall or the zero packet.
