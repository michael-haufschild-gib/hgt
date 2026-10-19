# Uniform critical cross-scale separation fails; affine classification survives

- **ID:** APT-CRITICAL-UNIFORM-GAP
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** ../1-in-progress/apt-critical-collar-resonance-2026-10-18.md
- **Statement:** No positive lower bound separates all factorial shifted-frequency pairs at fixed prime dilation thirteen.

## Goal

The rejected route would turn exact irrationality and same-layer spacing into a
uniform oscillatory gain for the critical prime operator. Its hidden premise fails
on literal factorial source frequencies, even at a fixed prime dilation.

## Gates

- [x] Exact source and proposed gain identified.
- [x] Dependency-closed paper counterexample and positive survivor proved.
- [x] Targeted leaf build and scratch axiom audit passed.
- [x] Final actual-file audit completed; repository lint failure from concurrent ownership/index changes recorded in the source card.
- [ ] Independent significance/priority gate; no contribution credited yet.

## No-go closure

- **Exact killing mechanism:** Write `λ_N=factorialShiftedFreq N`. For every positive
  integer `M`, the literal gap satisfies
  `13/(400M) ≤ λ_(13M+1)-13λ_M ≤ 13/(140M)`.
  It is positive at every scale and tends to zero. Moreover its inverse-square
  cosine correlation over `[1,∞)` tends to one, although every fixed-scale Bohr
  mean is zero. These are shifted-frequency channel statements.
- **Strongest positive survivor:** For positive `a,b,N,M` with `a≤N` and `b≤M`,
  `|aλ_N-bλ_M|<1/15` iff `a(12N+1)=b(12M+1)`. Exact equality of the frequencies
  forces `a=b` and `N=M`. Surviving dyadic harmonics also have uniform mixed
  separation from every integer frequency below their source scale, with the
  general defect estimate `|χ(k)|/12 ≤ |kλ_N-J|+k/(140N)`.
- **New insight:** The critical interaction retains the affine arithmetic clock
  `12N+1`. Nonzero Bohr frequencies do not imply scale-uniform physical decoupling.
  The positive classification identifies the near-resonant relations that a
  complete signed prime estimate must retain.
- **Paper status:** Complete proofs and the exact cubic factorization are in the
  source card. Inputs are the existing exact source cubic and collar bounds.
- **Lean status:** Implemented in
  `formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialAffineClockResonance.lean`.
  Public endpoints encode admissible positive integer ranges directly; they add no
  source or positivity premises. The leaf build passed. Seven endpoint axiom audits
  use only `propext`, `Classical.choice`, and `Quot.sound`. Final actual-file
  `lake env lean` audit passed with empty diagnostics; repository ownership lint
  is affected by concurrent work elsewhere.
- **Novelty status:** Existing cubic resonance equivalence, generic nearby-prime
  covariance, Bohr cancellation and divisor energy were explicitly audited and
  are not credited as new. This package remains a native structural candidate;
  full critical-energy control and significance beyond existing mathematics are
  not claimed.

## Next question

Retain both integer and affine incidence channels, including the dyadic mixed
alias exception, in a complete critical prime estimate. A coefficient-dependent
prime convergence theorem may be accessible through existing bounded-primitive
and Bernoulli Lipschitz results; polar admission remains separate.

## Log

- 2026-10-18 — Exact counterexample, affine classification, dyadic separation and
  admitted-band rigidity proved on paper and checked in Lean scratch/leaf builds.
  Final actual-source audit passed. Accepted significant contribution count remains 0/100.
