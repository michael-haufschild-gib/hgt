# Unconditional cofinal simple centers for every finite completed carrier

- **ID:** unconditional-finite-carrier-simple-centers
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For every `N ≥ 1`, there are `A,L > 0` such that every interval `[T,T+L]`
  with `T ≥ A` contains `τ` satisfying `completedGN N (linePt τ) = 0` and
  `deriv (completedGN N) (linePt τ) ≠ 0`.  Moreover there are `R > 0` and an analytic
  function `h`, nonvanishing on `ball (linePt τ) R`, such that
  `completedGN N z = (z - linePt τ) * h z` throughout that ball.  In particular these
  factorized simple centers are cofinal.
- **Lean:** `formal/GaloisForLFunctions/RHTower/CarrierTransverseZero.lean`,
  `formal/GaloisForLFunctions/RHTower/CarrierPhaseCrossing.lean`, and
  `formal/GaloisForLFunctions/RHTower/CarrierZeroUnconditional.lean`; capstone
  `RHTower.completedGN_factorized_simple_zero_syndetic` and its cofinal corollary
  `RHTower.completedGN_factorized_simple_zero_cofinal`.

## Goal

Remove the conditional carrier-center block from the Route-B pinned-window program.  Neither a
carrier zero, its simplicity, a derivative floor, a caustic small-ball estimate, a prime packet,
nor a local factorization is assumed.

## Gates

- [x] 0 → 1 in-progress: the conditional center hypotheses and their consumers were traced.
- [x] 1 → 2 fully-proven: the proof below has no open dependency.
- [x] 2 → 3 formalized: focused builds, the RHTower umbrella build, the formal lint gate, and
  the generated-index check pass; the capstone has only `propext`, `Classical.choice`, and
  `Quot.sound`.
- [ ] 3 → 4 publication-ready: extract a standalone note and connect target-local window
  placement to the remaining EM/circle data.

## Proof

1. For a finite Dirichlet polynomial `D(t)`, the exact second-moment lower bound is
   `U * Σ|aₙ|² - B ≤ ∫‖D‖²`, where `B` is the finite off-diagonal budget.  If
   `t₀² < Σ|aₙ|²` and `‖D(t)‖ ≤ t₀` on an interval, choosing
   `U = (|B|+1)/(Σ|aₙ|²-t₀²)` contradicts the pointwise integral upper bound.  Hence
   every interval of that fixed length contains `‖D(t)‖ > t₀`
   (`dpoly_floor_syndetic_of_diagonal`).
2. For the critical-line Dirichlet polynomial, the `n=1` coefficient alone gives diagonal mass
   at least `1`; taking `t₀=1/2` gives an unconditional cofinal floor
   (`dirichletPoly_half_floor_cofinal`).
3. The line derivative is bounded globally by
   `B_N = Σ_{n≤N} n^{-1/2} log n`.  A radius
   `r = 1/(8(B_N+1))` therefore spreads each center floor `>1/2` to the interval floor `≥1/4`.
   Above an unconditional height threshold, archimedean winding minus `B_N/(1/4)` advances by
   at least `π` across that interval.  Polar transport forces a zero of the real completed
   carrier there.
4. At such a zero the same strict phase dominance gives a nonzero derivative.  Analytic order is
   therefore exactly one; global peeling and continuity provide the positive-radius zero-free
   analytic cofactor.

## Dual gate

- **NOVEL:** corpus search contained only conditional simple-center/factorization producers and
  the caustic route to cofinal floors.  The diagonal-second-moment route removes all of those
  center assumptions and all caustic inputs.
- **SIGNIFICANT:** a full premise block of the pinned-window program is now an unconditional
  bounded-gap theorem at every finite carrier depth.  The remaining RH obstruction is not existence,
  simplicity, or peeling of carrier centers; it is target-local alignment with an arbitrary
  off-line `xi` zero together with the EM/circle certificate on the same window.

## Log

- 2026-07-10 — transversality, phase crossing, unconditional cofinal floor, cofinal simple zeros,
  and local peeling formalized; all verification gates green.
