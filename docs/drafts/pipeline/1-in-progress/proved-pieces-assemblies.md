# Assemblies of proved pieces

- **ID:** proved-pieces-assemblies
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-1011/obstacles-summary.md`, §2.1, “Assemblies of proved pieces”.
- **Goal:** Resolve every listed task, with exact paper arguments and kernel-checked Lean declarations; no additional mathematical premises.

## Scope and proof obligations

| Tasks | Required result | Status |
|---|---|---|
| A107 | Level-one positivity gives AAL, B56, and RH or Θ=1 | Complete: `3-formalized/level-one-positivity-abscissa-laws.md` |
| A110 | B13 iff comb-defect negative index is zero or infinite | Complete: `3-formalized/finite-stratum-packet-index-dichotomy.md` |
| A106 | AAL from length-dependent floors at `(k+1)π/67`, including prime logs | Both implications written; Lean check pending |
| A103 | Cancellation, positivity, companions, long moments, seven-way quasi-RH ladder | Exact domains assembled in `TheCancellationAndDepthLadder.lean`; check pending |
| A108 | Conductor first rung forces primes of both character signs | Full proof written; Lean check pending |
| A109 | Normalized prime-error trichotomy | Open |
| A113 | Half-plane map: bounded shapes, positivity, return-free windows | Open |
| A114 | Step-packet limit matrices with both pole moments and RH equivalence | Independent active proof: `agz-step-packet-limit-matrices.md`; preserve its work |
| A104 | Exceptional-height measure, second and growing moments | Contact-polynomial second-moment bound written; growing moments and sign transfer open |
| A105 | Density-matched rung-positive model with arbitrarily high deep zeros | Open |
| A102 | Sharp additive constant in height aperture | Open |
| A80, A94 | Finite-scale converse and index equality | Open |
| A82 | Li ladder as comb forms of tails | Open |
| A79, A81, A93 | Aperture–height constants and order of windowHeight | Open |
| A78, A89 | Cluster window theorem and prescribed sub-logarithmic radius | Open |
| A86, A47 | Near-diagonal cofactors, growing filters, one-quartet constants | Open |
| A111 | Critical-zero proportion from twisted moments and Levinson gate | Open |
| A116 | Ideal degree points, Hecke characters, non-abelian character index | Open; preserve existing independent ideal-square work |
| A119 | Linear depth-sum bound with explicit moment constant | Already proved: `RHTower.eventually_offLineMoment_le_montgomeryTaylor`, constant `66/1000` |

## Integrity

New proofs require exact stated scope, a direct `lake --old env lean` check, and umbrella
wiring. Existing proved results are reused. Mathematical counterexamples require a
positive-survivor audit.

## Exact arguments under verification

- **A107:** `RHTower.riemannHypothesis_iff_exists_jasDressedPSDAbove_one` already removes
  the edge exception. Its source checks directly; transitive axioms are only
  `propext`, `Classical.choice`, `Quot.sound`. Requested corollaries are in
  `SelectiveArithmetic/LevelOnePositivityAndTheAbscissaLaws.lean`.
- **A110:** Split each complex test into real and imaginary parts. Its Gram matrix is a
  compression of the real family, so the real packet supremum equals the full Pontryagin
  index, hence the number of distinct right zeros. This number is finite iff the off-line
  divisor is finite, and zero iff RH. Source:
  `ArithmeticCastelnuovoSeveri/TheFiniteStratumIsThePacketIndexDichotomy.lean`.
- **A106:** A finite exceptional set has a maximum and a finite nonempty active top layer.
  The finite-mode theorem contradicts a floor at its prescribed window length. For prime
  samples choose a larger fixed window and use prime-gap transfer: its error has exponent
  `max(0,b−1/3)<b`, contradicted by the normalized top-layer excursions. Source:
  `SurfaceOfSpecZ/ScaleLocality/LengthDependentFloorsGiveTheAbscissaLaw.lean`.
- **A103:** `exists_shape_positive_not_feasible` separates the bounded-shape conclusion of
  cancellation from the full positivity premise of `zeta_companion_of_rung`. The assembled
  statement must retain both domains; it cannot infer the latter sign from the former.
- **A104:** `TheContactPolynomialHasFewLargeHeights.lean` gives
  `measure{|D_a(t)| ≥ c log T} ≤ 33 T a³/(c log T)²` on `[T,2T]`, for `a ≥ 1` and
  `4 exp(4a)(2+2a)^4 ≤ T`. Markov's inequality uses the existing contact mean square.
  This controls one polynomial, not the supremum over every packet frequency.
- **A108:** The actual twisted zero form includes `placeEnergy`, bounded by `π` times the
  packet mass. A genuine split prime also requires controlling ramified primes; a departure
  from `χ(p)=-1` alone permits `χ(p)=0`. Proposed repair: use
  `exists_riesz_twist_le_of_nonneg`; ramified primes contribute at most `2a log q`
  by `vonMangoldt_sum` over conductor divisors. All proper prime powers together cost
  `O(a² exp a)` by `RHTower.sum_nonprime_vonMangoldt_div_sqrt_le`. At
  `a=log log q+η`, both are smaller than the gap between the prime main term `exp(2a)`
  and the conductor term `log q * exp a`. This comparison remains to formalize.
- **A119:** `RHTower.ZetaGateProductAFE.exists_eventually_offLineMoment_le_mul` is already
  unconditional. Its constant comes from the proved mollified gate and
  `eventually_offLineMoment_le_of_zetaGate_twoThirds`: for any positive slack `ε`,
  `(log c - 5R/3 + ε)/(4π)`, where the same `c ≥ 1` satisfies the gate at `R > 0`.
  The sharper `RHTower.eventually_offLineMoment_le_montgomeryTaylor` gives `66T/1000`
  from the proved Selberg gate of length `T^(21/50)`, `R=3/2`, and critical-zero count credit.
