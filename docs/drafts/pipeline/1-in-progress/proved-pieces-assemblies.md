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
| A106 | AAL from length-dependent floors at `(k+1)π/67`, including prime logs | Complete: `3-formalized/length-dependent-floors-abscissa-law.md` |
| A103 | Cancellation, positivity, companions, long moments, seven-way quasi-RH ladder | Complete: `3-formalized/cancellation-and-depth-ladder.md` |
| A108 | Conductor first rung forces primes of both character signs | Complete: `3-formalized/first-conductor-rung-prime-signs.md` |
| A109 | Normalized prime-error trichotomy | Complete corrected classification: `3-formalized/normalized-prime-error-top-trace.md`; empty, finite and infinite boundary spectrum, without an isolation gap |
| A113 | Half-plane map: bounded shapes, positivity, return-free windows | Complete: `3-formalized/half-plane-three-rungs.md` |
| A114 | Step-packet limit matrices with both pole moments and RH equivalence | Already formalized: `3-formalized/agz-step-packet-limit-matrices.md` |
| A104 | Exceptional-height measure, second and growing moments | Complete: `3-formalized/exceptional-contact-heights.md`; sharp exponent `1−1/(2κ)+ε`, including uniform bounded-shape transfer |
| A105 | Density-matched rung-positive model with arbitrarily high deep zeros | Full-test version impossible: unbounded positive apertures force all zeros onto the line. Exact obstruction and fixed-aperture density-matched survivor formalized in `3-formalized/density-matched-positive-windows.md`; bounded-shape restriction is a separate conjecture |
| A102 | Sharp additive constant in height aperture | Upper bound improved to `log(π/2)` and formalized in `3-formalized/absolute-cosine-height-aperture.md`; sharpness remains open |
| A80 | Finite-scale converse | Already formalized: `riemannHypothesis_iff_eventually_combForm_ge`; `3-formalized/agz-step-packet-limit-matrices.md` |
| A94 | Finite-scale index equality | Complete: `3-formalized/unshifted-comb-index-at-nonresonant-ratios.md`; raw index lies between restricted rank and rank plus nullity, hence equals rank at nonresonant apertures |
| A82 | Li ladder as comb forms of tails | Complete: `3-formalized/li-ladder-as-damped-comb-tails.md`; explicit damped, smoothly truncated Laguerre tails with divergent horizons and sampling scales |
| A79, A81, A93 | Aperture–height constants and order of windowHeight | Complete: `3-formalized/window-height-triple-exponential-order.md`; `log log log(windowHeight(a))−C a^(4/3)→log 138`, explicit `C` |
| A78 | Cluster window theorem | Already proved: `SurfaceOfSpecZ.ScaleLocality.finite_top_negative_in_every_window`; no frequency separation, length greater than `card(S)π/Γ` |
| A89 | Prescribed sub-logarithmic radius | Existing `3-formalized/double-logarithmic-windows-miss-the-minimal-face.md` covers every prescribed `R(T)≤(C/256)log log T` with one configuration; general `R(T)=o(log T)` remains open |
| A86 | Near-diagonal cofactors and growing filters | Complete: `3-formalized/growing-cofactor-filters-and-near-diagonal-pairs.md`; row bound `1+4W/(t sqrt(r))`, actual filtered transfer to `W≤3t^71`, error `≤2h^d exp(−at/8)` |
| A47 | One-quartet constants | Complete: `3-formalized/one-quartet-current-constant.md`; explicit normalized-current lower bound |
| A111 | Critical-zero proportion from twisted moments and Levinson gate | Actual three-moment remainder, shifted arithmetic jets, chi-taper jet limits and exact scalar `c(13/50)<18/5<exp(13/10)` proved. Uniform block assembly and gate insertion remain open |
| A116 | Ideal degree points, Hecke characters, non-abelian character index | Hecke explicit formula, ideal-degree pairing, Dedekind and class-character indices proved in `3-formalized/agz-hecke-explicit-formula-and-ideal-squares.md`; per-Artin-character analytic input remains open |
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
- **A104:** `TheContactPolynomialHasFewLargeHeights.lean` proves the stronger bound
  `measure{|D_a(t)| ≥ c log T} ≤ (13+2 log 4) T a²/(c log T)²` on `[T,2T]`, for `a ≥ 1` and
  `4 exp(4a)(2+2a)^4 ≤ T`. Mertens bounds the contact variance quadratically in `a`.
  This controls one polynomial, not the supremum over every packet frequency.
- **A113:** The bounded-shape rung uses the centred contacts `Λ(n)−1`, whose partial sum
  is `ψ(n)−n+1`. A half-plane `Θ≤b` gives every exponent above `b`, hence every rung
  `(2b−1)κ<1`. The same half-plane gives large-prime dressed positivity above `b+1/2`
  and the heavy-return lower bound `log t≥c y^(1−b)`.
- **A108:** The actual twisted zero form includes `placeEnergy`, bounded by `π` times the
  packet mass. A genuine split prime also requires controlling ramified primes; a departure
  from `χ(p)=-1` alone permits `χ(p)=0`. The proof uses
  `exists_riesz_twist_le_of_nonneg`; ramified primes contribute at most `2a log q`
  by `vonMangoldt_sum` over conductor divisors. All proper prime powers together cost
  `O(a² exp a)` by `RHTower.sum_nonprime_vonMangoldt_div_sqrt_le`. At
  `a=log log q+η`, both are smaller than the gap between the prime main term `exp(2a)`
  and the conductor term `log q * exp a`. The comparison is formalized in `TheFirstConductorRungForcesBothPrimeSigns.lean`.
- **A119:** `RHTower.ZetaGateProductAFE.exists_eventually_offLineMoment_le_mul` is already
  unconditional. Its constant comes from the proved mollified gate and
  `eventually_offLineMoment_le_of_zetaGate_twoThirds`: for any positive slack `ε`,
  `(log c - 5R/3 + ε)/(4π)`, where the same `c ≥ 1` satisfies the gate at `R > 0`.
  The sharper `RHTower.eventually_offLineMoment_le_montgomeryTaylor` gives `66T/1000`
  from the proved Selberg gate of length `T^(21/50)`, `R=3/2`, and critical-zero count credit.
