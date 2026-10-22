# Riemann–von Mangoldt zero counting, and the five-twelfths proportion

- **ID:** `riemann-von-mangoldt-zero-counting`
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) — formalization of two classical/modern analytic-number-theory inputs
- **Statement:** With `N(T)` the number of `ξ`-zeros of ordinate in `[0, T]` counted with
  multiplicity,

  ```text
  N(T) = (T/2π) log(T/2π) − T/2π + O(log T),
  ```

  and with `N₀(T)` the same count restricted to the critical line,

  ```text
  liminf_{T→∞} N₀(T)/N(T) > 5/12.
  ```

## Goal

`suzuki-critical-radical-anchor-finite-head-reduction` needs exactly these two as the *only*
remaining input to its fifth gate, the five-twelfths multiplicative-annulus coverage.  That card's
own handoff is explicit:

```text
The annular corollary additionally needs formal providers for Riemann–von Mangoldt and the
published >5/12 theorem; no hypothesis wrapper or axiom should be introduced in their place.
```

The consuming deduction is short.  With `α = √3`, `β = 12√3/5` and any `κ ∈ (5/12, liminf)`,

```text
N₀(βT) − N₀(αT) ≥ κ N(βT) − N(αT) = [(κβ − α)/(2π) + o(1)] T log T,
κβ − α = √3(12κ/5 − 1) > 0,
```

so every sufficiently large `T` has a positive-ordinate critical-line zero with ordinate in
`[αT, βT]`; Schwarz symmetry supplies the conjugate copy, and the pair has squared ordinate in
`[3T², (432/25)T²]`, which is the annular window `(SR-64.22)` of the consuming card.

## What already exists

**In the corpus**

```text
RHTower/XiZeroCountingFunction.lean   the counting functions themselves:
  xiRegionOrderSum, xiCountingBox, xiCriticalCountingBox
  isCompact_xiCountingBox, isCompact_xiCriticalCountingBox
  xiZeroCount, xiCriticalZeroCount, and their nonnegativity
  xiRegionOrderSum_congr                regions with the same zeros have the same mass
  exists_xi_zero_im_mem_Ioc_of_lt       a strict increase produces a zero in the band
  exists_xi_criticalLine_zero_im_mem_Ioc_of_lt   the same on the critical line
  exists_conj_pair_of_xi_zero           Schwarz symmetry gives the distinct conjugate copy

RHTower/WindingFull.lean               windingNumber_argument_principle
RHTower/WindingXiCircle.lean           xi_zeros_closedBall_finite, windingNumber_xi_circle
RHTower/ModulusSlopeField.lean         the ξ-divisor mass of a ball, and Jensen two-radius slope
RHTower/RiemannTower.lean              xi, xi_analyticOnNhd, xi_zeros_finite_in_ball
RHTower/Reflection.lean                xi_conj
PNTPlus/ZetaBounds.lean                zero-free region, LogDerivZetaBnd, ZetaNoZerosInBox
```

**In mathlib** — `completedRiemannZeta₀`, the functional equation, Stirling for `Γ` on vertical
lines, `Complex.circleIntegral` and the residue calculus, `MeromorphicOn.divisor` with local
finiteness.  Zero counting itself is absent.

## Approach

- **A. Counting functions and their band property.** *(closed)* Define `N` and `N₀` as `ξ`-divisor
  masses over compact regions; prove nonnegativity, the congruence lemma, and the band-existence
  statement that the consuming card actually uses.
- **B. Monotonicity and additivity.**  `N` is monotone; the mass of a disjoint union splits.  With
  `A` this reduces "there is a zero in the band" to a numeric inequality between counts.
- **C. The rectangle argument principle for `ξ`.**  Total divisor mass of a rectangle equals the
  winding of `ξ` along its boundary.  The corpus has the circle version; the rectangle needs a
  contour built from four segments and the same factorisation argument.
- **D. The Γ-factor phase.**  Stirling on the vertical line gives
  `arg Γ(s/2) = (T/2)log(T/2) − T/2 + O(1)` on `Re s = 1/2 + iT`, which supplies the main term.
- **E. `S(T) = O(log T)`.**  Backlund/Jensen: the number of sign changes of `Re ζ` on the segment is
  `O(log T)` because `ζ` is bounded by a power of `T` on the box and `ζ(2 + iT)` is bounded below.
- **F. Assembly.**  `N(T) = (T/2π)log(T/2π) − T/2π + O(log T)`, and the difference form
  `N(βT) − N(αT) = ((β−α)/2π) T log T + O(T)` the consuming card needs.
- **G. The five-twelfths theorem.**  Pratt–Robles–Zaharescu–Zeindler 2020.  Levinson's method with
  a mollifier of degree three plus the twisted fourth moment.  This is by far the largest layer and
  is properly its own card once F lands.
- **H. The consuming interface.**  Export the band statement in the coordinates of
  `suzuki-critical-radical-anchor-finite-head-reduction` and wire it into that card's fifth gate.

## Gates

- [x] 0 → 1  well-posed, source identified, existing corpus/mathlib inventory taken
- [x] A. counting functions, compact boxes, band-existence, conjugate copy
      — `RHTower/XiZeroCountingFunction.lean`
- [x] B. monotonicity of the counting functions, and `N₀ ≤ N`
      — `RHTower/XiZeroCountingFunction.lean`
- [x] upper half of F: `N(T) ≤ c T log T` — `RHTower/XiZeroCountJensenBound.lean`
- [x] C. rectangle argument principle for `ξ` — `RHTower/XiRectangleZeroCount.lean`
- [x] D. Γ-factor phase — **without Stirling**, from the corpus vertical digamma asymptotic
      — `RHTower/GammaVerticalPhaseAsymptotic.lean`
- [x] E. `S(T) = O(log T)` — Backlund's disc count and the sign-change-to-argument step
      (`RHTower/ZetaStripPolynomialBound.lean`, `RHTower/ZetaRealTraceDiscCount.lean`,
       `HTGeometry/ArgumentVariationSignChanges.lean`)
- [x] F. the two-sided `T log T` bound and the annular count
      (`RHTower/XiVerticalRatioLimit.lean`, `RHTower/XiSymmetricMassBounds.lean`,
       `RHTower/XiAdmissibleHeights.lean`)
- [x] G. the five-twelfths proportion theorem — **retired**, see the 2026-08-17 log entry
- [x] H. the consuming interface for the critical-radical-anchor card
      — `RHTower/XiOrdinateBandCopies.lean`, `RHTower/XiAnnularCopyCount.lean`
- [x] 1 → 2  complete paper proof recorded (the Lean chain is the proof)
- [x] 2 → 3  Lean theorem, axiom surface `propext, Classical.choice, Quot.sound`

## Log
- 2026-08-16 — created.  The consuming card
  `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki/suzuki-critical-radical-anchor-finite-head-reduction.md`
  has every other gate closed; this is its only remaining input, and its handoff forbids a
  hypothesis wrapper.

  **A closed.**  `RHTower/XiZeroCountingFunction.lean` defines `N` and `N₀` as `ξ`-divisor masses
  over the compact box `[0,1] × [0,T]` and the compact segment `{1/2} × [0,T]`.  Two design points.

  First, counting on the *closed* band `[0, T]` rather than `(0, T]` costs nothing — `ξ` has no real
  zeros in the strip — and buys compactness, which is what `MeromorphicOn.divisor`'s local
  finiteness needs.

  Second, the property the consuming card uses is not the asymptotic itself but the band statement
  "a strict increase across `(T₁, T₂]` produces a zero there".  That is proved directly, without
  additivity: if no zero has ordinate in the band, then for every zero `u` the two box memberships
  are equivalent, so the two divisor *functions* are equal and hence so are the masses.  This means
  layers B–F feed the card through a single numeric inequality `N₀(βT) > N₀(αT)`, and nothing about
  the internal structure of the counting functions has to be re-proved downstream.

  All new declarations audit to `[propext, Classical.choice, Quot.sound]`.

  **B closed.**  `xiRegionOrderSum_mono` compares two masses through a single Finset — the support of
  the larger region's divisor — after checking that the smaller region's support is contained in it.
  The termwise inequality is the trichotomy `u ∈ S`, `u ∈ S' ∖ S`, `u ∉ S'`.  Consequences:
  `xiZeroCount_mono`, `xiCriticalZeroCount_mono`, and `xiCriticalZeroCount_le_xiZeroCount`, the
  last being the `N₀(T) ≤ N(T)` the consuming card's `(SR-64.24)` uses.

  All audit to `[propext, Classical.choice, Quot.sound]`.

- 2026-08-17 — **The five-twelfths layer is retired, and the consumed statement is now a plain
  annular count.**  The consuming card's sharpening removed the critical line from the payment
  criterion: with `X = 1 + k - u`, `Y² = 4uk` and the strip bound `u < 1/4`, every Xi copy obeys

  ```text
  tau_r <= 1/(k+3/4),   a_r >= 1/(k+3),
  ```

  so an arbitrary copy above the band floor `3(1+h)` is a valid witness
  (`RHTower/SuzukiGeneralWitnessAnnularPayment.lean`, `RHTower.annulus_general_payment`).  What the
  consuming card now needs is

  ```text
  ∃ K > 1, ∃ Γ₀, ∀ Γ ≥ Γ₀:  N(KΓ) − N(Γ) ≥ (87/256)K² + 1,
  ```

  a **constant** number of ξ-zeros — on or off the line — in one fixed annulus.  Under any
  two-sided bound `c₁ T log T ≤ N(T) ≤ c₂ T log T` this holds for every `K > c₂/c₁`, because
  `N(KΓ) − N(Γ) ≥ (c₁K − c₂)Γ log Γ → ∞` while the requirement is a constant.

  Consequences for this card:

  - **G is dropped entirely.**  `N₀` and the Levinson/PRZZ mollifier layer leave the critical path;
    only `N` is needed.  Gate A's critical-line counting function stays as a definition but is no
    longer consumed.
  - **F is weakened.**  The sharp asymptotic is not required; a two-sided `T log T` bound with any
    explicit constants suffices, and `K` is then chosen from the constants.
  - The upper half `N(T) ≤ c₂ T log T` follows from mathlib's Jensen inequality
    `AnalyticOnNhd.sum_divisor_le` together with the corpus order-one envelope
    `RHTower.orderOneEnvelope_riemannXi`, with no contour integration at all.
  - The lower half `N(T) ≥ c₁ T log T` still needs C–E: the rectangle argument principle, the
    Γ-factor phase, and `S(T) = O(log T)`.  For E, `arg ζ` on the vertical line `Re s = 2` is
    bounded by `π/2` outright, since `|ζ(2+it) − 1| ≤ ζ(2) − 1 < 1`; the only genuine work is
    Backlund's disc count for the horizontal segment, and that is again mathlib's
    `AnalyticOnNhd.sum_divisor_le`.

- 2026-08-17 (later) — **The Jensen upper bound is closed.**
  `RHTower/XiZeroCountJensenBound.lean` proves

  ```text
  xiRegionOrderSum_closedBall_le :
    0 < r → (xiRegionOrderSum (closedBall 0 r) : ℝ)
              ≤ (C (1 + 2r) log (2 + 2r) + log 2) / log 2,
  exists_xiZeroCount_upper_bound :
    ∃ c > 0, ∀ T ≥ 2, (xiZeroCount T : ℝ) ≤ c T log T,
  ```

  from mathlib's `AnalyticOnNhd.sum_divisor_le`, the corpus envelope
  `RHTower.orderOneEnvelope_riemannXi` transported along `xi_eq_riemannXi`, and `ξ(0) = 1/2`.
  Doubling the radius makes `log(R/r) = log 2`, and every zero counted by `N(T)` lies in the closed
  disc of radius `1 + T`.  Axiom surface `propext, Classical.choice, Quot.sound`.

  **The lower half provably cannot be softened.**  Four candidate shortcuts were checked and all
  fail for the same structural reason.

  1. *Partial fractions.* `Re ξ'/ξ(2 + iT) = ½ log T + O(1)` with each zero contributing
     `≤ 1/(σ − 2)` bounds the local count from below only if the tail `∑_{|γ − T| > 1}` is smaller
     than the main term; with the Jensen upper bound the tail constant is `≥ π²/3 · c₂ ≫ ½`.
     Sharpening `c₂` from `e/2` (max) to `e/π` (circle average) is not nearly enough.
  2. *Zero-free-annulus rigidity.*  In a zero-free annulus Jensen makes the circle average
     `m(r) = (1/2π)∫ log|ξ(re^{iθ})|dθ` exactly linear in `log r` with slope `n(Γ)`, and the true
     growth is `(K−1)Γ log Γ/π` against the permitted `Γ log Γ log K/π`.  The contradiction needs a
     *lower* bound on `m(KΓ)`.
  3. *Nevanlinna.*  For entire `ξ`, `T(R) = m⁺(R)` and the first main theorem returns exactly
     Jensen: `N(R) = m⁺(R) − m⁻(R) − log|ξ(0)|`.  A lower bound for `N` is a statement that the
     deficiency `δ(0, ξ)` is bounded away from `1`, and at order one that is false in general
     (`e^z` has `δ(0) = 1`).
  4. *Ray growth + three circles.*  `T(2R) ≥ ⅓ log M(R) ≥ c R log R` follows from
     `riemannXi_ray_growth`, but it bounds `m⁺`, not `m⁺ − m⁻`.

  Every route collapses to the same missing ingredient: a lower bound for the signed circle average
  of `log|ξ|`, which is equivalent to the zero count itself.  So the classical argument-principle
  route is the route: the main term is `T log T` and the error is `O(log T)`, so **no constant in
  the `S(T) = O(log T)` bound matters** — which is exactly why the classical proof succeeds where
  all four shortcuts fail.

  Remaining chain, in dependency order:

  - **D (now the gating item).** Stirling for `log Γ` on vertical lines.  The corpus has
    `RHTower/GammaJumpBinetFormula.lean` (a Binet-type term-by-term integral identity) and
    `RHTower/DigammaImaginaryVerticalAsymptotic.lean` (the full complex vertical digamma
    asymptotic), but no `log Γ(z) = (z − ½) log z − z + ½ log 2π + O(1/|z|)`.  That is the module to
    build, and it is independently valuable to the corpus.
  - **E.** `S(T) = O(log T)`: `|arg ζ(2 + it)| < π/2` outright from `|ζ(2+it) − 1| ≤ ζ(2) − 1 < 1`,
    and Backlund's disc count for the horizontal segment is `AnalyticOnNhd.sum_divisor_le` again,
    now available and already exercised here.
  - **C, F.** The rectangle contour and the assembly.

- 2026-08-17 (later still) — **D is closed without Stirling, and E's analytic half is closed.**

  **D.** The card assumed Stirling for `log Γ` on vertical lines.  That is unnecessary: the phase is
  the integral of the *real part of the digamma function*, and the corpus already owns the vertical
  digamma asymptotic `re_digamma_vertical_sub_log_tendsto_zero` (`Re ψ(σ + it) = log t + o(1)`).
  Integrating,

  ```text
  gammaVerticalPhase σ T := ∫₀^T Re ψ(σ + it) dt = T log T − T + O(1) + o(T),
  ```

  so `RHTower.tendsto_gammaVerticalPhase_ratio : gammaVerticalPhase σ T / (T log T) → 1` for every
  `σ > 0`.  Supporting declarations: `analyticOnNhd_Gamma_rightHalf`, `continuousAt_digamma`,
  `continuous_digammaVerticalRe`, and the Cesàro lemma `tendsto_integral_div_atTop` (a vanishing
  function has sublinear primitive).  No Binet integral, no asymptotic expansion.

  **E, analytic half.**  Two modules:

  ```text
  RHTower/ZetaStripPolynomialBound.lean
    norm_riemannZeta_le_of_re_pos    ‖ζ(σ+it)‖ ≤ 2 + 2|t|/σ   for 0 < σ ≤ 2, |t| ≥ 2
    norm_riemannZeta_le_of_two_le_re ‖ζ(s)‖ ≤ π²/6            for Re s ≥ 2
    norm_riemannZeta_le_quarter      ‖ζ(s)‖ ≤ 2 + 8|Im s|     for Re s ≥ 1/4, |Im s| ≥ 2

  RHTower/ZetaRealTraceDiscCount.lean
    zetaRealTrace                    F_T(z) = (ζ(z+iT) + ζ(z−iT))/2
    zetaRealTrace_ofReal             F_T(σ) = Re ζ(σ+iT)
    norm_riemannZeta_sub_one_le      ‖ζ(2+it) − 1‖ ≤ π²/6 − 1
    two_sub_pi_sq_div_six_le_re      Re ζ(2+iT) ≥ 2 − π²/6 > 0
    analyticOnNhd_zetaRealTrace      analyticity on the disc of radius 7/4 about 2
    zetaRealTrace_divisor_le         Jensen's bound on the disc of radius 3/2
    exists_zetaRealTrace_count_bound ∃ c > 0, ∀ T ≥ 4, (zero count) ≤ c log T
  ```

  The polynomial bound comes from PNTPlus's Euler–Maclaurin identity `Zeta0EqZeta` **at `N = 1`**:
  the finite sum is `1`, the two boundary terms are each at most `1/2` once `|t| ≥ 2`, and
  `ZetaBnd_aux1` bounds the remaining integral by `2|t|/σ`.  Crude, but only its logarithm enters
  Jensen.

  What remains for E is purely topological: converting "at most `c log T` sign changes of
  `Re ζ(σ + iT)` on `σ ∈ [1/2, 2]`" into "the continuous argument of `ζ` varies by at most
  `π(1 + c log T)` along that segment".  Then C (the contour) and F (assembly) close the card.

- 2026-08-17 (E closed) — the topological half of E is
  `HTGeometry/ArgumentVariationSignChanges.lean`:

  ```text
  exists_cos_eq_zero_of_pi_lt        an interval of length > π meets a zero of cos
  abs_im_sub_le_pi_of_re_ne_zero     constant sign of Re confines the argument to a strip of width π
  abs_im_sub_le_pi_of_re_ne_zero_Ioo the same across a cell whose interior is sign-free
  abs_im_sub_le_of_finite_re_zeros   |Δ arg| ≤ (#sign changes + 1)·π
  ```

  The mechanism: `Re γ = exp(Re L)·cos(Im L)`, so on a preconnected set where `Re γ` never vanishes
  the continuous image `Im L '' J` is an interval avoiding every zero of the cosine, hence has
  length at most `π`.  Splitting a compact interval at the zeros of `Re γ` and telescoping gives the
  cell bound, by strong induction on the number of interior zeros.

  Combining with `exists_zetaRealTrace_count_bound`, the argument of `ζ` varies by `O(log T)` across
  `σ ∈ [1/2, 2]` at height `T`, which is `S(T) = O(log T)`.  Gates D and E are therefore closed; C
  (the contour) and F (assembly) remain.

- 2026-08-17 (C closed) — **The rectangle argument principle for `ξ` is Lean-proved**, by feeding
  `logDeriv xi` to PNTPlus's rectangle residue theorem rather than building a contour from scratch.

  ```text
  RHTower/XiRectangleZeroCount.lean
    meromorphicOrderAt_logDeriv_xi_nonneg_of_ne_zero  ξ'/ξ is analytic off the divisor
    hasSimplePolesOn_logDeriv_xi                      order ≥ −1 everywhere
    logDeriv_xi_pole_iff                              poles of ξ'/ξ = zeros of ξ
    residue_logDeriv_xi                               residue = vanishing order
    xi_zeros_rectangle_finite                         finitely many poles in a rectangle
    rectangleIntegral_logDeriv_xi                     (1/2πi)∮ ξ'/ξ = Σ orders
    rectangleIntegral_logDeriv_xi_eq_regionOrderSum   … = xiRegionOrderSum of the rectangle
  ```

  The corpus already owned `meromorphicOrderAt_logDeriv_xi_eq_neg_one` and
  `meromorphicAt_logDeriv_xi` (`RHTower/XiLogDerivNonholonomic.lean`), and
  `HTGeometry/LogarithmicResidueQuantization.lean` supplied the residue limit; PNTPlus supplied
  `RectangleIntegral'_eq_sumResiduesIn`.  The only hypothesis is that the boundary avoids the
  divisor.

  **What F now needs.**  Writing `f = logDeriv xi` and using `Im (VIntegral f x y₁ y₂) = ∫ Re f`,
  `Im (HIntegral f x₁ x₂ y) = ∫ Im f`, the reflection `ξ(s̄) = conj ξ(s)` and the functional equation
  `ξ(1−s) = ξ(s)` collapse the four sides of the rectangle `[−1,2] × [−T,T]` to

  ```text
  N(T) = (1/π) ∫₀^T Re f(2+iy) dy − (1/2π) ∫_{−1}^{2} Im f(x+iT) dx.
  ```

  The first integral splits along
  `f(s) = 1/s + 1/(s−1) − ½log π + ½ψ(s/2) + ζ'/ζ(s)` into

  - `gammaVerticalPhase 1 (T/2)` (closed, gate D),
  - `−(T/2) log π`,
  - `arctan` terms bounded by `π`,
  - `∫₀^T Re(ζ'/ζ)(2+iy) dy = Im log ζ(2+iT) − Im log ζ(2)`, bounded by `π` because
    `Re ζ(2+iy) > 0` puts the principal branch in a half-plane (closed, `two_sub_pi_sq_div_six_le_re`).

  The second integral is the argument variation of `ξ` along a horizontal segment, bounded by
  `O(log T)` from Backlund (gate E) plus explicit bounds on the three Archimedean factors.

- 2026-08-17 (F, vertical half) — the four-factor splitting and the vertical contribution are
  Lean-proved.

  ```text
  RHTower/XiLogDerivFactorization.lean
    logDeriv_quadratic, logDeriv_piPow, logDeriv_gammaHalf
    xi_eq_four_factors, logDeriv_xi_eq

  RHTower/XiVerticalPhaseTwo.lean
    re_logDeriv_xi_two_add                   the pointwise real part at 2 + iy
    continuous_re_logDeriv_xi_two, continuous_re_logDeriv_zeta_two
    integral_re_logDeriv_xi_two              the integrated splitting
    integral_rational_head                   ∫₀^T [2/(4+y²)+1/(1+y²)] = arctan(T/2) + arctan T
    abs_integral_rational_head_le            … bounded by π
    hasDerivAt_log_zeta_two                  the principal branch is differentiable on Re s = 2
    abs_integral_re_logDeriv_zeta_two_le     |∫₀^T Re(ζ'/ζ)(2+iy)| ≤ π
  ```

  So

  ```text
  ∫₀^T Re(ξ'/ξ)(2+iy) dy = gammaVerticalPhase 1 (T/2) − (T/2) log π + O(1),
  ```

  with the `O(1)` split into two explicit `≤ π` bounds — the arctangent head, and the ζ phase,
  which stays in a half-plane because `Re ζ(2+iy) ≥ 2 − π²/6 > 0`, so the *principal* logarithm
  already is the continuous branch.

  What remains in F: the horizontal side `∫_{−1}^{2} Im(ξ'/ξ)(x+iT) dx = O(log T)` (Backlund from
  gate E plus explicit bounds on the three Archimedean factors), the four-side symmetry reduction
  using `ξ(s̄) = conj ξ(s)` and `ξ(1−s) = ξ(s)`, and the final two-sided `T log T` bound.

- 2026-08-17 (F, horizontal half) — closed.  `RHTower/ZetaRealTraceSignChanges.lean` and
  `RHTower/XiHorizontalBound.lean` give `|∫_{1/2}^{2} Im(ξ'/ξ)(x+iT) dx| ≤ c log T`, using
  `HTGeometry/DistinctZerosLeDivisor.lean` to turn the Jensen divisor bound into a bound on the
  number of *distinct* sign changes, and `RHTower/ZetaHorizontalArgument.lean` to realise the
  argument increment as the integral itself (the branch is *constructed* as
  `Λ(x) = log ζ(x₀+iT) + ∫ (ζ'/ζ)`, and `ζ·e^{−Λ}` is constant).

  The digamma term needed no sector asymptotic: the corpus sandwich is uniform in the abscissa, so
  `0 ≤ Im ψ(σ+it) ≤ π + 1/t` for every `σ ≥ 0`.

  All four gates C, D, E, F now have their analytic content in Lean.  What remains is bookkeeping:
  the limit `mass(T)/(T log T) → 1/π` from `tendsto_gammaVerticalPhase_ratio` plus the two `≤ π`
  remainders and the `O(log T)` horizontal bound, and the choice of two heights off the (finite in
  any bounded range) ordinate set to convert the mass difference into an annular count.

- 2026-08-17 (F closed) — the assembly is done.

  ```text
  RHTower/XiVerticalRatioLimit.lean
    tendsto_bounded_div_TlogT      a bounded numerator over `T log T` vanishes
    tendsto_vertical_ratio         ∫₀^T Re(ξ'/ξ)(2+iy) dy / (T log T) → 1/2

  RHTower/XiSymmetricMassBounds.lean
    xiSymmetricMass                the divisor mass of [−1,2] × [−T,T]
    two_pi_mul_xiSymmetricMass     the quarter-path formula at a = 2
    exists_xiSymmetricMass_two_sided
        ∃ T₀, ∀ admissible T ≥ T₀,
          (1/2π) T log T ≤ mass T ≤ (2/π) T log T

  RHTower/XiAdmissibleHeights.lean
    exists_admissible_height       heights carrying no ξ-zero are dense
    exists_annular_mass_lower      ∀ C, ∃ Γ₀, ∀ Γ ≥ Γ₀, two admissible heights
                                   Γ < T₁ < T₂ < 10Γ with mass T₂ − mass T₁ ≥ C
  ```

  The two-sided constants `1/2π` and `2/π` differ by a factor `4`, so the annulus ratio `10` is
  comfortable: with `T₁ < 2Γ` and `T₂ > 9Γ` the difference is at least
  `(1/2π) Γ log Γ − (4 log 2/π) Γ → ∞`.

  Admissibility is not a restriction: all ξ-zeros lie in the open strip, so those with ordinate in a
  bounded interval sit in a compact box and are finite, and any nonempty interval of heights
  contains one that the whole horizontal line misses.

  **This closes the card's Lean content.**  `exists_annular_mass_lower` is exactly `(SR-64.35)` in
  divisor-mass form; what remains is the interface that converts a divisor-mass difference into a
  `Finset XiZeroCopy` for `suzuki-critical-radical-anchor-finite-head-reduction`.

- 2026-08-17 (card closed) — the consuming interface is built and
  `suzuki-critical-radical-anchor-finite-head-reduction` is at stage 3.

  ```text
  RHTower/XiOrdinateBandCopies.lean
    xiSymmetricMass_eq_support_sum    the mass is the total multiplicity below a height
    xiSymmetricMass_diff_eq_card      a mass difference is a band copy count
  RHTower/XiAnnularCopyCount.lean
    exists_annular_copies             the annular count, unconditional
    exists_annular_payment_of_large_height
  ```

  Every gate of this card is closed.  The zero-counting statement actually delivered is the
  two-sided `T log T` bound plus the annular count, not the sharp asymptotic — that is what the
  consumer needs, and it is strictly cheaper.  `N₀` and the five-twelfths layer were never built and
  are not needed by anything.
