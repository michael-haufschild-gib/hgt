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
- [ ] C. rectangle argument principle for `ξ`
- [ ] D. Γ-factor phase from Stirling
- [ ] E. `S(T) = O(log T)`
- [ ] F. the Riemann–von Mangoldt asymptotic and its difference form
- [ ] G. the five-twelfths proportion theorem
- [ ] H. the consuming interface for the critical-radical-anchor card
- [ ] 1 → 2  complete paper proof recorded
- [ ] 2 → 3  Lean theorem, axiom surface `propext, Classical.choice, Quot.sound`

## Log
- 2026-08-16 — created.  The consuming card
  `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki/suzuki-critical-radical-anchor-finite-head-reduction.md`
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
