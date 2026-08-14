# Route T fixed short-interval handoff

- **ID:** `route-t-fixed-short-interval-handoff`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `rh-current-frontier-map.md` · Route T C61
- **Statement:** Every sufficiently large Route-T upper physical window contains a prime: the fixed
  exponent `7/10` lies strictly below every upper-window width exponent, and unconditional Ingham
  zero density gives prime supply at that fixed exponent.

## Goal

Delete Route T's signed over-height true-prime boundary as an independent analytic problem.  The
claim must use an unconditional classical prime-supply theorem and the exact corpus handoff, with no
RH, density-hypothesis, or route-specific cancellation premise.

## Gates

- [x] 0 → 1  in-progress: exact statement, source-pure mechanism, internal/external audits complete
- [x] 1 → 2  fully-proven: dependency-closed paper proof below
- [ ] 2 → 3  formalized: unconditional Lean prime-supply theorem, Route-T composition, direct check,
  umbrella build, lint, and axiom audit
- [ ] 3 → 4  publication-ready: standalone theorem, proof, Lean certificate, and Route-T dependency map

## Exact statement

Write

```text
d       = maynardLongGlobalAmplitudeDeficit,
mu_*    = 4/(1+2d),
theta_* = 1-1/mu_* = 3/4-d/2,
theta_0 = 7/10.
```

The corpus proves `0<d<1/100`.  The exact theorem is:

> There is `X_0>=1` such that, for every real `x>=X_0` and every real `mu>=mu_*`, there is a prime
> natural number `p` satisfying
>
> ```text
> x < p <= x + x^(1-1/mu).
> ```

## Frontier audit

- `[CORPUS]` `routeTPhysicalSliceHandoff_widthExponent` and
  `routeTPhysicalSliceHandoffTheta_le_widthExponent` in
  `formal/GaloisForLFunctions/RHTower/Sieve/MaynardUpperPhaseHandoff.lean` identify the exact upper
  width exponent.
- `[CORPUS]` `maynardLongGlobalAmplitudeDeficit_lt_one_hundredth` gives `d<1/100`.
- `[LOCAL-RESEARCH]` C60 in `route-t-maynard-near-one-endpoint-exclusion.md` reduced the unresolved
  upper phase to signed true-prime boundary mass; proper prime powers and every positive sub-height
  coloring are already closed.
- `[LITERATURE]` Ingham's 1940 density estimate is
  `N(sigma,T) << T^(3(1-sigma)/(2-sigma)) log(T)^5`, uniformly for `1/2<=sigma<1`.
  Tao--Trudgian--Yang, ANTEDB Theorem 11.14, records the equivalent exponent bound
  `A(sigma)<=3/(2-sigma)`.
- `[LITERATURE]` The standard density-to-short-ranges theorem gives
  `theta_PNT <= 1-1/||A||_infinity` (ANTEDB Proposition 15.4).  In particular the weaker uniform
  envelope `A(sigma)<=3` gives PNT, hence a prime, in every interval of length `x^theta` for each
  fixed `theta>2/3` and all sufficiently large `x`.

## Conjecture loop and hostile verdict

### C1 — Route T needs a new signed upper-boundary theorem `[FALSIFIED AS A NECESSITY]`

Killing mechanism: C61 gives a single lower exponent for every upper width.  Once this exponent is
compared with classical density theory, direct signed boundary control is optional rather than
necessary.

Strongest positive survivor: the whole upper phase can be erased by one fixed classical
short-interval theorem.  This changes the representation from a continuum of seam amplitudes to one
prime-supply exponent.

### C2 — Use the exact moving exponent `theta_*` `[REJECTED AS NEEDLESS ENDPOINT COUPLING]`

Killing mechanism: making the analytic theorem depend on the tiny Route-T deficit imports an
irrelevant endpoint into every zero-density and contour estimate.

Stronger replacement: choose one rational exponent strictly between the coefficient-three
threshold `2/3` and `theta_*`.  The choice `theta_0=7/10` leaves fixed rational margins on both sides.

### C3 — Fixed `7/10` prime supply `[BRIDGE; SURVIVES HOSTILE ATTACK]`

This is not new analytic number theory: Ingham is much stronger.  The route-specific composition is
new internal knowledge.  It does not assume RH, does not use Density Hypothesis, is stable under
endpoint rounding and fixed multiplicative losses because the exponent gap is positive, and applies
uniformly to every `mu>=mu_*`.

## Complete paper proof `[PAPER-PROVED]`

Set `theta_0=7/10`.  First,

```text
theta_* - theta_0
  = (3/4-d/2)-7/10
  = 1/20-d/2
  > 1/20-1/200
  = 9/200.
```

Thus `theta_0<theta_*`, with fixed reserve `9/200`.  If `mu>=mu_*`, the corpus handoff theorem gives
`theta_*<=1-1/mu`; hence

```text
theta_0 < 1-1/mu.                                      (1)
```

Second, Ingham's unconditional estimate gives

```text
A(sigma) <= 3/(2-sigma) <= 3       (1/2<=sigma<1).
```

Therefore `||A||_infinity<=3`.  By the density-to-short-ranges theorem,
`theta_PNT<=1-1/3=2/3`.  Since `theta_0=7/10>2/3`, there is `X_0>=1` such that for every real
`x>=X_0`,

```text
theta(x+x^theta_0)-theta(x) > 0.
```

The difference is a finite sum of `log p` over primes `x<p<=x+x^theta_0`; positivity therefore
produces a prime natural number `p` in that interval.

Finally `x>=1` and (1) imply monotonicity in the exponent:

```text
x^theta_0 <= x^(1-1/mu).
```

The same prime consequently satisfies

```text
x < p <= x+x^theta_0 <= x+x^(1-1/mu),
```

which proves the statement.  Fixed factors, integer endpoints, and open/closed endpoint choices are
absorbed by the strict `9/200` exponent reserve after enlarging `X_0`; none changes the theorem.

Hostile audit: multiplicities in `N(sigma,T)` are included in Ingham's theorem; the bound is uniform
in `sigma`; `theta_0` is strictly, not weakly, above `2/3`; exponent monotonicity is used only for
`x>=1`; and `mu_*` is positive.  No open dependency remains in the paper argument.

## Exact Lean frontier

`[LEAN-PROVED]` `MaynardUpperPhasePrimeSupplyHandoff.lean` formalizes the scalar interface:

```text
theta_* - 7/10 > 9/200,
1 - 3(1-7/10) = 1/10,
mu>=mu_* -> 7/10 < 1-1/mu,
x>=1 -> x^(7/10) <= x^(1-1/mu).
```

`[LEAN-PROVED DEPENDENCY]` `ZetaResidueUnitRectanglePeeling.lean` now removes the zero-free-box
restriction from the smooth Chebyshev contour. It proves exact multiplicity-weighted zero crossing
for the actual cutoff Mellin transform and unconditionally selects all four boundary edges. Thus
the explicit-formula geometry needed by density-to-short-ranges is closed at every finite height.

`[OPEN CORE]` Formalize Ingham's quantitative density bound and its density-to-short-ranges
summation strongly enough to produce the eventual prime in `(x,x+x^(7/10)]`, then compose it with
the scalar handoff and upper Route-T shell. Zero crossing and contour selection are no longer open;
the live analytic debt is the quantitative density estimate plus edge/height summation.

## Log

- 2026-08-14 — `[PAPER-PROVED] [BRIDGE]`; exact scalar margins and formal analytic open core isolated.
- 2026-08-14 — scalar interface `[LEAN-PROVED]`; direct Lean check and axiom audit pass with only
  `propext`, `Classical.choice`, and `Quot.sound`; full prime-supply theorem remains Stage 2.
- 2026-08-14 — exact smooth Chebyshev zero-crossing dependency `[LEAN-PROVED]`; finite contours no
  longer require a zero-free interior or an assumed zero-free boundary.
