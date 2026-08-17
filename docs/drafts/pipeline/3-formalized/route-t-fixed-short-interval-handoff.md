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
- [x] 2 → 3  formalized: unconditional Lean prime-supply theorem, Route-T composition, direct check,
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

`[LEAN-PROVED]` The former open core is closed.  The uniform-detector zero-density tower
(`InghamUniformDetectorMellin*.lean`) carries the quantitative density estimate and the
density-to-short-ranges summation all the way to an unconditional eventual prime, at the fixed
rational exponent `71/100` rather than `7/10`
(`exists_eventually_routeT_prime_in_every_base_window`).  Since `2/3 < 71/100 < theta_*`, this is
the same collapse the card's C2/C3 argument asks for, with the fixed rational chosen inside the
same open interval; see "Lean progress -- prime supply in every upper physical window".

## Log

- 2026-08-14 — `[PAPER-PROVED] [BRIDGE]`; exact scalar margins and formal analytic open core isolated.
- 2026-08-14 — scalar interface `[LEAN-PROVED]`; direct Lean check and axiom audit pass with only
  `propext`, `Classical.choice`, and `Quot.sound`; full prime-supply theorem remains Stage 2.
- 2026-08-14 — exact smooth Chebyshev zero-crossing dependency `[LEAN-PROVED]`; finite contours no
  longer require a zero-free interior or an assumed zero-free boundary.

## Lean progress -- the unconditional scalar composition

`formal/GaloisForLFunctions/RHTower/Sieve/RouteTShortIntervalHandoff.lean` (new, umbrella-wired,
axiom-clean) proves the card's whole reduction, with no zero-density and no route-specific input.

| Card item | Declaration |
|---|---|
| `7/10 < theta_* = 3/4 - d/2`, from the corpus bound `d < 1/100` | `sevenTenths_lt_routeTPhysicalSliceHandoffTheta` |
| hence `7/10 < 1 - 1/mu` for every `mu >= mu_*`, using the corpus handoff `routeTPhysicalSliceHandoffTheta_le_widthExponent` | `sevenTenths_lt_widthExponent` |
| the fixed window `(x, x + x^{7/10}]` sits inside every Route-T upper physical window, for `x >= 1` | `routeT_window_contains_sevenTenths_window` |
| **the handoff transfer**: a prime in the fixed window already lies in every Route-T upper physical window | `routeT_prime_in_upperWindow` |

This is exactly the content of C61: the continuum of route-specific seam widths collapses to *one*
classical prime-supply exponent, and the collapse itself is unconditional.

### What remains

Only the `[LITERATURE]` input the card already names: an unconditional short-interval prime-supply
theorem at the single fixed exponent `7/10`, i.e. `for all large x there is a prime in
(x, x + x^{7/10}]`.  Classical prime number theory with the Vinogradov--Korobov error term does
*not* reach this: its error `x exp(-c sqrt(log x))` dominates `x^{7/10}`.  The genuine input is a
zero-density estimate -- Ingham's `A(sigma) <= 3/(2-sigma)`, or already the weaker uniform envelope
`A(sigma) <= 3`, combined with the standard density-to-short-ranges transfer
`theta_PNT <= 1 - 1/||A||_infinity`.  Neither is in mathlib nor in the vendored `PNTPlus`, so this
is a self-contained analytic-number-theory formalisation project, and it is the *only* thing
between this card and stage 3.

## Lean progress -- prime supply in every upper physical window

`formal/GaloisForLFunctions/RHTower/Sieve/RouteTFixedShortIntervalPrimeSupply.lean` (new,
umbrella-wired, axiom-clean) closes the card.  It composes the corpus's unconditional
short-interval prime supply with the scalar handoff and turns the `mu`-indexed family of
`Eventually` statements into the card's *single* threshold.

| Card item | Declaration |
|---|---|
| the fixed exponent lies strictly above the coefficient-three density threshold | `two_thirds_lt_routeTHoheiselEveryBaseExponent` |
| `2/3 < 71/100 < theta_*`, i.e. C2's "one rational with fixed margins on both sides" | `routeTHoheiselEveryBaseExponent_mem_margin` |
| prime supply at the fixed exponent, with an explicit threshold | `exists_threshold_routeT_prime_in_fixed_window` |
| **the card's exact statement**: one `X_0 >= 1` such that for every `x >= X_0` and every `mu >= mu_*` there is a prime in `(x, x + x^(1-1/mu)]` | `exists_threshold_routeT_prime_in_every_upperPhase_window` |
| the same supply as strictly positive Chebyshev mass on the physical window | `exists_threshold_routeT_upperPhase_theta_window_pos` |

`#print axioms` on all four: `propext`, `Classical.choice`, `Quot.sound` only.

### The one deviation from the paper proof, and why it is faithful

The paper proof runs through `theta_0 = 7/10`.  The corpus's unconditional supply
(`exists_eventually_routeT_prime_in_every_base_window`, from the uniform-detector zero-density
tower) is at `71/100`.  The card's C2 asks precisely for *one* fixed rational strictly between the
coefficient-three threshold `2/3` and the handoff exponent `theta_* = 3/4 - d/2`, chosen so that
both margins are fixed and rational; `71/100` is such a rational
(`routeTHoheiselEveryBaseExponent_mem_margin`), and the exponent monotonicity step
`x^{71/100} <= x^{1-1/mu}` for `x >= 1` is identical.  Nothing else in the argument depends on the
particular value, so the statement proved is the card's statement verbatim, not a weakening: the
theorem quantifies only over `x` and `mu`, never over `theta_0`.

The uniformity of `X_0` in `mu` is genuine and not an artefact of the restatement: the threshold
comes from the fixed-exponent supply alone, and the passage to width exponent `1-1/mu` is the
pointwise monotonicity step, which needs only `x >= 1`.

### Log

- 2026-08-17 -- `[LEAN-PROVED]`; the analytic open core (Ingham density plus density-to-short-ranges)
  was already discharged inside the corpus's uniform-detector tower at exponent `71/100`, so the
  card closes with the scalar composition above.  Direct check, olean build, and axiom audit pass.
