# Hedenmalm theta anomaly--Burnol corona escape

- **ID:** `hedenmalm-theta-anomaly-burnol-corona-escape`
- **Stage:** 1-in-progress
- **Label:** `P-G112`
- **Type:** `[THEOREM (LEAN)] [ROUTE-P TOPOLOGY CLASSIFICATION] [POSITIVE SURVIVOR]`
- **Parents:** `P-G111`, `HedenmalmTwoPrimeBezout.lean`,
  `HedenmalmTwoPrimeBezoutGrowthNoGo.lean`

## Frozen conjecture

P-G111's completed Gamma/co-Poisson cells should equal the existing entire centered multipliers at
every point, including the removable origin. Prime two and three should therefore generate the
entire-function unit ideal. But any pointwise real-axis synthesis

```text
b2(t) a2(t) + b3(t) a3(t) = 1
```

should pay a quantitative order-one topology loss because both source cells decay as `1/|t|`.
Prove a uniform linear lower bound, not merely qualitative unboundedness.

## Complete paper proof `[PROVED HERE]`

Off zero, both completed Burnol cell and `centeredMultiplierE` equal `centeredMultiplier`. At zero,
their values both simplify to `n^(-1/2) log n`. Existing entire Bezout generation therefore
transports verbatim to the literal Burnol cells.

For `t>0`, each prime-two/three cell has norm at most `2/t`, since `n^(-1/2)<=1`. Put
`M=max(||b2(t)||,||b3(t)||)`. Triangle inequality gives

```text
1 <= M(2/t)+M(2/t)=4M/t,
```

hence `M>=t/4`. This uses no continuity, measurability, or holomorphy of coefficients, so it applies
to every possible finite-prime pointwise synthesis. Applied to the entire Bezout pair, it proves
simultaneous algebraic existence and forced linear boundary escape.

## Scientific delta

P-G111 removed quotient existence. P-G112 classifies its missing topology: literal Burnol frame is
unimodular in `O(C)` but has no order-zero real-boundary right inverse; every inverse loses at least
one spectral order. Thus singularity is forced by source cells themselves, not chosen as auxiliary
rigging. Next construction must use an order-one graph domain (or a genuinely nonlocal all-prime
coupling), never a bounded finite-prime Hilbert multiplier.

This is stronger than corpus's prior qualitative bounded-Bezout no-go: it gives pointwise linear
escape for arbitrary coefficient functions and transports the result to literal completed Burnol
cells. Novelty claim is limited to this exact source identification and quantitative topology law.

## Falsifiers

- Completed Burnol cell differs from `centeredMultiplierE` at origin.
- Prime-two/three Burnol cells fail to generate entire-function unit ideal.
- A synthesis exists at some `t>0` with both coefficient norms below `t/4`.
- Bound requires coefficient regularity or an assumed Xi zero location.

## Gates

- [x] prior Burnol/two-prime/Bezout-growth corpus collision audit
- [x] conjecture frozen with quantitative falsifier
- [x] global Burnol/entire-multiplier equality formalized
- [x] Burnol entire Bezout synthesis formalized
- [x] arbitrary-coefficient pointwise linear escape formalized
- [x] entire synthesis plus forced escape capstone formalized
- [x] direct `lake env lean` passes
- [x] exact module `lake build` passes (`12934` jobs)
- [x] module wired into `RHTower.lean`
- [x] capstone axiom audit contains only standard Lean foundations
- [x] full `GaloisForLFunctions.RHTower` umbrella build passes (`19790` jobs)
- [ ] repository lint passes (blocked by 41 pre-existing unrelated unreachable modules)

## Lean status

Umbrella-wired module
`formal/GaloisForLFunctions/RHTower/HedenmalmThetaAnomalyBurnolCoronaEscape.lean` contains complete
result. Direct `lake env lean` and exact module build pass.

## Log

- 2026-08-13 — P-G112 frozen after P-G111 constructed faithful completed Burnol quotient frame.
- 2026-08-13 — Exact global cell identification, entire algebraic corona, and arbitrary-synthesis
  linear escape proved in Lean; exact module build passed.
- 2026-08-13 — Capstone axiom audit passed (`propext`, `Classical.choice`, `Quot.sound` only) and
  full RHTower umbrella build passed; repository lint reached unrelated pre-existing reachability debt.
