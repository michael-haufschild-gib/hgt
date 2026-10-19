# Known-method applications of the RH source calculus

- **ID:** review1910-known-method-applications
- **Stage:** 3-formalized
- **Type:** THEOREM; 31 unconditional Lean theorems verified; application audit complete
- **Source:** `docs/reports/review-1910/hard-obstacles-summary-1910.md`, section 1
- **Statement:** Unconditional finite observation inversion with complete graph/energy budgets, literal Möbius/BV recovery, and simultaneous Hausdorff positivity for any finite set of orders.

## Scope and completion requirements

The task covers all five application categories in the summary. Existing theorems
are reused rather than duplicated. Open RH-closing estimates are not premises of
new results. No numerical experiments or finite numerical certificates are used.

| Category | Required output | State |
|---|---|---|
| Exact identities and receiver implications | Check the listed route applications against actual declarations; preserve source, normalization, domain and the exact remaining premise. | All 47 route/candidate interfaces inspected; facts recorded in the owned knowledge ledger. |
| Specified finite problems with rigorous error | Exact symbolic finite reconstruction, a two-sided complete-energy enclosure, and simultaneous positivity for a finite set of Hausdorff orders. | Proved in the finite decoder and finite-order positivity modules. |
| Reconstruction and graph-error specialization | Price anchor loss and finite inversion for actual Möbius and Barban–Vehov rows, with all arithmetic side conditions proved. | Arithmetic decoding module supplies exact inverse losses and fixed-cutoff reference budgets. |
| Source instantiation | Construct the decoded finite arithmetic source in the original complete graph; check the other named source-admission applications. | Literal Möbius/BV graph recovery proved; other general admission interfaces inspected. |
| Obstruction and repair formulas | Include zero-anchor loss explicitly; check the named existing corrections and the scope of their positive conclusions. | Exact zero-anchor loss and BV observation-loss boundary proved; existing repair interfaces audited. |

All named applications from section 1 are covered: WL, RW, PA, CHMD, PM,
BVI, JAS, PBM, RB, LA, TH, HCF, XN, CTF, APF, IRK, BiScale, FU, RFHM, SZ,
RN, MSC, W1C, PW-B, THIM, ACT, RP, EGC and PCS. The route-by-route A-items
provide the remaining application details; all 47 entries have an explicit
source and mathematical boundary in the knowledge ledger.

The finite-evaluation category specifies no matrix entries, interval, disc,
contour or tolerance. The supplied outputs therefore quantify symbolically
over finite data. No numerical certification is claimed. Existing general
source-admission and repair theorems are retained without redundant aliases;
an application requiring an unproved RH-closing estimate is not marked solved.

## Exact finite decoder

Fix natural horizon `N`, clock cutoff `k`, a real coefficient row `c`, real anchor
`a`, and arbitrary real observed row `z`. Let

`Y_c(q) = sum_{1<=d<=N, q|d} c(d)/d`,
`D_a(z)(d) = d sum_{1<=m<=N/d} mu(m) z(dm)/a`,
`F(c) = sum_{1<=d<=N} c(d) A_d`,

where `A_d` is the canonical full arithmetic graph clock. Division by zero uses
Lean's total real division. Write `e(q)=z(q)-a Y_c(q)` and

`K = |a/a-1| ||F(c)|| + inversionCost(N,k,q -> |e(q)/a|)`.

### Paper proof

Finite multiples inversion gives
`D_a(z)(d)-c(d)=(a/a-1)c(d)+d sum mu(m)e(dm)/a`
for every active `d`. This is finite algebra and holds also at `a=0`.
Linearity of finite synthesis separates the first term. The triangle inequality
and the existing weighted inversion estimate give

`||F(D_a(z))-F(c)|| <= K`.

The complete signed energy satisfies
`|E(u)-E(v)| <= ||u-v||^2 + 2||u-v||||v||`.
Consequently the unconditional error enclosure is

`|E(F(D_a(z)))-E(F(c))| <= K^2 + 2K||F(c)||`.

Every term uses the original full source graph, including its mass and all
prime-power edges. No realizability assumption on `z`, positivity assumption,
small-error premise, or RH hypothesis is needed.

At `a=0`, the decoder vanishes and the defect is exactly `||F(c)||`.
At a proved nonzero arithmetic anchor, the defect vanishes. Exact observations
then recover the finite source. The useful replacement for an unjustified
positive-denominator assumption is explicit accounting of both cases.

## Literal arithmetic rows

Let `p` be the `n`-th prime and set the horizon to `p`. Then `p>=2` and the
only active multiple of `p` is `p` itself. Consequently the Möbius anchor is
`Y_mu(p)=-1/p`. For the actual BV taper with `X=p+m+1`, the anchor is
`-log(X/p)/p<0`. Both anchors are nonzero without an added premise.

For observation residual `e(q)=z(q)-Y_c(p)Y_c(q)`, the graph radii become
`p inversionCost(|e|)` for Möbius and
`p/|log(X/p)| inversionCost(|e|)` for BV. This follows by pulling the
constant reciprocal anchor through the finite inversion sums. Substitution
in the complete-energy estimate gives the two arithmetic decoding bounds.
Zero residual gives exact source recovery.

The established fixed-cutoff budget supplies one `B>0` for every horizon:
`||F_mu|| <= B sqrt(p) H_p` and
`||F_BV|| <= B sqrt(p) log(X) H_p`. Inserting these bounds in the linear
term of `K²+2K||F||` gives the stated arithmetic energy budgets. Nonnegativity
of `K` follows from its norm-error bound. For arbitrary `X`, the entire BV
mixed row vanishes exactly when `X<=p`; this is a loss of observation, not
vanishing of the reference source.

## Finite simultaneous Hausdorff positivity

For a finite set `S` of orders, set
`R(S) = max({primeArchHausdorffShiftThreshold j | j in S} union {0})`.
Every `j in S` has its established threshold at most `R(S)`. Hence its
scaled Hausdorff moment difference is nonnegative at `R(S)+r`, for every
natural `r`. Choosing `S = {0,...,n}` proves simultaneous positivity for
every order through `n`, with no unproved sign premise. Finite maxima also
give monotonicity under inclusion and the exact union law.

This is a symbolic finite-order certificate. `R(S)` is supplied by the
existing existence theorem; no effective numerical value or bound uniform
over all orders is asserted.

## Lean modules and ownership

- `formal/GaloisForLFunctions/RHTower/FinitePrimeAnchorDecoder.lean`: 11 theorems.
- `formal/GaloisForLFunctions/RHTower/PrimeAnchorArithmeticDecoding.lean`: 15 theorems.
- `formal/GaloisForLFunctions/RHTower/PrimeArchFiniteOrderHausdorffPositivity.lean`: 5 theorems.
- All three are imported once by `formal/GaloisForLFunctions/RHTower.lean`.
- Facts and failures: `logs/known-method-applications-1910-facts.md`.

## Verification requirements

- [x] Symbolic proofs; no new assumptions or axioms; all public conclusions audited.
- [x] All five categories and all 47 route/candidate applications accounted for; 57 declaration references checked against their actual source files.
- [x] Source side conditions discharged for actual arithmetic specializations.
- [x] Each new leaf passed its final `lake env lean <file>` audit without diagnostics.
- [x] Dependency targets restored with `--old`; no full or umbrella build. Final leaf audits run sequentially.
- [x] All 41 public declarations audited from `/tmp`: only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Umbrella wiring and generated indexes checked. Formal lint executed without a build; three unrelated missing imports prevent the global gate from passing.
- [x] Owned scratch artifacts removed; interrupted dependency outputs restored; concurrent work preserved.

Final source audits, run sequentially from `formal/`, all returned exit code 0:

```sh
lake env lean GaloisForLFunctions/RHTower/FinitePrimeAnchorDecoder.lean
lake env lean GaloisForLFunctions/RHTower/PrimeAnchorArithmeticDecoding.lean
lake env lean GaloisForLFunctions/RHTower/PrimeArchFiniteOrderHausdorffPositivity.lean
```

The remaining global lint errors concern these concurrent modules, outside
this card's write scope:

- `BezoutValuationIncidence.DifferentiatedBarbanVehovKernelsAndSmoothPrimeSigmaRate`
- `TransHorizonIncidenceMechanics.MatomakiTeravainenPaperScaleSieveAndRankinEulerTail`
- `SquareRootThreshold.WindowedOffDiagonalBeyondThreshold`

All three new modules in this card are reachable from their umbrella. No
generated-index error remains in that lint result. Existing repository size
warnings are separate from these errors.

No RH-closing cancellation, positivity, cofinal compactness or source-to-divisor
identification is asserted by the finite decoder theorem.
