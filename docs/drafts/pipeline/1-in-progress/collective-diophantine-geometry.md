# Collective Diophantine Geometry of the Prime Logarithms

- **ID:** CDG
- **Stage:** 1-in-progress
- **Type:** RESEARCH PROGRAMME
- **Source:** `docs/reports/review-0911/obstacles-summary.md`, §2.11.
- **Goal:** Growing-dimension return counting, collective approximation tools,
  and a sign-free producer of the two-sided prime-degree crude bound.

## Required mathematical outputs

1. Return counts uniform in growing prime families; augmented lattice minima.
2. Quantitative heavy-return/large-value transfer with explicit weight and mass.
3. A breadth mechanism beyond bounded-height rounding: first quadratic-log,
   then positive-power lower bounds for logarithmic return height.
4. A sign-free decision theorem at prime degrees and an arithmetic producer
   using the functional equation centred at one half.

## Established decision mechanism

The two-sided gap iteration avoids Landau's theorem. A width bound
`a`, degree gaps `O(x^θ)`, and trace bound `O(d^σ)` give the new width
`max(σ, a+θ−1)` by Lipschitz propagation and the absolute-convergence rate
theorem. Iterating removes the initial width for every `θ<1`.
`CollectiveDiophantineGeometry/TwoSidedGapIteration.lean` proves the exact
width law and its prime specialization. All four public theorems passed
the axiom audit with only `propext`, `Classical.choice`, and `Quot.sound`.
The rate theorem uses a Laplace transform, analytic continuation and residues.
The final direct Lean check passed; the programme umbrella imports the module.
Paper proof: [CDG-GAP](../3-formalized/cdg-two-sided-gap-iteration.md).

## Fixed-height mass boundary

For logarithmic prime weights, the geometric-comb mass tends to
`M(δ)=(1−e^(−2δ))/(1−e^(−2π))` along `x_N=e^(2πN+δ)`.
Every selected prime returns at height `1` with radian error at most `δ`.
Thus any required mass fraction below `M(δ)` fails to admit a growing
first-return lower bound. In particular, more than half the logarithmic
mass returns with error `1/2` radian at arbitrarily large cutoffs.

`FixedHeightPrimeMass.lean` proves the infinite-comb limit, its identification
with actual prime subsets, and these witnesses. This is classical phase-mass
calibration, not a new breadth estimate. TTPO's precise `MainConjecture` uses
`p^(−1/2)` weights and existentially chooses the missing-mass allowance;
that statement is not refuted. No transfer between weights is assumed.
The direct Lean check and six public-declaration axiom audits passed.
Paper proof: [CDG-MASS](../3-formalized/cdg-fixed-height-return-mass.md).

## Absolute modulus and heavy returns

For `P(t)=Σ a_i exp(itℓ_i)`, `a_i≥0`, `S=Σa_i`, a bounded integer
dilation satisfies `D(mt)≤2Q²(S−|P(t)|)+4π²S/Q²`, `1≤m≤Q`.
Given cosine precision `η>0` and missing-mass allowance `κ>0`, take
`Q=ceil(sqrt(8π²/(κη)))+1` and `c=κη/(4Q²)>0`.
Every absolute large value `|P(t)|>(1−c)S` yields a heavy return at `mt`.
On `[A,B]`, `A≥0`, its measure is at most `H_Q` times the heavy-return
measure on `[A,QB]`. All constants are independent of dimension and weights.

`AbsoluteValuesForceHeavyReturns.lean` proves the dilation bound, measure
transfer, and the exact dichotomy for `Σ_{p≤y}log p·p^(−it)` with `S=θ(y)`.
This supplies the modulus transfer; it does not estimate arithmetic returns.
Paper proof and audited declarations:
[CDG-MOD](../3-formalized/cdg-absolute-values-and-returns.md).

## Collective rank and near-relation counts

For `r` independent integer forms in `k` distinct prime logarithms, maximal-minor
elimination reduces the Baker input to `k−r+1` logarithms. At height `H`, the
explicit floor is
`exp(−B_{k−r+1}(y)(log((k−r+1)r!H^r)+2))/(r!H^(r−1))`.
Full rank has the stronger floor `log 2/(r!H^(r−1))`.

Below the rank-`r` floor, integer near relations in the height-`H` box span
at most `r−1` dimensions and number at most `(2H+1)^(r−1)`.
`CollectiveRankDepth.lean` proves the rank law, penultimate-rank two-logarithm
specialization, and actual near-relation count. The first-rank estimate
retains the existing scalar Baker bound; return-height counts remain open.
Paper proof and audited declarations:
[CDG-RANK](../3-formalized/cdg-collective-rank-depth.md).

## Open core

The corpus already has fixed-prime depth laws, bounded-height obstructions,
smooth-head moment estimates, and a positive-resonator finite-time Bohr
isometry. Repackaging those is not a new breadth estimate. No unconditional
growing-family return exclusion or RH producer has been proved here.

The existing comb estimate propagates prime precision to a smooth integer
with `k` factors at cost `k` times that precision. Its useful counting range
is past integer length comparable to the height. The unresolved collective
tool must control growing smooth supports below that range without losing
constant prime precision. This is an arithmetic counting problem, not a
missing wrapper around the existing moment estimates.

`README.md` gives the foundational draft. A return starts at `t≥1`; heaviness
must specify its weight and fraction. Exact prime-log relation lattices are
zero; successive minima concern approximation bodies in the integer lattice.
