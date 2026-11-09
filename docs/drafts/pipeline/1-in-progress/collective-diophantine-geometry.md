# Collective Diophantine Geometry of the Prime Logarithms

- **ID:** CDG
- **Stage:** 1-in-progress
- **Type:** RESEARCH PROGRAMME
- **Source:** `docs/reports/review-0911/obstacles-summary.md`, original §2.11,
  commit `718eee62deb23075e72f3bddae2c486b026e4211`.
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
specialization, and actual near-relation count. Scalar coordinate slicing
already gives that cardinal exponent. For rank at least two and height at
least one, its threshold is at least the collective threshold. The genuinely
collective conclusion is the bound on the
rational span; transferring only cardinality to smooth-box mean squares does
not use that extra information. The first-rank estimate retains the existing
scalar Baker bound; a stronger first-minimum estimate remains open.
Paper proof and audited declarations:
[CDG-RANK](../3-formalized/cdg-collective-rank-depth.md).
The exact scalar comparison and projection theorem are formalized in
[CDG-SLICE](../3-formalized/cdg-coordinate-slicing.md).
The closed simultaneous bound and published benchmark are in
[CDG-SIM](../3-formalized/cdg-simultaneous-logarithm-bounds.md).

## Collective auxiliary construction

The integral auxiliary retains `k` prime-frequency coordinates and only
`d=k−r` free jet directions. Its system has `XS^(d+1)` equations against
`(N+1)q^k` coefficients. The explicit parameter degree is
`(floor(d/r)+1)(k+1)+k`, at most `3k+2` when `r≥d`.
`CollectiveAuxiliaryConstruction.lean` constructs a nonzero bounded-height
integer kernel, exact initial jet vanishing, and a nonzero true value
before the full interpolation length. The free-direction analytic
extrapolation preserves the original coefficient box through the terminal
interpolation count.
Proof and formalization: [CDG-AUX](../3-formalized/cdg-collective-auxiliary.md).

## Simultaneous logarithm bound

`CollectiveLogarithmBound.lean` proves, for rank `r`, height `H≥1`,
and `W=ceil(Σ log p_j)+1`, that some original form has size at least

`exp(−(C′+1)(log(r!H^r)+2))/(r·r!H^(r−1))`.

`C′` is the explicit `collectiveLambdaExponent` of the collective
parameters. The integer system and terminal count use `q`; only analytic
majorants use `Q=kq`. Thus the rank-dependent root degree survives the
complete argument. Direct checks and the capstone's transitive axiom audit
passed. Proof: [CDG-SIM](../3-formalized/cdg-simultaneous-logarithm-bounds.md).

`ReciprocalRankBounds.lean` bounds `C′+1` by
`U^(100h(k+1))`, where `U=10⁴(W+1)(k+1)²`, `h=floor((k−r)/r)+1`.
The exponent degree times rank is at most `100k(k+1)` and is linear in
dimension at half rank. Below the resulting uniform floor, the entire
height-`H` approximation body spans at most `r−1` rational dimensions and
has at most `(2H+1)^(r−1)` integer points. The maximum-floor theorem retains
the earlier scalar and full-rank bounds. Direct verification and six
transitive axiom audits passed.
Proof: [CDG-EXP](../3-formalized/cdg-rank-sensitive-exponent.md).

## Bounded coordinate elimination

For integer forms of height `H≥1` and values below `ε`, every coordinate
intersection of their rational span has a rational basis of integer rows
with height at most `k!H^k` and values below `k!H^(k−1)ε`.
Cramer elimination preserves the full intersection rank. The theorem applies
to every real linear form; it supplies the height-controlled localization
needed for hereditary small-form rank bounds.
Proof and audited Lean declarations: [CDG-ELIM](../3-formalized/cdg-bounded-coordinate-elimination.md).

## Finite-time return counts

For `k` distinct primes, rank threshold `r`, and `N≥2`, put `H=N−1`
and `Δ=Δ_r(H)`. In every interval of length `T`, the measure of returns
to any target phase vector at chord or radian precision `1/(2N)` is at most

`(5π/2)·4^k·max(T/2,Δ⁻¹)/N^(k−r+1)`.

At `T≥2/Δ`, relative measure is at most `(5π/4)·4^k/N^(k−r+1)`.
The horizon is exactly `B H^(rC+r−1)`, with
`B=2r·r!·exp(C(log(r!)+2))` and the proved collective exponent `C`.
The shared small-form span bounds close smooth-number pairs; the Fejér
window theorem removes the far-frequency error. This supplies a formal
shrinking-precision counting tool; no improvement over published scalar
separation or constant-precision breadth is claimed.
Direct Lean verification and five transitive axiom audits passed.
Proof: [CDG-COUNT](../3-formalized/cdg-finite-time-rank-counts.md).

## Hereditary rank and weighted separation

Put `H′=k!H^k`, `K=k!H^(k−1)` and `δ=Δ_k(H′)/K`.
Below `δ`, every coordinate intersection of the small-form span has
dimension at most half its support size. A minimum-weight coordinate basis
and Hall matching then retain at least half of any nonnegative prime weight
on coordinates whose nonzero height-`H` forms have size at least `δ`.
This closes the hereditary localization and weighted selection mechanisms.
Direct Lean checks and four capstone axiom audits passed; both modules
are imported by the programme umbrella.
Proofs: [CDG-HERED](../3-formalized/cdg-hereditary-rank-bounds.md),
[CDG-WEIGHT](../3-formalized/cdg-weighted-coordinate-separation.md).

The comparison with quadratic scalar dimension degree applies only to the
earlier formal Fel'dman estimate. Published Matveev scalar bounds already
have linear degree and keep all coordinates at a stronger floor. These
formal tools do not claim an improvement on that benchmark. A weighted
return detector using only worst separation would therefore be insufficient
as the next contribution; it must control small-ratio distributions before
that horizon.

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
