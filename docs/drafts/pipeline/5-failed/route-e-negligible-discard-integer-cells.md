# Route E: small-discard repair of complete integer-factor cells

- **ID:** E-INTEGER-WINDOW-MASS-001
- **Stage:** 5-failed, small-discard repair; positive mass theorem formalized
- **Target:** determine whether restricting a complete singleton histogram to the physical window can discard negligible mass.
- **Status:** full mixed-orientation mass limit and literal all-slot admission fraction pass scratch Lean and final targeted build.
- **Parent:** [integer aperture](route-e-complete-integer-factor-cells.md).

## Conjecture, first proof, and pivot

The integer aperture law excludes a complete cell with three changing factors,
but one missing extreme corner need not have appreciable probability. A mass
estimate is necessary before excluding a small-boundary repair.

Orient each nonconstant integer factor by its lower and upper value. For a
family of corner subsets whose products lie in `[L,L+W]`, with `L>=0` and
`W^3<27*L^2`, two comparable admitted subsets can differ in at most two
coordinates. Indeed their two products are the minimum and maximum corners
of the intermediate cube; the already proved aperture law applies to it.
Thus partitioning admitted subsets by cardinality modulo three gives three
antichains. Sperner bounds their total cardinality by
`3*choose(d,floor(d/2))`, where `d` counts nonconstant coordinates.
The same argument applies after freezing any coordinates.

For the actual singleton histogram, a fixed slot has independent Bernoulli
coordinates with parameter `p=1/(M+2)`. Sorting lower/upper values changes
some parameters to `1-p`; an identical-bias LYM argument alone is therefore
insufficient. The replacement is exact fair resampling: each coordinate is
frozen at its more probable value with probability `1-2*p`, otherwise drawn
uniformly from its two values. Conditional on the resampled coordinate set
of size `K`, the accepted fraction is at most
`min(1,3*choose(K,floor(K/2))/2^K)`.

The resampled count has mean `2*d*p` and variance at most `2*d*p`.
Chebyshev gives `P(K<d*p)<=2/(d*p)`. The corpus's Wallis asymptotic gives
`choose(K,floor(K/2))/2^K=O(K^(-1/2))`. Hence the admitted slot mass tends
to zero whenever `d*p` tends to infinity. The probability that every slot
is admitted is no larger. This would exclude a negligible-discard repair
of this class of complete integer-factor singleton cells at growing density.

## Scope and unpaid work

This is a claim about unsigned uniform histogram mass. It is not a signed
covariance estimate. The count `d` must be the number of nonconstant physical
integer factors; identifying it with any abstract sign-component count is
a separate obligation. Independently constructed product-conditioned cells
need not be small modifications of a complete cell and remain candidates.

Closed milestones: comparable-corner bound; three-antichain partition,
cardinality and Lubell bounds; exact orientation conditioning; varying-bias
concentration; literal histogram marginal and all-slot admission transfer.
The simpler orientation argument below replaces the first resampling plan.
The earlier integer aperture leaf has passed its final targeted build.
`formal/GaloisForLFunctions/RHTower/RouteEIntegerWindowMass.lean` now proves
the comparable-corner law, three-antichain cardinality bound, Lubell bound
`sum_A choose(d,|s|)^(-1)<=3`, and the weighted bound by three times the
square root of the squared Bernstein-row norm. It also proves the varying
dimension/bias concentration limit and its application to the actual
growing marker window, with an arbitrary spectator of size at least one.
Scratch `lake env lean /tmp/route_e_integer_window_mass.lean` and targeted
`lake build GaloisForLFunctions.RHTower.RouteEIntegerWindowMass` passed.
The leaf is wired into `RHTower.lean`.

`formal/GaloisForLFunctions/RHTower/RouteEHistogramWindowMass.lean` now
transfers this limit to actual uniform histogram counts. It proves exact
subset and family masses from the original joint slot marginal, identifies
the literal slot-receiver event, and proves its probability tends to zero
for increasing integer components when `d*p*(1-p)->infinity`, with
`p=1/(m+1)`. Scratch `lake env lean /tmp/route_e_histogram_window_mass.lean`
and targeted `lake build GaloisForLFunctions.RHTower.RouteEHistogramWindowMass`
passed. This leaf is also wired into `RHTower.lean`.

After both finished mass modules, `scripts/formal_tools.py index` completed
and `scripts/formal_tools.py lint --check-generated` passed with existing
large-file warnings. No umbrella build was run.

## Simpler orientation reduction

At least half of the nonconstant components have the same lower/upper
orientation relative to the rare singleton value. Freeze all other
components. Within the selected group the coordinates are identically
distributed with parameter `p` or `1-p`; the remaining positive integer
product is a spectator. Dividing both window endpoints by that spectator
preserves the aperture inequality. Apply LYM separately to the three
antichains, then average over the frozen coordinates.

This gives a route to the same vanishing-mass result without a mixed-bias
Sperner theorem. The exact Bernstein-row identity in the corpus also gives
an alternative to a uniform Stirling estimate: the square of any binomial
atom is at most the sum of all squared atoms, and that row square equals
a normalized integral of
`(1-4*p*(1-p)*sin(t)^2)^d`. Dominated convergence makes this integral
vanish whenever `d*p*(1-p)` tends to infinity. The required varying-parameter
limit and the literal increasing-component histogram transfer are now
formalized. Averaging over frozen opposite-orientation components and the
all-slot histogram endpoint now also pass scratch Lean.

## Direct varying-parameter proof

For `0<=u<=1`, induction gives `(1-u)^d*(1+d*u)<=1`:
the next factor satisfies
`(1-u)*(1+(d+1)*u)=1+d*u-(d+1)*u^2`.
Thus `(1-u)^d<=(1+d*u)^(-1)`. With
`u=4*p*(1-p)*sin(t)^2`, the base is nonnegative because it equals
`(2*p-1)^2*sin(t)^2+cos(t)^2`, and it is at most one.
For `0<t<=pi/2`, its reciprocal bound tends to zero when
`d*p*(1-p)->infinity`. The constant one dominates every integrand on the
finite quarter interval. Dominated convergence and the corpus's exact
quarter-circle Bernstein-row identity therefore prove the needed varying
binomial concentration without a fixed-parameter Stirling substitution.

## Closed mixed-orientation proof

For `d` nonconstant components and common singleton probability `p`, let
`k` be the larger of the two orientation-group sizes. Then `2*k>=d`.
The finite target is an upper bound by
`3*sqrt(bernsteinRowSquare(p',1-p',k))`, where `p'=p` or `p'=1-p`
according to the chosen group. Its variance is unchanged:
`p'*(1-p')=p*(1-p)`. Conditional on every assignment outside the group,
the selected factors satisfy the existing spectator mass bound. The
outside product weights are nonnegative and sum to one, so averaging
preserves the same ceiling. Since `k*p*(1-p)>=d*p*(1-p)/2`, the ceiling
vanishes at the required growing density.

`RouteEHistogramMixedOrientationMass` proves this argument by the exact
`Equiv.piEquivPiSubtypeProd` splitting and global bit complementation. Its
finite bound chooses orientation and group size independently of the
window. The varying-variance limit transfers to the literal histogram
event, and the all-slot event is a subset of the slot-zero event. Scratch
`lake env lean /tmp/route_e_mixed_orientation_mass.lean` passes without
diagnostics. The finished leaf is wired into `RHTower.lean`; its final
targeted `lake build GaloisForLFunctions.RHTower.RouteEHistogramMixedOrientationMass`
passed without leaf diagnostics. Constant-valued components must be excluded from `d`;
identifying this count with an abstract sign-component density cannot be
assumed.

## Broad-paper audit

Broad searches for thinning, localization, fluctuation and transport mostly
returned unrelated material or dates outside the requested range. Two
August 2026 primary texts were inspected:

- [SinkSLOT](https://arxiv.org/html/2608.28262v1) constructs a sparse
  non-independent reference coupling before Gibbs scaling. Its convergence
  argument requires a feasible support with the prescribed marginals;
  connected support gives a spectral gap but no cutoff-uniform gap here.
  This suggests examining source-defined sparse couplings, but does not
  supply the missing arithmetic incidence or Möbius cancellation.
- [Transport-Matched Penalties](https://arxiv.org/html/2608.28022v1) derives
  boundary jump terms matched to the original transport discretization.
  Its coercivity depends on that source form and whole-boundary trace
  estimates. No counterpart has been established for the incomplete
  integer-product boundary, so no theorem is transferred.

Corpus deep and method searches were partial; broad rephrasing recovered
LYM, exact Bernstein-row diagonalization, Wallis bounds and a dominated
convergence pattern. No numerical experiments or resampling computations
were used.

A later broad search for excursion and lattice found
[Remote Flux Refocuses Nonadiabatic Excursions](https://arxiv.org/html/2609.07198v1).
Its exact projected dynamics retain departure, complementary propagation,
and return in a memory kernel; its reported return improvements are numerical.
No source-preserving control parameter or bounded initial Hilbert norm has
been identified for the literal Möbius prefixes. The paper therefore gives
no covariance estimate here. The abstract of
[Quantum Simulation of QCD in Axial Gauge](https://arxiv.org/abs/2608.16783)
concerns analytic constraint elimination and quantum resource bounds, with
no identified transfer to integer-product window conditioning.

## New source test after the mass closure

Small-discard repair fails in the stated class: even the maximal admitted
subset has relative mass tending to zero. This does not exclude direct
conditioning on that rare subset. Common slot permutations preserve its
support and one-component slot marginals, but independent component
permutations need not preserve the window. Thus the complete-cell product
parity formula cannot be reused after conditioning. No new receiver is
needed to record that distinction.

The next arithmetic test retains common integer divisors of distinct slot
receivers. A component active in exactly one slot contributes its inactive
integer factor to every pair avoiding that slot. Multiplying the resulting
difference-divisibility inequalities should bound the inactive product in
terms of aperture width and the number of distinct receivers. The separate
[common-divisor card](../1-in-progress/route-e-conditioned-slot-divisors.md) records the
precise paper target; this is not yet a Lean result.

A broad September search also found
[Countable IET Models and Defect Sets](https://arxiv.org/html/2609.01670v1).
Its direct-image defect identity retains mass gained across branch images;
preimage invariance alone does not remove that defect. The source here is
finite and atomic, so its nonatomic interval-model theorem does not apply.
The useful audit question is whether the actual conditioning preserves
the original transported weights; no arithmetic cancellation bound follows.

## Positive survivor and retirement boundary

The strongest proved survivor is the finite orientation-selected ceiling
`mass <= 3*sqrt(bernsteinRowSquare(q,1-q,k))`, with `2*k>=d` and
`q*(1-q)=p*(1-p)`, followed by vanishing actual all-slot admission mass.
It is valid for either orientation of every nonconstant positive integer
factor and for the original uniform singleton histogram. All proofs are
closed in the three finished mass leaves. Only the proposal to retain
most of a complete cell is retired; a rare conditioned support is not
excluded by this theorem.

After the mixed-orientation leaf, `scripts/formal_tools.py index` completed
and `scripts/formal_tools.py lint --check-generated` passed. Existing
large-file warnings remain. No umbrella build was run.
