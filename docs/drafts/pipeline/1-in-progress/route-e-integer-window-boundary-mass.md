# Route E: mass of incomplete integer-factor cells

- **ID:** E-INTEGER-WINDOW-MASS-001
- **Stage:** 1-in-progress
- **Target:** determine whether restricting a complete singleton histogram to the physical window can discard negligible mass.
- **Status:** paper argument below; Lean verification in progress.
- **Parent:** [integer aperture](route-e-integer-cube-aperture.md).

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

Formal milestones: comparable-corner bound; three-antichain partition and
cardinality bound; exact mixed-orientation resampling; quantitative tail
bound; transfer to the literal histogram marginal and growing schedule.
Only the earlier integer aperture leaf has passed Lean so far.
