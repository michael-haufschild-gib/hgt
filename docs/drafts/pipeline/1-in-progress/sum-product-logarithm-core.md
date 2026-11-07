# Sum-product arithmetic at a single height

- **ID:** SPL-core
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [Obstacles summary §§2.6, 2.9](../../../reports/review-0711/obstacles-summary.md)
- **Statement:** Produce arithmetic control of logarithmic phases beyond the
  diagonal and polynomial-phase ceilings, with no quadratic-form sign input.

## First quantitative target

Find fixed `K>1`, `c>0`, `T₀` such that, for every `t≥T₀` and
`y=(log t)^{2K}`,

`Σ_{p≤y} p^{-1/2}(1−cos(t log p)) ≥ c Σ_{p≤y} p^{-1/2}`.

This is the all-height proportional-saving question from §2.6. An estimate
on a density-one set of heights does not meet it. A prime-alignment hypothesis
is not an input to assume. No theorem in the new programme proves this estimate.

## Arithmetic information still missing

The translated-product reconstruction theorems bound the occupation of each
**real** logarithmic cell. They do not control the distribution between distinct
winding cells. In particular, inverse-square separation at large height is
consistent with every integer of a fixed interval returning to a small arc.

A useful further estimate must connect integer translation, multiplication,
and the actual prime weights, rather than only count the signatures of a
finite set. It must also avoid a loss proportional to word length that turns
constant prime precision into vanishing precision.

The [balanced smooth × prime count](../3-formalized/logarithm-smooth-prime-determinant-gcd.md)
now bounds fine energy by its exact diagonal plus disjoint gcd-class costs
for differences up to `floor(4X²/T)`. The
[cumulative incidence bound](../3-formalized/logarithm-cumulative-collision-gcd-cancellation.md)
cancels the gcd loss, giving `E≤#A #P+2 floor(4X²/T)#A²`, with exact
diagonal energy when `T>4X²`. Prime-density savings at random scale and
control of winding cells are still missing.
The [coprime-density refinement](../3-formalized/smooth-prime-coprime-difference-density.md)
retains the reduced-row prime factors: each row pair costs at most
`g #{1≤v≤H/g:gcd(v,(m/g)(n/g))=1}`, with a totient bound for every positive
divisor of the reduced product. This improves the finite arithmetic envelope
without proving the random-scale prime-density law.
The [rectangular census](../3-formalized/rectangular-smooth-rough-arithmetic-moments.md)
gives `(Z/X+1)floor(2XZδ)` per positive log fibre for rows in `(X,2X]`
and columns in `[1,Z]`. In broader RH work, TAPO transfers these counts through
a triangular Fourier majorant to actual weighted mean squares, higher prime-tail
moments, and large-tail bounds. This analytic transfer uses positivity and is
kept outside the restricted arithmetic programme.
The [primitive-step extension](../3-formalized/unrestricted-smooth-head-arithmetic-moments.md)
removes the dyadic restriction on rows. Each pair retains the cost
`Z(2Z+m/gcd(m,n)+n/gcd(m,n))`; weighted moments on arbitrary finite smooth
heads pay its coefficient-weighted sum, bounded by `2Z²R₁²+2ZR₁M₁`.
The [normalized moment bound](../3-formalized/primitive-head-normalized-tail-moments.md)
uses reduced ratio height `H=max(1,max m/gcd(m,n))`, invariant under common
dilation. Actual head mass is at least `(2T−52H)R₂`; at `T≥52H` and `R₂>0`,
normalized prime-tail moments retain the primitive error divided by `T R₂`.
The same invariant gives `C(A,r,Z)≤2Z(Z+H)R₁²`.

## Independent finite-zero target

Decide whether the exact integer count and its carries contradict the finite
oscillation forced by a nonempty finite right-zero layer. The proportional
saving above concerns growing heights and does not itself exclude a fixed
exceptional zero. Linear floor readings and exact ledgers are already blind
to these modes.

## Full scope still required

* Additive energy of phase level sets past the diagonal.
* Exponential-sum savings when Taylor degree exceeds `(log length)²`.
* A carry argument deciding the finite-oscillation question.
* Effective return bounds in both directions, with cutoff/height dependence explicit.
* Count-distance geometry above the Beurling isolation gap, keeping nonnegative
  generator multiplicities and finite exceptional zero support explicit.

The [discrete two-scale window](../3-formalized/logarithm-discrete-half-turn-separation.md)
now bounds an attained half-turn index above and below at every precision.
It supplies an initial-index exclusion for `log 3/log 4`; the many-prime
cutoff/height problem remains open.

[Bounded-count rigidity](../3-formalized/logarithm-bounded-count-rigidity.md) isolates a concrete
advance on this last question: rational-prime rigidity extends from vanishing
count error to `o(log n)` error at slope one. Collision amplification in the
free label monoid and consecutive-integer cancellation give the
[logarithmic floor](../3-formalized/logarithm-count-distance-floor.md). This does not determine
the smallest distance carrying an exceptional zero.

The [positive-generator model](../3-formalized/logarithm-positive-generator-near-count-model.md)
has nonclassical labels and slope-one count error `O((log x)²)`, with an
explicit bound. It brackets the nonclassical count-distance problem between
logarithmic and quadratic logarithmic scales. Its finite Euler modification
does not supply an exceptional right zero.
Its [carry recurrence](../3-formalized/logarithm-positive-model-carry-recurrence.md)
gives an exact ternary-digit formula under dyadic dilation and signed
logarithmic deficits. These are quantitative statements about the actual
model count; they do not settle the finite-right-zero target.
The [first count average](../3-formalized/logarithm-positive-model-averaged-deficit.md)
has a deficit of exact order `x log x`, with explicit two-sided bounds.
Its [Euler continuation](../3-formalized/logarithm-positive-model-euler-continuation.md)
is identified from the actual series and preserves zeta’s complete
right-half-plane zero divisor and residue one.
Pointwise optimality and exceptional-zero distance remain open. The
[exact averaged coefficient](../3-formalized/logarithm-positive-model-exact-average.md)
is `1/(4 log 3)`, formalized for the actual integral count.
[Effective profile averaging](../3-formalized/logarithm-effective-profile-average.md)
now gives uniform error `O(log log n/log n)` and actual integral-count
coefficient error `O(log log log x/log log x)`, with explicit constants and
cutoffs. The [proved two-prime Baker transfer](../3-formalized/logarithm-polynomial-return-profile-rate.md) further supplies polynomial
half-turn returns and a fixed positive exponent `η`: uniform profile error
`O(n^(−η))` and actual coefficient error `O((log x)^(−η))`.
These averaged rates do not close the pointwise distance gap.

Finite-field calibration must retain the precise odd-degree hyperelliptic
scope of existing Stepanov and descent results over finite fields of odd
characteristic. General curves remain beyond that scope. Any power-saving parity output must include
its zero-free-strip consequence. None of these requirements is discharged
by exact shifted-product reconstruction alone.
