# Gcd classes of smooth × prime near-collisions

- **ID:** SPL-smooth-prime-determinant-gcd
- **Stage:** 1-in-progress
- **Type:** CANDIDATE THEOREM
- **Question:** Which arithmetic restrictions survive on a nonzero shifted-product fibre?

Let `m,m'` have only prime factors at most `y`, and let primes `p,p'>y`.
If `mp+h=m'p'`, then

`gcd(m,h)=gcd(m',h)=gcd(m,m')`.

Thus, for each nonzero difference `h`, contributing smooth rows belong to
the same exact class `d=gcd(m,h)`. This is stronger than the unrestricted
integer-fibre condition `gcd(m,m')|h`: the classes are disjoint, and the
column coprimality is an arithmetic consequence of smoothness and roughness.

For rows and columns in `(X,2X]`, let `A_d(h)` contain the smooth rows `m`
with `gcd(m,h)=d`. The actual ordered collision count satisfies

`C_{X,y}(h) ≤ Σ_{d|h} d |A_d(h)|²` for `h>0`.

The proof uses `gcd(m,h)=gcd(m,m'p')` and `gcd(m,p')=1`, then
interchanges the rows. Every nonempty fibre has both row gcds equal to
`d=gcd(m,m')`. The existing balanced-integer fibre bound gives at most `d`
column pairs. Summing within the disjoint gcd classes gives the bound.
The corpus's unrestricted divisor-mass bound uses all rows divisible by
`d`, with overlapping classes; smoothness and prime columns produce the
additional exact-class restriction here.

For logarithmic width `δ≥0`, let `E⁺(δ)` count the positive orientation
of off-diagonal collisions: `mp<m'p'` and `log(m'p')−log(mp)≤δ`.
Then

`E⁺(δ) ≤ Σ_{1≤h≤ceil(4X²δ)} Σ_{d|h} d |A_d(h)|²`.

Indeed `b−a≤b(log b−log a)≤4X²δ` for the two products `a<b`.
Their unique positive difference lies in the indicated range. The bound
therefore retains each difference's exact gcd classes at logarithmic
resolution; it does not replace the missing prime-pair asymptotic.

The complete ordered logarithmic energy is exactly
`|A||P|+2E⁺(δ)`, where `A` is the smooth row set and `P` the prime column
set. Smooth/rough product uniqueness gives the diagonal; swapping the two
products exchanges the positive and negative orientations. Thus the same
bound, doubled and added to the exact diagonal, controls the full energy.

Lean verification remains open. No prime-pair
asymptotic, random-energy law, or exponential-sum saving is claimed.
