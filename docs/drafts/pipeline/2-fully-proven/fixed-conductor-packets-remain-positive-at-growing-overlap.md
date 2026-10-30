# Fixed conductor packets at growing overlap

- **ID:** fixed-conductor-packets-remain-positive-at-growing-overlap
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean audit pending)
- **Source:** quantitative residue primes; actual source decomposition;
  completed-shell Fourier positivity; arithmetic Hodge Gram bounds.

## Statement

Let `φ` be the explicit tilted unit spline, `M=∫φ²`, and let `T>0` be
`tiltedSplineTailConstant`. For every finite set `S` of positive conductors
and every `0≤α<1/48`, one horizon gives, simultaneously for
`1≤c≤(log N)^α` and all real coefficients `a_m`,

`completeWeilEnergy(φ,c,N,Σ_(m∈S) a_m v_(m,N))
 ≥ T/(M c⁷) Σ_(m∈S) a_m²`.

Here `v_(m,N)` is the actual logarithmically normalized Ramanujan vector.
Thus the entire fixed conductor span has positive actual energy at
prescribed unbounded overlap. The conductor set stays fixed; full-matrix
positivity and RH remain open.
The same conclusion holds throughout `1≤c≤(log log N)^A` for every
fixed `A≥0`.

## Proof

Write `L=log N` and `δ=2T/M`. Fourier-tail positivity gives
`E_m(c)≥δ/c⁷`; the global shell bound and exact self/pole scaling give
`|E_m(c)|≤C_m c²`.

Quantitative fixed-progression prime sums, including nonunit classes and
all prime powers, yield every inverse-logarithmic residue Mertens rate.
Abel transport gives shell error `O(c³/(log Y)²)` when `X≥2cY`;
globally support and the Chebyshev bound give `O(c²)`. Split the harmonic
row norm at `X=2c exp(√L)` to obtain squared normalized error
`O(c⁶/√L)`.

For `N≥4(e+3)²c²`, literal upward offsets lie in `B=ceil(ec)`.
Kernel linearization costs `O(c⁴(B+1)⁶/√L)` in squared normalized
harmonic norm; moving the exact prime cutoff costs `O((B+1)⁶/√L)`.
Combining these with the reciprocal shell estimate gives actual upward
squared residual `O(c¹⁰/√L)`. Exact near-gamma/downward cancellation and
small-width geometry give `O(c⁵/L)`. Pole and separated-cross errors
cost `O(c⁴/L)`, center error `O(c²/L)`, self error `O(c²/N²)`.
The existing arithmetic Hodge budget gives prime-ratio error `O(1/L)`.
The exact eight-term decomposition therefore gives, for each fixed `m`,

`||W_(c,N)v_(m,N)−E_m(c)v_(m,N)||²≤K_m c¹⁰/√L`.

Consequently `c⁷` times its norm tends uniformly to zero on the stated
range: its square is at most `K_m L^(24α−1/2)`, which tends to zero
because `α<1/48`. The horizon condition holds uniformly since
`L^(2α)/N→0`. Every fixed power of `log log N` is smaller than every
positive power of `log N`, giving the second range.

The Hodge Gram bound gives
`|<v_m,v_l>−1_(m=l)|≤(1+2ml)/L`, and each vector norm is eventually
at most two. Pair the actual residual with `v_l` and use
`|E_m(c)|≤C_m c²`. Then

`c⁷ |<Wv_m,v_l>−1_(m=l)E_m(c)|→0`

uniformly in overlap; the Gram contribution is at most `O(L^(9α−1))`,
which tends to zero under the same restriction.
For `d=|S|`, choose all mixed-entry errors at most
`δ/[2(d+1)c⁷]`. Finite Cauchy–Schwarz bounds the packet energy error
by `d` times this quantity times `Σa_m²`, hence by
`δ/(2c⁷)Σa_m²`. Subtract from the diagonal floor `δ/c⁷`.

## Lean status

Supporting source, geometry, kernel and cutoff lemmas have direct audits.
Remaining support modules and the complete packet formalization are
written and under check. No accepted contribution until the capstone and
its transitive axiom audit pass. All supporting lemmas belong to this
single contribution.
