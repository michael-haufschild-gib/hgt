# Multiplicative phase positivity of the full aperture spectrum

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ6
- **Statement:** For every completely multiplicative `χ` with `|χ(n)|=1` for `n≥1`, every `0<a<1/2` and real `b`,
  `Σ_(n,m≥1) Re(χ(n) conjugate(χ(m))) B_nm(a,b) ≥ 0`,
  where `B_nm=∫_(r>0) w_a(r) thetaPairCenterTailAmplitude n m r b dr`.

The corpus pair-amplitude bound makes this series absolutely convergent.
The physical choice `χ(n)=exp(ib log n)` recovers the actual aperture
spectrum, so the conjecture would settle the full signed inequality.
The radial frequency and the multiplicative phase are independent in the
conjecture; this strengthening requires its own proof or counterexample.

The [geometric-chain spectrum theorem](../3-formalized/geometric-theta-aperture-spectrum.md)
proves the relevant phase sign for support `1,q,q²,…`, including the
literal integral bridge and absolute pair summability.
For general support, grouping ratios by coprime `n,m` gives the coefficient
`Σ_(d≥1) B_(dn,dm)(a,b)` on the prime torus. The first target is the
interaction of two independent prime chains, with every diagonal counted
once. Positivity of separate one-prime marginals is insufficient.

Corpus anchors: `thetaPairCenterTailSpectrum_eq`,
`thetaPairApertureSpectrum_eq_shifted`,
`thetaFullApertureTail_remainder_le`, `primeTorus_kronecker_dense`,
and the geometric-phase convex cancellation theorem.
No positive joint measure or full-source sign is presently established.

## Candidate producer: distinct-prime second differences

Put `A(t)=exp(−t/2)∫_(s>0) w_a((s−t)₊)F_b(s) ds` and
`E_h A(t)=A(t+h)`. Test the stronger statement

`[Π_(p∈P)(1−E_(log p))²] A(log m) ≥ 0`

for every finite set of distinct primes `P` and every integer `m≥1`.
The one-prime case follows from the damped convex payment. The proposed
bridge is a multivariate Fejér expansion on finite rectangular sets of
prime exponents, followed by the proved absolute pair remainder.
Both the mixed-difference sign and this multivariate bridge require proof.
Repeated occurrences of the same prime are not included in the conjecture.

The [two-prime center obstruction](../3-formalized/two-prime-center-cancellation-boundary.md)
rules out proving the mixed-difference sign before radial integration:
the two actual shifts `log 2`, `log 3` already give a negative clipped
weight at center `log 6` for small positive apertures. The integrated
mixed-difference conjecture remains open.

## Candidate obstruction to independent phases

The [positive frequency-average theorem](../3-formalized/bessel-cosh-frequency-average.md)
replaces `K_ib(2q)` by `π exp(−2q cos η)` under weight `cosh(ηb)`,
`0≤η<π/2`, including absolute convergence and the actual weighted Bessel
tails. Set `N=(cos η)⁻¹`. Prescribe phase `−1` on
every prime above `Y≈N^γ`, where `1/2<γ<1`, and average the small-prime
phases. The [frozen-prime finite-head theorem](../3-formalized/frozen-prime-divisor-head.md)
proves the exact mean, for `X<Y²` and arbitrary product amplitude `A(k)`:

`Σ_(d²≤X) A(d²)−2Σ_(Y<p≤X, p prime) Σ_(pd²≤X) A(pd²)`.

The diagonal survives; every large-prime channel has coefficient `−2`.
The [product-tail theorem](../3-formalized/product-exponential-tail.md) proves
`Σ_(nm≥L)exp(−qnm)≤64q^(−2)exp(−qL/2)` for `0<q≤4`, with absolute
summability. Applying this bound to the signed infinite spectrum still
requires the frequency and aperture interchanges. The prime block up to
`N` alone is the proposed source of negative mass.

For fixed `0<a<1/2`, the expected diagonal scale is
`N^(9/2+a) log N`; the negative prime scale is `N^5/log N`.
The [radial square identity](../3-formalized/exponential-tail-square-profile.md)
and [exponential aperture bounds](../3-formalized/theta-exponential-aperture-bounds.md)
are formalized, including absolute center integrability and upper and lower
bounds for the averaged radial profile.

If justified uniformly through all sums and integrals, the scale comparison would
disprove independence of phase and radial frequency, forcing a producer
that retains their physical relation. The finite phase mean is proved.
Prime-mass asymptotics, infinite sum/integral interchanges, and the connection
to the full signed spectrum remain unproved.

Corpus anchors for this test: `besselFirstAtomTailDensity`,
`modifiedBesselKOrder_imaginary_re_integral`,
`strip_axis_eq_ofReal`, `integral_cosh_stripDensity`, and
`SteinhausModel`, and `sum_Icc_eq_smooth_add_largePrimeSigma`.
