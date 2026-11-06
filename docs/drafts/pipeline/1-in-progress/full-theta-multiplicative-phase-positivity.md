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

Test the positive frequency average with weight `cosh(ηb)`, `η<π/2`.
Schläfli inversion should replace `K_ib(2q)` by
`π exp(−2q cos η)`. Set `N=(cos η)⁻¹`. Prescribe phase `−1` on
every prime above `Y≈N^γ`, where `1/2<γ<1`, and average the small-prime
phases. The corpus largest-prime decomposition isolates the prospective
head mean, for `X<Y²` and product amplitude `A(k)`:

`Σ_(d²≤X) A(d²)−2Σ_(Y<p≤X, p prime) Σ_(pd²≤X) A(pd²)`.

The diagonal survives; every large-prime channel is negative. The
remaining product tail starts at `Y²` and should be exponentially
suppressed after frequency averaging. The prime block up to `N` alone
would supply the needed negative mass.

For fixed `0<a<1/2`, the expected diagonal scale is
`N^(9/2+a) log N`; the negative prime scale is `N^5/log N`.
If justified uniformly through all sums and integrals, this would
disprove independence of phase and radial frequency, forcing a producer
that retains their physical relation. The transform, asymptotics, phase
average and suppression estimates are not yet proved together.

Corpus anchors for this test: `besselFirstAtomTailDensity`,
`modifiedBesselKOrder_imaginary_re_integral`,
`strip_axis_eq_ofReal`, `integral_cosh_stripDensity`, and
`SteinhausModel`, and `sum_Icc_eq_smooth_add_largePrimeSigma`.
