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

The geometric-chain cancellation identity proves the relevant phase sign
for support `1,q,q²,…`, after the literal integral bridge is completed.
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
