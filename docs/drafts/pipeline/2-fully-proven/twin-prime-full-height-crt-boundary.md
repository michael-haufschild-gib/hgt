# The full-height CRT kernel is the shift itself

- **ID:** twin-prime-full-height-crt-boundary
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / BOUNDARY CLASSIFICATION
- **Source:** [balanced CRT estimate](twin-prime-balanced-crt-compensation.md).
- **Statement:** Above half the physical horizon, the CRT incidence kernel is exactly the gap-two shift matrix. Its odd unweighted block has an order-horizon positive discrepancy from the period mean.

## Exact classification

Let `N_X(d,e)=#{n:2<=n<=X,d|n,e|n+2}`. If
`X/2+2<=d,e<=X`, then

`N_X(d,e) = 1` when `e=d+2`, and `0` otherwise.

Indeed a positive multiple of `d` below `X<2d` must be `d` itself.
Then `e|(d+2)` and `d+2<=X+2<2e`, so its positive cofactor is also
one. Conversely `n=d` supplies the unique incidence when `e=d+2`.
The lower bounds imply `d>=2`, including all small-horizon edge cases
when the carrier is empty.

Thus the bilinear sum with any two boundary coefficient sequences
reduces exactly to their shifted correlation on this carrier. No
inverse-residue averaging remains at this endpoint.

## Quantitative positive boundary

Take `T>=12`, `X=8T+2`, and the `2T` odd divisors

`d_i=4T+3+2i`, `0<=i<2T`.

They lie in the classified carrier. Exactly `2T-1` pairs satisfy
`d_j=d_i+2`. For odd pairs the CRT compatibility condition is
coprimality. Define

`Delta_T = sum_(0<=i,j<2T)
 [N_X(d_i,d_j) - (8T+1) [gcd(d_i,d_j)=1]/(d_i d_j)]`.

Split the reciprocal sum at `i=T`. The first `T` denominators are
at least `4T` and the second `T` at least `6T`; therefore

`sum_i 1/d_i <= 1/4+1/6 = 5/12`.

Discarding the coprimality restriction only increases the nonnegative
period mean, so

`Delta_T >= 2T-1-(8T+1)(5/12)^2
          = (88T-169)/144 >= T/2`.

Every inequality is elementary and independent of the distribution
of primes or Möbius signs.

Moreover `T/2 >= (8T+2)/20` for `T>=1`. Thus the normalized discrepancy
is at least `1/20` at every horizon in this family. This directly rules
out an error tending to zero after normalization by the horizon.

## Research consequence and positive survivor

This rules out extending a uniform product-weight power-saving CRT
estimate to full divisor height, even for the constant positive
weights on this explicit odd block. The strongest survivor is the
exact shift-matrix classification, not just failure of a bound.

For the actual Möbius or compensated coefficients, the same
classification retains their actual shifted scalar correlation.
It does not prove or disprove cancellation in that correlation.
The boundary shows why estimates which work for every bounded
product weight must give way to source-specific arithmetic there.

**Positive second pass:** the
[cofactor-compensation identity](twin-prime-compensated-damping-coefficients.md)
uses the exact Möbius zero sum to transfer the weight to the
complementary divisor: `tau_epsilon(n)/epsilon` is the divisor
convolution of `mu(d)d^(-epsilon)` with
`(1-m^(-epsilon))/epsilon`. The latter vanishes at `m=1`.
Consequently the unit-cofactor endpoint disappears in that full-source
representation. This does not make the uncorrected block small; it
shows why its compensation must be retained across the decomposition.
The next arithmetic obligation concerns growing nonunit cofactors,
not a forced estimate for the isolated unit block.

This also marks the limit of the four-long-variable operator route:
cofactors equal to one are outside its stated range. No extension
across that endpoint is silently assumed.

## Gates

- [x] Exact kernel and complete paper proof.
- [x] Positive survivor and quantitative boundary identified.
- [ ] Corpus dependency audit and unconditional Lean certificate.
- [ ] Leaf and foundational axiom audits; umbrella integration.

## Log

- 2026-10-23 — Located the exact full-height obstruction after paying
  the balanced block on paper. Twin-prime infinitude remains unproved.
