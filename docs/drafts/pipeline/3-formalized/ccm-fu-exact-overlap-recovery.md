# CCM-FU: recover actual mergers beyond the geometric certificate

- **Stage:** 3-formalized
- **Type:** [BRIDGE], direct source comparison
- **Goal:** Complete signed Abel bound and RH remain open.
- **Parent:** [first-prime certificate obstruction](../5-failed/ccm-fu-universal-first-prime-certificate.md).

## Closed source theorem

At M=12p, every sufficiently large prime p has **every** available second
prime q satisfy `Q_{p,q}<=B=Q_empty`. The geometric first-prime certificate
fails in this same family. Thus these are actual states where the geometric
allowance rejects the entire state although all next energies remain below
the original diagonal. Every four-cofactor block is retained in the proof.

The source-level theorem is stronger: for all sufficiently large positive
integers p, every positive second dilation q and every positive cofactor r,
the four original unsigned channels at r,pr,qr,pqr satisfy

`(K_r-K_pr-K_qr+K_pqr)^2 <= K_r^2+K_pr^2+K_qr^2+K_pqr^2` at M=12p.

The same threshold works for all q and r. Primality enters only when the
full prime-label decomposition transfers this comparison to actual energy.

## Global ceiling from square endpoints

The unconditional estimate `K_d(M)<=3sqrt(M)/5` holds at every cutoff and
dilation, including all clipped endpoints. For fixed integer s, the smooth
profile is

`f_s(N)=log(N!)-(2N+1)H_s+s^2+s+2gamma*N`.

Its increments `log(N+1)-2H_s+2gamma` increase. A sequence with increasing
increments lies below the larger endpoint value on every integer interval.
On the interval from s^2 to (s+1)^2-1, this profile is the actual smooth
remainder. At the next square t^2, its jump is

`1/t-2*(H_t-log(t)-gamma)>=0`.

The harmonic half-bound proves that sign. Thus the entire interval is
controlled by the two adjacent square values. Stirling's global ceiling
and the harmonic lower twelfth-square correction bound the value at s^2 by

`7/6-gamma-1/(2s)+1/(12s^2)<3/5` for s>=1.

The analytic bound `gamma>=0.5768` and the zero-cutoff identity cover the
remaining cases. Centered time cancellation and exact clipped homothety
transfer the smooth ceiling to every unsigned K_d. This replaces the
previous coefficient7 by3/5 without an asymptotic threshold.

## Complete four-cofactor comparison

For the quotient-twelve child, analytic endpoint estimates give
`K_d(12)<=0.104sqrt(12)` for all d>0. The exact mean gives a parent floor
`K_r(12p)>=0.09sqrt(12p)` uniformly over r<=12 once p is large.
For q>12 the joint child vanishes. The bounds b<=0.104sqrt(M),
c<=0.6sqrt(M), a>=0.09sqrt(M) imply `bc<=a(b+c)`, because
`0.104*0.6<0.09*(0.104+0.6)`.

The endpoint bounds use `K_1(11)<=0.18`, `D(11)<=1.22` and exact successor
transport for d=1. For d>=2 the quotient is at most6. The first five
endpoint bounds, `D(4)<=0`, `D(5)<=0.56`, and the sixth successor supply
the same0.104 ceiling through exact clipped interpolation. All logarithm
and square-root bounds are analytic.

The parent floor uses `c=log(2*pi)/2-gamma-1/4>=0.091`, proved from
`pi>3.14`, the established log2/log5 and Gamma bounds, and
`log(625/628)<=-3/628`. Apply the uniform mean error with epsilon1/2000
to every cofactor scale d<=144. One threshold for p covers all these scales.

For q<=12, the two large-parent channels approach the same coefficient
uniformly on these finitely bounded cofactor scales. Their difference can
be made at most0.001sqrt(M), while the difference of the two nonnegative
small-child profiles is at most0.104sqrt(M). Their complete alternating
square is then paid by the two parent squares alone. Cofactors r>12 have
both p-children zero and contract directly.

Both parent channels are at least0.09sqrt(M), so their squared sum alone
dominates the alternating square bounded by `(0.105sqrt(M))^2`. For q>12,
the harmonic comparison displayed above proves the block inequality with
zero joint child. Summing every original prime-label block gives the full
energy result, without replacing signed correlations by the geometric bound.

## Lean modules and boundary

`DivisorSmoothSquareMaximum.lean` proves:

- `divisorHyperbolaSmoothRemainder_le_three_fifths`.
- `divisorUnsignedDilationChannel_one_le_three_fifths_sqrt`.
- `divisorUnsignedDilationChannel_le_three_fifths_sqrt`.

`MobiusDivisorTwelveSecondPrimeRecovery.lean` proves:

- `exists_twelve_large_dilation_all_two_coordinate_blocks`.
- `exists_twelve_large_prime_all_second_energy_bounds`.
- `exists_failed_certificate_with_all_second_energy_bounds`.

Both modules are under `formal/GaloisForLFunctions/RHTower`, namespace
`RHTower`. The last theorem supplies arbitrarily large actual prime states
that fail the geometric certificate but satisfy every available second
energy bound. All proofs are analytic; no computation was run.

This proves two initial mergers in the stated infinite family. It does not
prove the unrestricted all-cutoff two-prime comparison or a complete adaptive
order. Later changed fields still require their own full signed overlap
control; the old geometric certificate cannot be treated as necessary for
those actual admissible steps. The uniform signed Abel bound and RH remain open.
