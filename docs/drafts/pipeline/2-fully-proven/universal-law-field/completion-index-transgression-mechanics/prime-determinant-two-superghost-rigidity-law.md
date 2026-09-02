# Prime-determinant two-superghost rigidity

- **ID:** `ULF-PD2SG-1`
- **Stage:** 2-fully-proven
- **Type:** unconditional arithmetic reconstruction/rigidity law
- **Status:** dependency-closed paper proof; Lean-certified in
  `GaloisForLFunctions.HTGeometry.PrimeDeterminantTwoSuperghostRigidity`

## Statement

Let `p` be prime and let `X,Y` be positive real numbers satisfying

`XY=p^2`, `1<Y<=X<p^2`.

If both odd power sums

`S_1=X-Y`, `S_2=X^2-Y^2`

are integers, then `X=Y=p`.

Consequently, for `0<=b<1`, put

`X=p^(1+b)`, `Y=p^(1-b)`.

Integrality of only

`p^(1+b)-p^(1-b)` and `p^(2+2b)-p^(2-2b)`

forces `b=0`. No all-scale hypothesis, cofinal limit, dense set of primes, or common lattice is
needed.

## Proof

Write `S_1=m` and `S_2=n` with `m,n in Z`.

If `m=0`, then `X=Y`; positivity and `XY=p^2` give `X=Y=p`.

Assume `m!=0`. Since

`S_2=(X-Y)(X+Y)`,

we have `X+Y=n/m in Q`. Moreover

`(X+Y)^2=(X-Y)^2+4XY=m^2+4p^2 in Z`.

A rational number whose square is an integer is an integer, so write `X+Y=k in Z`. Since
`k^2-m^2=4p^2`, `k` and `m` have the same parity. Hence

`X=(k+m)/2`, `Y=(k-m)/2`

are positive integers. Their product is `p^2`. Primality leaves only the factor pairs
`(1,p^2)`, `(p,p)`, `(p^2,1)`. The strict bounds `1<Y` and `X<p^2` exclude the outer pairs, so
`X=Y=p`, contradicting `m!=0`. Thus only the first case occurs.

For the conformal corollary, `XY=p^2`, and `0<=b<1` gives `1<Y<=X<p^2`. The preceding result
gives `p^(1+b)=p^(1-b)`. Injectivity of real exponentiation at base `p>1` gives `b=0`.

## Sharp boundaries

1. **Primality is load-bearing.** At composite base `6`, `X=9`, `Y=4` satisfy `XY=36`, while
   `X-Y=5` and `X^2-Y^2=65` are integral with `X!=Y`.
2. **Odd parity is load-bearing.** Put
   `X=(7+sqrt(13))/2`, `Y=(7-sqrt(13))/2`. Then `XY=9`, `1<Y<3<X<9`, and the even power sums
   `T_r=X^r+Y^r` are integers for every `r>=0`, because `T_0=2`, `T_1=7`, and
   `T_(r+2)=7T_(r+1)-9T_r`. Thus an actual nonneutral base-three reciprocal pair has integral
   traces at every prime-power depth. The odd supertrace, not the trace, removes this quadratic
   survivor.
3. One ghost is insufficient: integrality of `X-Y` alone does not make `X+Y` rational. The second
   ghost performs reconstruction.

## Corpus consequence

The mixed `(+,-)` rank-two form is not an obstruction to polarize away. It is the arithmetic
orientation needed for reconstruction. The final source burden is now strictly smaller than the
all-scale/common-lattice programmes: construct, before divisor specialization, one integral
parity-graded prime object whose first two Adams/Frobenius supertraces analytically realize the
reciprocal functional-equation weights. Big-Witt Frobenius already transports ghost two to ghost
one; the missing theorem is source/Gamma supertrace naturality, not an infinite family of integral
indices.

## Dependency audit

- Fundamental theorem of arithmetic for divisors of `p^2`.
- Elementary parity and rational-square lemmas.
- Real-power product and injectivity at base `p>1`.
- No RH, Xi zero, numerical computation, external axiom, or unproved analytic input.
