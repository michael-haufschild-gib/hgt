# EDQ completed coprime kernel column: Euler main and decaying error

Stage: dependency-closed paper proof; Lean formalization in progress.
The target remains the complete EDQ signed growth bound and ultimately RH.

For positive m,b, retain the actual kernel K(a,b)=sum_(j>=1)P_b(a*j)/(a*j)^2
and define the completed coprime numerator column

```
C(m,b)=sum_(a>=1, gcd(m,a)=1)mu(a)*K(a,b),
E_alpha(m)=prod_(p|m)(1-p^(-alpha))^(-1).
```

The sum is absolutely convergent: |P_b|<=b/8 bounds its full double series
by a constant times the product of two reciprocal-square sums. Grouping k=a*j
and applying the corpus's complete coprime divisor inversion gives exactly

```
C(m,b)=sum_(k>=1, every prime dividing k divides m) P_b(k)/k^2.
```

This identity retains both the actual Möbius coefficients and every time term.
It is the completed column; restricting a above or below a cutoff changes it.

## Uniform main term

For 0<alpha<1,

```
0 <= C(m,b)+E_1(m)/2 <= E_alpha(m)*b^(alpha-1)/2.
```

Indeed set D_b(k)=P_b(k)+k/2. For b,k>0 the exact residue formula gives
`0<=D_b(k)<=min(k/2,k^2/(2b))`: when k<=b, the second upper bound is an
equality; when k>=b, P_b<=0 supplies it. For the lower bound, k mod b<=k
and P_b(k)>=-(k mod b)/2. Consequently

```
0 <= D_b(k)/k^2 <= min(1/(2k),1/(2b))
                 <= b^(alpha-1)*k^(-alpha)/2.
```

Sum over the exact prime support. Its reciprocal mass is E_1(m), and its
alpha mass is E_alpha(m), by `DeletionCoprimeColumn.hasSum_supportedRpow`.
At squarefree m, the corpus also identifies E_1(m)=m/phi(m).

`exists_supportedEulerMass_le` supplies, for every delta>0, a constant
C_(alpha,delta) with E_alpha(m)<=C_(alpha,delta)*m^delta uniformly in m.
Thus the completed column has a positive error of size
`O_(alpha,delta)(m^delta*b^(alpha-1))` after the explicit Euler main.
No numerical calculation or Möbius cancellation hypothesis enters the proof.

## Effect on the unresolved rectangle

The reduced coordinates use m=r*b with r*b<=N. Multiplying the error by
the literal common-factor weight at most 1/r and summing all admitted r,b
gives an arbitrarily small power of N: bound m^delta by N^delta and sum
`b^(alpha-1)/r`, then take alpha,delta small and absorb the harmonic factor.
This aggregate deduction is a paper estimate, separate from the column theorem.

The numerator tail needed by EDQ is `C(r*b,b)` minus the finite numerator
head a<=floor(N/r). That subtraction still has its actual Möbius signs.
The explicit completed Euler main is not an estimate of that finite head.
In particular, the result does not prove the large-reduced-denominator tail
small, the complete flux ceiling, or RH.

As a consistency check on paper, summing the Euler mains over coprime r,b
with r*b<=N gives -M(N)/2: at each squarefree prime the two allocations have
coefficients 1/(p-1) and -p/(p-1), whose sum is -1. Completing all columns
already gives -(M(N)-H(N))/2, so the complete signed sum of their errors is
exactly H(N)/2. This cancellation does not control the retained finite head.
