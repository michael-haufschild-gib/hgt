# Prime dilation square energy is the conductor adjunction

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [Q1/O1](three-frontier-questions-full-solutions.md);
  [exact dilation](../3-formalized/centered-prime-heads-have-logarithmic-packet-norms.md).

On conductors `1≤m,l≤Q`, let
`D_k(m,l)=mean(u_m(n)u_l(kn))` and `E_k=D_k−I`.
Conjecture the exact packet identity

`sum'_k Lambda(k)||E_k a||²/k = sum_(l≤Q)[log l+tau(l)]a_l²`.

Also conjecture its logarithmic moment bound

`sum'_k Lambda(k)log(k)||E_k a||²/k`
`≤(1+log Q)sum_(l≤Q)[log l+tau(l)]a_l²`.

## Proposed proof

For a fixed prime `p`, dilation preserves the prime-free conductor factor.
On one chain `r p^v`, the zero-exponent column has zero jump. For `v≥1`,
the diagonal square energy is `v log p+log p/(p−1)`.
For `1≤v<w`, the simultaneous collapse tail `j≥w` contributes
`log p·p^(-(w−v)/2)`, exactly canceled by the mixed transition at `j=w−v`.
Different prime-free factors are orthogonal. Summing the diagonal terms
over primes gives `log l+tau(l)`.

Equivalently, expand the squared packet as a finite gcd profile. Its
harmonic finite part identifies the averaged dilation generator on `F²`
with torsion `T`. The centered period head gives `2 mean(F·UF)=T−L`,
where `L=sum[log l+tau(l)]a_l²`. Their difference is the jump-square
energy `mean(U(F²)−2F·UF)=L`.

For a divisor packet `F=sum_(m|M)f_m c_m`, the same calculation is finite
after the existing completed prime-row series is summed. Put
`A=sum_(m|M)phi(m)f_m²`, `L=sum_(m|M)phi(m)[log m+tau(m)]f_m²`,
and `E=divisorJetEnergy M f`. Reciprocal gcd inversion gives
`mean U(F²)=log M·A−E`. The packet–jet identity gives
`2 mean(F·UF)=log M·A−E−L`. Thus the exact series has sum `L`.
The row at zero is valid directly because both its dilation jump and
its completed adjunction correction vanish.

For the moment bound, put `V=floor(log_p Q)`. The entire matrix `E_(p^j)`
is constant for `j≥V`. Earlier exponents have `j log p≤log Q`; the
geometric tail has mean logarithm `V log p+log p/(p−1)≤log Q+1`.
Thus the logarithmic bound holds in the order on positive quadratic forms.
The same bound holds for every finite prime cutoff. A finite proof uses
`(1-r)sum_(i<L)i r^i=r sum_(i<L)r^i−L r^L`, `r=1/p`.
After the valuation saturates, this identity bounds each truncated tail's
mean excess logarithm by `log p/(p−1)≤1`. Earlier exponents cost at most
`log Q`. Distinct positive prime powers are injectively indexed by their
prime and exponent, so the exact total square energy bounds the resulting
finite sum.

## Norm transfer

The active prime mass obeys
`sum_(p≤Q)log p/(p−1)≤2sum_(k≤Q)Lambda(k)/k≤14(1+log Q)`.
Weighted Cauchy–Schwarz and the
[packet quotient-tail bound](../3-formalized/conductor-packet-quotient-tails-cost-only-logarithms.md)
would therefore bound the omitted upward correction in squared norm by
`C(1+log Q)³/log N` times coefficient mass.
For a finite prime cutoff, interchange the row and prime sums. The omitted
rows satisfy exactly `N/n<k`, so the packet tail costs
`1+log(2k)+16(1+log Q)`. The energy identity and logarithmic moment then
pay both terms. Completed prime-row convergence removes the cutoff.

Together with the formalized
[uniform scalar estimate](../3-formalized/scalar-prime-residuals-have-logarithmic-packet-cost.md),
this gives the conjectured full arithmetic bound, for every `Q,N≥2`,

`sum_(n≤N)[sum_(m≤Q)a_m ramanujanPrimeResidual(m,N,n)]²/log N`
`≤C(1+log Q)³ sum a_m²/log N`.

The divisor-packet and normalized square identities are formalized as
`hasSum_primeDilationPacket_sq` and `hasSum_primeConductorDilationJump_sq`.
`Conductor.PrimeConductorDilationEnergy` passed its direct production audit;
all six capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`.
Umbrella import present.
The finite and full logarithmic moment bounds, including summability,
are formalized in `PrimeConductorDilationMoments`. Its direct production
audit passed; all ten capstones have only the standard three axioms.
Norm transfer awaits Lean verification.
The complete Weil shell and pole residuals remain separate.
