# Prime dilation square energy is the conductor adjunction

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Q1/O1](../1-in-progress/three-frontier-questions-full-solutions.md).

For `Q≥1` and `u_m=c_m/sqrt(phi(m))`, let `D_k` be its exact conductor dilation matrix,
`E_k=D_k−I`, `F(n)=sum_(m≤Q)a_m u_m(n)`, `M=sum a_m²`,
`L=sum_(m≤Q)[log m+tau(m)]a_m²`, `tau(m)=tameDifferent(m)`, and `H=1+log Q`.

The exact square energy and its logarithmic moment are

`sum'_k Lambda(k)||E_k a||²/k = L`,

`sum'_k Lambda(k)log(k)||E_k a||²/k ≤ H L`.

Both series converge. The moment bound also holds at every finite prime cutoff.
For the literal prime residual, one absolute `C>0` satisfies, for all `Q,N≥2`,

`sum_(n≤N)[sum_(m≤Q)a_m ramanujanPrimeResidual(m,N,n)]²/log N`
`≤C H³ M/log N`.

## Exact energy

For `R≥1` and a divisor packet `F=sum_(m|R)f_m c_m`, put
`A=sum phi(m)f_m²`, `L=sum phi(m)[log m+tau(m)]f_m²`,
and `E=divisorJetEnergy R f`. Reciprocal gcd inversion gives
`mean U(F²)=log R·A−E` for the completed prime generator `U`.
The packet–jet identity gives `2 mean(F·UF)=log R·A−E−L`.
Subtracting leaves `mean(U(F²)−2F·UF)=L`, exactly the jump-square series.
Complete-period Plancherel converts this to normalized conductor coordinates.
The zero row is valid because its dilation jump and completed correction vanish.

## Logarithmic moment

For a prime `p`, put `V=floor(log_p Q)`. Every dilation matrix is constant
for exponents `j≥V`; primes `p>Q` act trivially. For `p≤Q`, earlier exponents
cost at most `V log p≤log Q`. The saturated tail has mean excess logarithm
at most `log p/(p−1)≤1`. This also holds for finite tails by

`(1−r)sum_(i<B)i r^i = r sum_(i<B)r^i−B r^B`, `r=1/p`.

Distinct positive prime powers are injectively indexed by prime and exponent.
Their unweighted square energy is bounded by the exact series, giving `H L`.
Nonnegative finite-sum bounds then give convergence and the full moment bound.

The prime-chain entry `D_(m,m p^a)(p^j)` equals
`phi(m p^a)/(sqrt(phi(m))sqrt(phi(m p^a)))` when `a≤j` and either `j=a`
or `p` does not divide `m`; otherwise it is zero. The local logarithmic
Mangoldt mass is `p(log p)²/(p−1)²`.

## Literal residual

Only primes through `Q` change the packet; their reciprocal Mangoldt mass is
at most `sum_(p≤Q)log p/(p−1)≤14H`. Weighted Cauchy–Schwarz therefore bounds
each omitted upward row's square by `14H` times its prime-weighted jump squares.
After swapping finite sums, omitted rows satisfy `N/n<k`. The
[quotient-tail bound](conductor-packet-quotient-tails-cost-only-logarithms.md)
gives harmonic packet mass at most `[18H+log k]||E_k a||²`.
The exact energy and moment give `19H L≤38H² M`, hence the finite upward tail
has squared harmonic norm at most `532H³ M`. Completed prime-row convergence
removes the cutoff. Combining this with the
[scalar bound](scalar-prime-residuals-have-logarithmic-packet-cost.md)
`C_s H M/log N` gives `C=2C_s+1064`.

The complete Weil shell, Gamma, and pole comparison remains separate.

## Lean

All modules lie in `SuccessorShellArithmetic.Conductor`:

- `PrimeConductorDilationEnergy`: `hasSum_primeDilationPacket_sq`,
  `hasSum_primeConductorDilationJump_sq`, and `hasSum_normalizedRamanujanPacket_up`.
- `PrimeConductorDilationMoments`: `primeConductorDilationMean_prime_chain`,
  `hasSum_localMangoldt_logMoment`, `sum_primeConductorDilationJump_logMoment_le`,
  `summable_primeConductorDilationJump_logMoment`, and
  `tsum_primeConductorDilationJump_logMoment_le`.
- `PrimeConductorResidualNorm`: `exists_primeResidual_packet_sq_le`.

All seventeen capstones have dependency closures containing only
`propext`, `Classical.choice`, and `Quot.sound`. Direct production audits passed.
Umbrella imports present.
